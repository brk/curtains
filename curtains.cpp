/*
Overview:

  This tool is meant to be a best-effort (rather than fully secure)
  path watchdog -- restricting the files a given command can access,
  but with a simpler model/interface than a more robust solution like
  chroot/containers/etc.

  Somewhat ironically, the approaches with the more heavyweight mental
  model--containers, overlay filesystems, etc--can have significantly (?)
  faster implementation, since they can rely on direct kernel support
  and we're stuck hammering ourselves into a ptrace-shaped hole.

Warning:

  Currently only handles the openat and creat system calls.
  Should also handle (at least) open, opendir, stat, access, chdir,
  mkdir, rmdir, *link, truncate, chmod, chown, mknod, statfs, mount,
  pivot_root, chroot, *xattr, mq_open, name_to_handle_at, ...
  (and variants thereof).

  Paths are not canonicalized; we look at whatever the program sends
  our way. Given our default-deny approach, this is a matter of
  (in-)convenience rather than security.

  I haven't put any effort into making this robust for process trees.

Usage:

      curtains allowed.txt command args...

  Runs the given command, disallowing access to any path not listed
  in the file provided in the first argument.

  Most programs dynamically link against system libraries, which will
  need to be explicitly whitelisted -- there are no hardcoded defaults.
  You can use  strace  or a wrapper like  tracefile  to help generate
  a list of accessed files to use as a starting point for allowed.txt.

Related work:

  There's a rich literature on sandboxing, most of which I'm not aware
  of. But based on my searching so far, it was going to be faster to
  flesh out this code rather than find the needle in the haystack.

  If you'd like something stronger, DetFlow provides a more general (and
  lower-overhead) runtime enforcement based on a combination of LD_PRELOAD
  interpositioning and ptrace. There's also a binary instrumentation
  system called reverie (which could be used to build a more specialized
  tool like this).

  Another related tool is MBOX by Kim & Zeldovich, but its model seems to
  be to allow all reads and then capture/redirect writes, rather than
  disallowing reads selectively.

  SandFS needs a custom kernel module.

  Libdetox/Lockdown appear to be strictly more general than this tool but
  unfortunately they're also 32-bit only.


Credits:

  Heavily based on
      www.win.tue.nl/~aeb/linux/lk/ptrace.c
  and
      nullprogram.com/blog/2018/06/23/


  You might also enjoy reading
      blog.nelhage.com/2010/08/write-yourself-an-strace-in-70-lines-of-code/


Notes:

  seccomp-BPF uses classic BPF and therefore can't inspect userspace data like paths.
  AFAICT there's a lot of friction around the idea of combining seccomp with eBPF.

  TODO it would be quite useful to extend this to masking/filtering
      network-related syscalls as well. It would be really cool to
      have an allow/block model based on URLs, but obviously that
      requires rather more heavyweight introspection and state tracking
      than is currently called for.

      Another interesting idea would be to redirect network traffic to
      the local filesystem...
*/

#include <cerrno>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <unistd.h>

#include <fstream>
#include <iostream>
#include <set>
#include <string>

#define ptrace_checked(request, pid, addr, data)                               \
  do {                                                                         \
    int i = ptrace(request, pid, addr, data);                                  \
    if (i) {                                                                   \
      perror("ptrace");                                                        \
      exit(1);                                                                 \
    }                                                                          \
  } while (0)

/*
 * Since -1 may be valid data, we have to check errno.
 */
long ptrace_PEEKUSER(pid_t pid, void *addr, void *data) {
  long i;

  errno = 0;
  i = ptrace(PTRACE_PEEKUSER, pid, addr, data);
  if (i == -1 && errno) {
    perror("ptrace");
    exit(1);
  }
  return i;
}

long ptrace_PEEKDATA(pid_t pid, void *addr, void *data) {
  long i;

  errno = 0;
  i = ptrace(PTRACE_PEEKDATA, pid, addr, data);
  if (i == -1 && errno) {
    perror("ptrace");
    exit(1);
  }
  return i;
}

pid_t pid; /* the traced program */

int got_sig = 0;

void sigusr1(int dummy) { got_sig = 1; }

void kill_checked(pid_t pid, int sig) {
  int i = kill(pid, sig);
  if (i) {
    perror("kill");
    exit(1);
  }
}

#define SIGSYSTRAP (SIGTRAP | 0x80)

#define EXPECT_EXITED   1
#define EXPECT_SIGNALED 2
#define EXPECT_STOPPED  4

void wait_checked(pid_t p, int report, int stopsig) {
  int status;
  pid_t pw = wait(&status);

  if (pw == (pid_t)-1) {
    perror("wait");
    exit(1);
  }

  /*
   * Report only unexpected things.
   *
   * The conditions WIFEXITED, WIFSIGNALED, WIFSTOPPED
   * are mutually exclusive:
   * WIFEXITED:  (status & 0x7f) == 0, WEXITSTATUS: top 8 bits
   * and now WCOREDUMP:  (status & 0x80) != 0
   * WIFSTOPPED: (status & 0xff) == 0x7f, WSTOPSIG: top 8 bits
   * WIFSIGNALED: all other cases, (status & 0x7f) is signal.
   */
  if (WIFEXITED(status) && !(report & EXPECT_EXITED))
    fprintf(stderr, "child exited%s with status %d\n",
            WCOREDUMP(status) ? " and dumped core" : "", WEXITSTATUS(status));
  if (WIFSTOPPED(status) && !(report & EXPECT_STOPPED))
    fprintf(stderr, "child stopped by signal %d\n", WSTOPSIG(status));
  if (WIFSIGNALED(status) && !(report & EXPECT_SIGNALED))
    fprintf(stderr, "child signalled by signal %d\n", WTERMSIG(status));

  if (WIFSTOPPED(status) && WSTOPSIG(status) != stopsig) {
    /* a different signal - send it on and wait */
    // fprintf(stderr, "Waited for signal %d, got %d\n", stopsig,
    // WSTOPSIG(status));
    if ((WSTOPSIG(status) & 0x7f) == (stopsig & 0x7f))
      return;
    ptrace_checked(PTRACE_SYSCALL, p, 0, (void *)(uintptr_t)(WSTOPSIG(status)));
    return wait_checked(p, report, stopsig);
  }

  if ((report & EXPECT_STOPPED) && !WIFSTOPPED(status)) {
    fprintf(stderr, "Not stopped?\n");
    exit(1);
  }
}

// Read path from tracee's memory, one byte at a time.
// TODO use process_vm_readv
void copy_string_from(char* dest, int maxlen, uintptr_t addr, pid_t p) {
  dest[maxlen - 1] = 0;
  for (int i = 0; i < maxlen - 1; ++i) {
    void* from = (void*)(addr + i);
    long val = ptrace_PEEKDATA(p, from, 0);
    char c = (unsigned long)val;
    dest[i] = c;
    if (c == 0)
      break;
  }
}

std::set<std::string> allowed;

bool is_path_allowed(const char* path) { return allowed.count(path) == 1; }

int main(int argc, char** argv, char** envp) {
  pid_t p0, p;

  if (argc <= 2) {
    fprintf(stderr, "Usage: %s allowed-paths.txt command args\n", argv[0]);
    exit(1);
  }

  {
    std::ifstream infile(argv[1]);
    if (!infile) {
      fprintf(stderr, "Error: unable to read allowed paths from %s\n", argv[1]);
      return 1;
    }

    std::string s;
    while (std::getline(infile, s)) {
      // fprintf(stderr, "allowing path %s\n", s.c_str());
      allowed.insert(s);
    }
  }

  {
    void (*oldsig)(int);

    /*
     * fork off a child that executes the specified command
     */

    /*
     * The parent process will send a signal to the child
     * and do a wait() to wait until the child stops.
     * If the signal arrives before the child has said
     * PTRACE_TRACEME, then maybe the child is killed, or
     * maybe the signal is ignored and we wait forever, or
     * maybe the child is stopped but we are not tracing.
     * So, let us arrange for the child to signal the parent
     * when it has done the PTRACE_TRACEME.
     */

    /* prepare both parent and child for signal */
    oldsig = signal(SIGUSR1, sigusr1);
    if (oldsig == SIG_ERR) {
      perror("signal");
      exit(1);
    }

    /* child needs parent pid */
    p0 = getpid();

    p = fork();
    if (p == (pid_t)-1) {
      perror("fork");
      _exit(1);
    }

    if (p == 0) { /* child */
      ptrace_checked(PTRACE_TRACEME, 0, 0, 0);

      /* tell parent that we are ready */
      kill_checked(p0, SIGUSR1);

      /* wait for parent to start tracing us */
      while (!got_sig)
        ;

      /*
       * the first thing the parent will see is
       *  119: sigreturn - the return from the signal handler
       */

      /* exec the given process */
      argv[argc] = 0;
      execve(argv[2], argv + 2, envp);
      exit(1);
    }

    /* wait for child to get ready */
    while (!got_sig)
      ;

    /*
     * tell child that we got the signal
     * this kill() will stop the child
     */
    kill_checked(p, SIGUSR1);
    wait_checked(p, EXPECT_STOPPED, SIGUSR1);

    ptrace_checked(PTRACE_SYSCALL, p, 0, (void *) SIGUSR1);
  }

  /*
   * trace the victim's syscalls
   */
  while (1) {
    struct user_regs_struct u_in = { 0 };
    int handled = 0;
    int blocked = 0;

    wait_checked(p, EXPECT_STOPPED, SIGSYSTRAP);

    ptrace_checked(PTRACE_GETREGS, p, 0, &u_in);
    int syscall = u_in.orig_rax;

    if (syscall == __NR_openat) {
      char path[512] = { 0 };
      copy_string_from(&path[0], 512, u_in.rsi, p);
      if (!is_path_allowed(path)) {
        // fprintf(stderr, "openat BLOCKING %s\n", path); fflush(stderr);
        blocked = EACCES;
      }
    } else if (syscall == __NR_creat) {
      char path[512] = {0};
      copy_string_from(&path[0], 512, u_in.rdi, p);
      if (!is_path_allowed(path)) {
        // fprintf(stderr, "creat BLOCKING %s\n", path); fflush(stderr);
        blocked = EACCES;
      }
    }

    if (blocked) {
      // We can't prevent the system call from happening, but we can
      // change *what* system call path the victim is about to execute;
      // specifically, we can ask for a non-existent system call to
      // get the same result as not executing any call.
      u_in.orig_rax = -1;
      ptrace(PTRACE_SETREGS, p, 0, &u_in);
    }

    if (syscall == __NR_execve) {
      struct user *usr = 0;
      uintptr_t rax;

      ptrace_checked(PTRACE_SYSCALL, p, 0, 0);
      wait_checked(p, EXPECT_STOPPED, SIGSYSTRAP);

      /*
       * For a successful execve we get one more trap
       * But was this call successful?
       */
      rax = ptrace_PEEKUSER(p, &(usr->regs.rax), 0);
      if (rax == 0) {
        // fprintf(stderr, "SYSCALL execve, once more\n");

        /* the syscall return - no "good" bit */
        ptrace_checked(PTRACE_SYSCALL, p, 0, 0);
        wait_checked(p, EXPECT_STOPPED, SIGTRAP);
      }
      handled = 1;
    }

    if (!handled) {
      /* wait for syscall return */
      ptrace_checked(PTRACE_SYSCALL, p, 0, 0);
      if (syscall == __NR_exit || syscall == __NR_exit_group) {
        wait_checked(p, EXPECT_EXITED, 0);
        exit(0);
      }
      wait_checked(p, EXPECT_STOPPED, SIGSYSTRAP);

      if (blocked) {
        u_in.rax = -blocked;
        ptrace_checked(PTRACE_SETREGS, p, 0, &u_in);
      }
    }

    // Resume victim.
    ptrace_checked(PTRACE_SYSCALL, p, 0, 0);
  }
  return 0;
}
