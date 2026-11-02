/* Scheduling/fault hooks for otherwise hard-to-hit boundaries. No return value
 * is fabricated. after-fork waits for a real API interrupt; cancel-write-failure
 * closes the real peer's reader; after-reap injects an ordinary OS SIGINT. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <fcntl.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static pid_t owner;
static pid_t split_child;
static int fired;
static int protocol_writes;

pid_t setsid(void) {
  static pid_t (*real_setsid)(void);
  if (!real_setsid) real_setsid = dlsym(RTLD_NEXT, "setsid");
  pid_t result = real_setsid();
  if (result > 0) owner = getpid();
  return result;
}

static int mode(const char *name) {
  const char *value = getenv("ROCQ_REVIEW_SCHEDULE");
  return value && !strcmp(value, name) && owner == getpid() && !fired;
}

pid_t fork(void) {
  static pid_t (*real_fork)(void);
  if (!real_fork) real_fork = dlsym(RTLD_NEXT, "fork");
  int both_sides = mode("both-fork-sides");
  pid_t child = real_fork();
  if (both_sides && child >= 0) {
    const char *marker = getenv("ROCQ_REVIEW_MARKER");
    char release[4096];
    snprintf(release, sizeof release, "%s.release", marker);
    if (child > 0) {
      int fd = open(marker, O_WRONLY | O_CREAT, 0600);
      if (fd >= 0) close(fd);
    }
    while (access(release, F_OK) != 0) usleep(1000);
    /* Let the helper's inherited handler publish its response first. */
    if (child > 0) for (int i = 0; i < 100; ++i) usleep(1000);
  }
  if (child > 0 && owner == getpid()) {
    split_child = child;
    if (mode("after-fork")) {
      fired = 1;
      const char *marker = getenv("ROCQ_REVIEW_MARKER");
      if (marker) {
        int fd = open(marker, O_WRONLY | O_CREAT, 0600);
        if (fd >= 0) close(fd);
        /* The API caller removes the marker after publishing cancellation. */
        while (access(marker, F_OK) == 0) usleep(1000);
      }
    }
  }
  return child;
}

ssize_t write(int fd, const void *buffer, size_t length) {
  static ssize_t (*real_write)(int, const void *, size_t);
  if (!real_write) real_write = dlsym(RTLD_NEXT, "write");
  if (fd == STDOUT_FILENO && owner == getpid()) {
    ++protocol_writes;
    if (protocol_writes == 2 && mode("cancel-write-failure")) {
      /* The real peer loses its command reader just before publishing Started. */
      fired = 1;
      close(STDIN_FILENO);
      ssize_t result = real_write(fd, buffer, length);
      raise(SIGSTOP);
      return result;
    }
  }
  return real_write(fd, buffer, length);
}

int open64(const char *path, int flags, ...) {
  static int (*real_open64)(const char *, int, ...);
  if (!real_open64) real_open64 = dlsym(RTLD_NEXT, "open64");
  mode_t permissions = 0;
  if ((flags & O_CREAT) || ((flags & O_TMPFILE) == O_TMPFILE)) {
    va_list args;
    va_start(args, flags);
    permissions = va_arg(args, int);
    va_end(args);
  }
  int fd = real_open64(path, flags, permissions);
  const char *schedule = getenv("ROCQ_REVIEW_SCHEDULE");
  const char *api = getenv("ROCQ_REVIEW_API_PID");
  size_t length = strlen(path);
  if (fd >= 0 && schedule && !strcmp(schedule, "guard-atomic") && api &&
      getpid() == atoi(api) && !fired && (flags & O_ACCMODE) == O_RDWR &&
      length >= 3 && !strcmp(path + length - 3, "/in")) {
    fired = 1;
    const char *marker = getenv("ROCQ_REVIEW_MARKER");
    int ready = real_open64(marker, O_WRONLY | O_CREAT, 0600);
    if (ready >= 0) close(ready);
    /* Pause after the actual open, before any later fcntl can repair its flags. */
    while (access(marker, F_OK) == 0) usleep(1000);
  }
  return fd;
}

pid_t waitpid(pid_t pid, int *status, int options) {
  static pid_t (*real_waitpid)(pid_t, int *, int);
  if (!real_waitpid) real_waitpid = dlsym(RTLD_NEXT, "waitpid");
  pid_t result = real_waitpid(pid, status, options);
  if (result > 0 && result == split_child && mode("after-reap")) {
    fired = 1;
    kill(getpid(), SIGINT);
  }
  return result;
}
