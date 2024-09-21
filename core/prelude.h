#include <gc/gc.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static inline char *__toad_gcalloc(size_t bytes) {
  if (bytes) {
    return (char *)GC_malloc(bytes);
  }
  return NULL;
}

static inline void print_usize(uintptr_t n) { printf("%lu", n); }
