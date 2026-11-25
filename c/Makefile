CC ?= cc
CFLAGS ?= -O3
THREAD_FLAGS = -pthread
IFMA_FLAGS ?= -march=native -mavx512ifma -mavx512dq

BELLARD_SOURCES = bellard_bench.c bellard_direct.c bellard_grouped.c
SCALAR_BINARIES = euler_grouped smith_fast bellard_baseline bellard_bench

.PHONY: all ifma clean

all: $(SCALAR_BINARIES)

ifma: euler_grouped_ifma

euler_grouped: euler_grouped.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(THREAD_FLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS) -lm

smith_fast: smith_fast.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(THREAD_FLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS) -lm

bellard_baseline: $(BELLARD_SOURCES) bellard.h
	$(CC) $(CPPFLAGS) $(CFLAGS) $(THREAD_FLAGS) $(LDFLAGS) -o $@ $(BELLARD_SOURCES) $(LDLIBS) -lm

bellard_bench: $(BELLARD_SOURCES) bellard_grouped_seg.c bellard.h
	$(CC) $(CPPFLAGS) -DBELLARD_SEGMENTED $(CFLAGS) $(THREAD_FLAGS) $(LDFLAGS) -o $@ $(BELLARD_SOURCES) bellard_grouped_seg.c $(LDLIBS) -lm

euler_grouped_ifma: euler_grouped_ifma.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(IFMA_FLAGS) $(THREAD_FLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS) -lm

clean:
	$(RM) $(SCALAR_BINARIES) euler_grouped_ifma
