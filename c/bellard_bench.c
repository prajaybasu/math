#define _DARWIN_C_SOURCE

#define _POSIX_C_SOURCE 200809L
#include "bellard.h"

#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

const Family families[7] = {
    {4, 1, 5, true}, {4, 3, 0, true}, {10, 1, 8, false},
    {10, 3, 6, true}, {10, 5, 2, true}, {10, 7, 2, true}, {10, 9, 0, false}
};

double wall_time(void)
{
    struct timespec now;
#ifdef __APPLE__
    clock_gettime(CLOCK_UPTIME_RAW, &now);
#else
    clock_gettime(CLOCK_MONOTONIC, &now);
#endif
    return (double)now.tv_sec + (double)now.tv_nsec * 1e-9;
}

typedef struct {
    Range fn;
    const void *data;
    uint32_t length, chunk;
    atomic_uint next;
} Job;

typedef struct {
    Job *job;
    uint32_t *scratch;
    Partial partial;
} Worker;

static void *work(void *arg)
{
    Worker *w = arg;
    Job *job = w->job;
    for (;;) {
        uint32_t lo = atomic_fetch_add_explicit(&job->next, job->chunk, memory_order_relaxed);
        if (lo >= job->length)
            return NULL;
        uint32_t hi = lo + job->chunk;
        if (hi > job->length)
            hi = job->length;
        job->fn(job->data, lo, hi, &w->partial, w->scratch);
    }
}

static void merge(Partial *out, const Partial *p)
{
    out->sum += p->sum;
#define MERGE(field) out->counts.field += p->counts.field
    MERGE(rounded);
    MERGE(query_powers);
    MERGE(coefficient_powers);
    MERGE(query_squares);
    MERGE(coefficient_squares);
    MERGE(mulmods);
    MERGE(inversions);
    MERGE(inverse_divisions);
    MERGE(coefficient_slots);
    MERGE(block_sums);
    MERGE(dyadic_divisions);
    MERGE(primes);
    MERGE(prime_powers);
    MERGE(sieve_writes);
    MERGE(inversion_batches);
    MERGE(sieve_worker_seconds);
    MERGE(phase_groups);
    MERGE(coefficient_seconds);
    MERGE(evaluation_seconds);
    MERGE(timer_seconds);
#undef MERGE
}

bool run_ranges(Range fn, const void *data, uint32_t length, uint32_t chunk,
                unsigned threads, size_t scratch, Partial *out)
{
    uint32_t *storage = scratch ? malloc(threads * scratch * sizeof(*storage)) : NULL;
    if (scratch && !storage)
        return false;
    if (threads == 1) {
        fn(data, 0, length, out, storage);
        free(storage);
        return true;
    }

    uint32_t target = (length + 4 * threads - 1) / (4 * threads);
    if (target < 64)
        target = 64;
    if (chunk > target)
        chunk = target;
    Job job = {.fn = fn, .data = data, .length = length, .chunk = chunk, .next = 0};
    Worker workers[10] = {0};
    pthread_t handles[9];
    for (unsigned i = 0; i < threads; ++i) {
        workers[i].job = &job;
        workers[i].scratch = scratch ? storage + i * scratch : NULL;
    }
    unsigned started = 0;
    while (started + 1 < threads) {
        if (pthread_create(&handles[started], NULL, work, &workers[started]) != 0) {
            for (unsigned i = 0; i < started; ++i)
                pthread_join(handles[i], NULL);
            free(storage);
            return false;
        }
        ++started;
    }
    work(&workers[threads - 1]);
    for (unsigned i = 0; i < started; ++i)
        pthread_join(handles[i], NULL);
    for (unsigned i = 0; i < threads; ++i)
        merge(out, &workers[i].partial);
    free(storage);
    return true;
}

static void tail(int64_t exponent, uint64_t first, Partial *out)
{
    for (uint64_t k = first; k < first + TAIL_ROWS; ++k) {
        for (unsigned i = 0; i < 7; ++i) {
            Family f = families[i];
            uint64_t d = f.stride * k + f.offset;
            int64_t e = PRECISION + exponent - 10 * (int64_t)k + f.shift;
            bool negative = f.negative ^ (k & 1);
            u128 quotient = 0;
            bool remainder = true;
            if (e >= 0) {
                u128 numerator = (u128)1 << e;
                quotient = numerator / d;
                remainder = quotient * d != numerator;
            }
            out->sum += negative ? -(quotient + remainder) : quotient;
            ++out->counts.rounded;
        }
    }
}

static bool parse(const char *s, uint64_t minimum, uint64_t maximum, uint64_t *value)
{
    char *end;
    errno = 0;
    unsigned long long n = strtoull(s, &end, 10);
    if (errno || end == s || *end || n < minimum || n > maximum)
        return false;
    *value = n;
    return true;
}

int main(int argc, char **argv)
{
    uint64_t n, width = 32, threads = 1, max_n = 1000000000;
    bool segmented = false, valid_block = true;
#ifdef BELLARD_SEGMENTED
    uint64_t block_slots = DEFAULT_COFACTOR_BLOCK;
    segmented = argc > 1 && !strcmp(argv[1], "segmented");
    if (segmented) {
        max_n = SEGMENTED_MAX_N;
        if (argc > 5)
            valid_block = parse(argv[5], 1, MAX_COFACTOR_BLOCK, &block_slots);
    }
#endif
    bool original = argc > 1 && (!strcmp(argv[1], "direct") || !strcmp(argv[1], "grouped"));
    if (argc < 3 || argc > (segmented ? 6 : 5) || (!original && !segmented) ||
        !valid_block || !parse(argv[2], 1, max_n, &n) ||
        (argc > 3 && !parse(argv[3], 1, 64, &width)) ||
        (argc > 4 && !parse(argv[4], 1, 10, &threads))) {
        fprintf(stderr, "usage: %s direct|grouped n[1..1000000000] [width=32] [threads=1]\n", argv[0]);
#ifdef BELLARD_SEGMENTED
        fprintf(stderr, "       %s segmented n[1..%" PRIu64 "] [width=32] [threads=1] "
                "[cofactor_block=%d, range 1..%d]\n",
                argv[0], SEGMENTED_MAX_N, DEFAULT_COFACTOR_BLOCK, MAX_COFACTOR_BLOCK);
#endif
        return 2;
    }
    Partial out = {0};
    double sieve_seconds = 0;
    double start = wall_time();
    int64_t exponent = (int64_t)n - 7;
    uint64_t first_tail = 0;
    if (exponent >= 0) {
        uint64_t last = (uint64_t)exponent / 10;
        bool ok;
#ifdef BELLARD_SEGMENTED
        if (segmented)
            ok = grouped_segmented(exponent, last, threads, block_slots, &out, &sieve_seconds);
        else
#endif
            ok = argv[1][0] == 'd'
                ? direct(exponent, last, threads, &out)
                : grouped(exponent, last, threads, &out, &sieve_seconds);
        if (!ok) {
            fprintf(stderr, "could not allocate memory or create workers\n");
            return 2;
        }
        first_tail = last + 1;
    }
    tail(exponent, first_tail, &out);
    u128 lo = (out.sum - 1) & FIXED_MASK;
    u128 hi = (out.sum + out.counts.rounded + 1) & FIXED_MASK;
    uint64_t lower_window = (uint64_t)(lo >> (PRECISION - width));
    uint64_t upper_window = (uint64_t)(hi >> (PRECISION - width));
    bool certified = lower_window == upper_window &&
        (u128)out.counts.rounded + 2 < ((u128)1 << (PRECISION - width));
    double seconds = wall_time() - start;
    struct rusage usage = {0};
    getrusage(RUSAGE_SELF, &usage);
#ifdef __APPLE__
    uint64_t rss_bytes = usage.ru_maxrss;
#else
    uint64_t rss_bytes = (uint64_t)usage.ru_maxrss * 1024;
#endif
    printf("{\"method\":\"%s\",\"n\":%" PRIu64 ",\"width\":%" PRIu64 ",\"threads\":%" PRIu64 ","
           "\"certified\":%s,\"window\":", argv[1], n, width, threads,
           certified ? "true" : "false");
    if (certified) {
        putchar('"');
        for (unsigned i = width; i > 0; --i)
            putchar('0' + ((lower_window >> (i - 1)) & 1));
        putchar('"');
    } else {
        fputs("null", stdout);
    }
    printf(",\"seconds\":%.9f,\"sieve_seconds\":%.9f,\"rss_bytes\":%" PRIu64
           ",\"rounded\":%" PRIu64 ",\"head_start_exponent\":%" PRId64
           ",\"lower96\":\"%08" PRIx32 "%016" PRIx64 "\",\"error_ulps\":%" PRIu64,
           seconds, sieve_seconds, rss_bytes, out.counts.rounded, exponent,
           (uint32_t)(lo >> 64), (uint64_t)lo, out.counts.rounded + 2);
#ifdef BELLARD_SEGMENTED
    if (segmented)
        printf(",\"cofactor_block\":%" PRIu64 ",\"sieve_worker_seconds\":%.9f",
               block_slots, out.counts.sieve_worker_seconds);
#endif
#ifdef COUNT_OPS
#define PRINT_COUNT(field) printf(",\"" #field "\":%" PRIu64, out.counts.field)
    PRINT_COUNT(query_powers);
    PRINT_COUNT(coefficient_powers);
    PRINT_COUNT(query_squares);
    PRINT_COUNT(coefficient_squares);
    PRINT_COUNT(mulmods);
    PRINT_COUNT(inversions);
    PRINT_COUNT(inverse_divisions);
    PRINT_COUNT(coefficient_slots);
    PRINT_COUNT(block_sums);
    PRINT_COUNT(dyadic_divisions);
    PRINT_COUNT(primes);
    PRINT_COUNT(prime_powers);
    PRINT_COUNT(sieve_writes);
    if (segmented)
        PRINT_COUNT(inversion_batches);
#undef PRINT_COUNT
#endif
#ifdef PROFILE_PHASES
    printf(",\"phase_groups\":%" PRIu64 ",\"coefficient_seconds\":%.9f,"
           "\"evaluation_seconds\":%.9f,\"timer_seconds\":%.9f",
           out.counts.phase_groups, out.counts.coefficient_seconds,
           out.counts.evaluation_seconds, out.counts.timer_seconds);
#endif
    puts("}");
    return certified ? 0 : 1;
}
