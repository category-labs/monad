#define _GNU_SOURCE 1
#define LINUX_THREAD_DB_USER_THREADS_AM_LIBTHREAD_DB 1

#include <gdb/linux-thread-db-user-threads.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <dlfcn.h>

#define LIBTHREAD_DB_EXTERN extern __attribute__((visibility("default")))

// These get intercepted by our functions below
#define LIBTHREAD_DB_FUNCTION(symbol) static symbol##_ftype *symbol##_orig;
LIBTHREAD_DB_FUNCTION(td_init)
LIBTHREAD_DB_FUNCTION(td_ta_map_lwp2thr)
LIBTHREAD_DB_FUNCTION(td_ta_new)
LIBTHREAD_DB_FUNCTION(td_ta_thr_iter)
LIBTHREAD_DB_FUNCTION(td_thr_get_info)

LIBTHREAD_DB_FUNCTION(td_log)
LIBTHREAD_DB_FUNCTION(td_symbol_list)
LIBTHREAD_DB_FUNCTION(td_ta_clear_event)
LIBTHREAD_DB_FUNCTION(td_ta_delete)
LIBTHREAD_DB_FUNCTION(td_ta_enable_stats)
LIBTHREAD_DB_FUNCTION(td_ta_event_addr)
LIBTHREAD_DB_FUNCTION(td_ta_event_getmsg)
LIBTHREAD_DB_FUNCTION(td_ta_get_nthreads)
LIBTHREAD_DB_FUNCTION(td_ta_get_ph)
LIBTHREAD_DB_FUNCTION(td_ta_get_stats)
LIBTHREAD_DB_FUNCTION(td_ta_map_id2thr)
LIBTHREAD_DB_FUNCTION(td_ta_reset_stats)
LIBTHREAD_DB_FUNCTION(td_ta_set_event)
LIBTHREAD_DB_FUNCTION(td_ta_setconcurrency)
LIBTHREAD_DB_FUNCTION(td_ta_tsd_iter)
LIBTHREAD_DB_FUNCTION(td_thr_clear_event)
LIBTHREAD_DB_FUNCTION(td_thr_dbresume)
LIBTHREAD_DB_FUNCTION(td_thr_dbsuspend)
LIBTHREAD_DB_FUNCTION(td_thr_event_enable)
LIBTHREAD_DB_FUNCTION(td_thr_event_getmsg)
LIBTHREAD_DB_FUNCTION(td_thr_getfpregs)
LIBTHREAD_DB_FUNCTION(td_thr_getgregs)
LIBTHREAD_DB_FUNCTION(td_thr_getxregs)
LIBTHREAD_DB_FUNCTION(td_thr_getxregsize)
LIBTHREAD_DB_FUNCTION(td_thr_set_event)
LIBTHREAD_DB_FUNCTION(td_thr_setfpregs)
LIBTHREAD_DB_FUNCTION(td_thr_setgregs)
LIBTHREAD_DB_FUNCTION(td_thr_setprio)
LIBTHREAD_DB_FUNCTION(td_thr_setsigpending)
LIBTHREAD_DB_FUNCTION(td_thr_setxregs)
LIBTHREAD_DB_FUNCTION(td_thr_sigsetmask)
LIBTHREAD_DB_FUNCTION(td_thr_tls_get_addr)
LIBTHREAD_DB_FUNCTION(td_thr_tlsbase)
LIBTHREAD_DB_FUNCTION(td_thr_tsd)
LIBTHREAD_DB_FUNCTION(td_thr_validate)
#undef LIBTHREAD_DB_FUNCTION

thread_db_userspace_threads_state_t current_thread_db_userspace_threads;

static struct ps_prochandle *my_prochandle;
static psaddr_t thread_db_userspace_threads_addr;

static void *base_so;

static void __attribute__((destructor)) base_so_cleanup()
{
#if PRINT_LOGGING
    printf("custom-libthread_db: base_so_cleanup\n");
#endif
    if (base_so != NULL) {
        dlclose(base_so);
        base_so = NULL;
    }
}

LIBTHREAD_DB_EXTERN td_err_e td_init()
{
#if PRINT_LOGGING
    printf("custom-libthread_db: td_init\n");
#endif
#ifdef __x86_64__
    static char const libthread_db_path[] =
        "/usr/lib/x86_64-linux-gnu/libthread_db.so";
#elif defined(__aarch64__)
    static char const libthread_db_path[] =
        "/usr/lib/arm-linux-gnueabihf/libthread_db.so";
#endif
    base_so = dlopen(libthread_db_path, RTLD_LAZY | RTLD_LOCAL);
    if (base_so == NULL) {
        fprintf(
            stderr,
            "FATAL: Failed to load '%s' "
            "due to '%s'.\n",
            libthread_db_path,
            dlerror());
        abort();
    }
#define LIBTHREAD_DB_FUNCTION(symbol)                                          \
    symbol##_orig = dlsym(base_so, #symbol);                                   \
    if (symbol##_orig == NULL) {                                               \
        fprintf(                                                               \
            stderr,                                                            \
            "FATAL: Failed to resolve symbol '" #symbol "' due to '%s'.\n",    \
            dlerror());                                                        \
        abort();                                                               \
    }
    LIBTHREAD_DB_FUNCTION(td_init)
    LIBTHREAD_DB_FUNCTION(td_ta_map_lwp2thr)
    LIBTHREAD_DB_FUNCTION(td_ta_new)
    LIBTHREAD_DB_FUNCTION(td_ta_thr_iter)
    LIBTHREAD_DB_FUNCTION(td_thr_get_info)

    LIBTHREAD_DB_FUNCTION(td_log)
    LIBTHREAD_DB_FUNCTION(td_symbol_list)
    LIBTHREAD_DB_FUNCTION(td_ta_clear_event)
    LIBTHREAD_DB_FUNCTION(td_ta_delete)
    LIBTHREAD_DB_FUNCTION(td_ta_enable_stats)
    LIBTHREAD_DB_FUNCTION(td_ta_event_addr)
    LIBTHREAD_DB_FUNCTION(td_ta_event_getmsg)
    LIBTHREAD_DB_FUNCTION(td_ta_get_nthreads)
    LIBTHREAD_DB_FUNCTION(td_ta_get_ph)
    LIBTHREAD_DB_FUNCTION(td_ta_get_stats)
    LIBTHREAD_DB_FUNCTION(td_ta_map_id2thr)
    LIBTHREAD_DB_FUNCTION(td_ta_reset_stats)
    LIBTHREAD_DB_FUNCTION(td_ta_set_event)
    LIBTHREAD_DB_FUNCTION(td_ta_setconcurrency)
    LIBTHREAD_DB_FUNCTION(td_ta_tsd_iter)
    LIBTHREAD_DB_FUNCTION(td_thr_clear_event)
    LIBTHREAD_DB_FUNCTION(td_thr_dbresume)
    LIBTHREAD_DB_FUNCTION(td_thr_dbsuspend)
    LIBTHREAD_DB_FUNCTION(td_thr_event_enable)
    LIBTHREAD_DB_FUNCTION(td_thr_event_getmsg)
    LIBTHREAD_DB_FUNCTION(td_thr_getfpregs)
    LIBTHREAD_DB_FUNCTION(td_thr_getgregs)
    LIBTHREAD_DB_FUNCTION(td_thr_getxregs)
    LIBTHREAD_DB_FUNCTION(td_thr_getxregsize)
    LIBTHREAD_DB_FUNCTION(td_thr_set_event)
    LIBTHREAD_DB_FUNCTION(td_thr_setfpregs)
    LIBTHREAD_DB_FUNCTION(td_thr_setgregs)
    LIBTHREAD_DB_FUNCTION(td_thr_setprio)
    LIBTHREAD_DB_FUNCTION(td_thr_setsigpending)
    LIBTHREAD_DB_FUNCTION(td_thr_setxregs)
    LIBTHREAD_DB_FUNCTION(td_thr_sigsetmask)
    LIBTHREAD_DB_FUNCTION(td_thr_tls_get_addr)
    LIBTHREAD_DB_FUNCTION(td_thr_tlsbase)
    LIBTHREAD_DB_FUNCTION(td_thr_tsd)
    LIBTHREAD_DB_FUNCTION(td_thr_validate)
#undef LIBTHREAD_DB_FUNCTION
    return td_init_orig();
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_new(struct ps_prochandle *__ps, td_thragent_t **__ta)
{
#if PRINT_LOGGING
    printf("custom-libthread_db: td_ta_new\n");
#endif
    my_prochandle = __ps;
    ps_err_e e = ps_pglobal_lookup(
        __ps,
        NULL,
        "_thread_db_userspace_threads",
        &thread_db_userspace_threads_addr);
    if (e != PS_OK) {
        fprintf(
            stderr,
            "FATAL: ps_pglobal_lookup of '_thread_db_userspace_threads' "
            "failed with %d\n",
            e);
        abort();
    }
#if PRINT_LOGGING
    printf(
        "custom-libthread_db: _thread_db_userspace_threads in inferior was "
        "resolved to %p\n",
        (void *)thread_db_userspace_threads_addr);
#endif
    e = thread_db_userspace_threads_read_current_thread_db_userspace_threads(
        __ps, thread_db_userspace_threads_addr);
    if (e != PS_OK) {
        fprintf(
            stderr,
            "FATAL: "
            "thread_db_userspace_threads_read_current_thread_db_userspace_"
            "threads failed with %d\n",
            e);
        abort();
    }
    return td_ta_new_orig(__ps, __ta);
}

LIBTHREAD_DB_EXTERN td_err_e td_ta_map_lwp2thr(
    td_thragent_t const *ta_p, lwpid_t lwpid, td_thrhandle_t *th_p)
{
#if PRINT_LOGGING
    printf("custom-libthread_db: td_ta_map_lwp2thr\n");
#endif
    ps_err_e e =
        thread_db_userspace_threads_read_current_thread_db_userspace_threads(
            my_prochandle, thread_db_userspace_threads_addr);
    if (e != PS_OK) {
        fprintf(
            stderr,
            "FATAL: "
            "thread_db_userspace_threads_read_current_thread_db_userspace_"
            "threads failed with %d\n",
            e);
        abort();
    }
    return thread_db_userspace_threads_td_ta_map_lwp2thr(
        td_ta_map_lwp2thr_orig, ta_p, lwpid, th_p);
}

LIBTHREAD_DB_EXTERN td_err_e td_ta_thr_iter(
    td_thragent_t const *ta_p, td_thr_iter_f *cb, void *cbdata_p,
    td_thr_state_e state, int ti_pri, sigset_t *ti_sigmask_p,
    unsigned ti_user_flags)
{
#if PRINT_LOGGING
    printf(
        "custom-libthread_db: td_ta_thr_iter cbdata_p = %p state = %d\n",
        cbdata_p,
        state);
#endif
    ps_err_e e =
        thread_db_userspace_threads_read_current_thread_db_userspace_threads(
            my_prochandle, thread_db_userspace_threads_addr);
    if (e != PS_OK) {
        fprintf(
            stderr,
            "FATAL: "
            "thread_db_userspace_threads_read_current_thread_db_userspace_"
            "threads failed with %d\n",
            e);
        abort();
    }
    return thread_db_userspace_threads_td_ta_thr_iter(
        td_ta_thr_iter_orig,
        ta_p,
        cb,
        cbdata_p,
        state,
        ti_pri,
        ti_sigmask_p,
        ti_user_flags);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_get_info(td_thrhandle_t const *th_p, td_thrinfo_t *ti_p)
{
#if PRINT_LOGGING
    printf("custom-libthread_db: td_thr_get_info\n");
#endif
    return thread_db_userspace_threads_td_thr_get_info(
        td_thr_get_info_orig, td_ta_map_lwp2thr_orig, th_p, ti_p);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_getgregs(td_thrhandle_t const *__th, prgregset_t __gregs)
{
#if PRINT_LOGGING
    printf("custom-libthread_db: td_thr_getgregs\n");
#endif
    return thread_db_userspace_threads_td_thr_getgregs(
        td_thr_getgregs_orig, __th, __gregs);
}

LIBTHREAD_DB_EXTERN td_err_e td_log(void)
{
    return td_log_orig();
}

LIBTHREAD_DB_EXTERN const char **td_symbol_list(void)
{
    return td_symbol_list_orig();
}

LIBTHREAD_DB_EXTERN td_err_e td_ta_delete(td_thragent_t *__ta)
{
    return td_ta_delete_orig(__ta);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_get_nthreads(td_thragent_t const *__ta, int *__np)
{
    return td_ta_get_nthreads_orig(__ta, __np);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_get_ph(td_thragent_t const *__ta, struct ps_prochandle **__ph)
{
    return td_ta_get_ph_orig(__ta, __ph);
}

LIBTHREAD_DB_EXTERN td_err_e td_ta_map_id2thr(
    td_thragent_t const *__ta, pthread_t __pt, td_thrhandle_t *__th)
{
    return td_ta_map_id2thr_orig(__ta, __pt, __th);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_tsd_iter(td_thragent_t const *__ta, td_key_iter_f *__ki, void *__p)
{
    return td_ta_tsd_iter_orig(__ta, __ki, __p);
}

LIBTHREAD_DB_EXTERN td_err_e td_ta_event_addr(
    td_thragent_t const *__ta, td_event_e __event, td_notify_t *__ptr)
{
    return td_ta_event_addr_orig(__ta, __event, __ptr);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_set_event(td_thragent_t const *__ta, td_thr_events_t *__event)
{
    return td_ta_set_event_orig(__ta, __event);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_clear_event(td_thragent_t const *__ta, td_thr_events_t *__event)
{
    return td_ta_clear_event_orig(__ta, __event);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_event_getmsg(td_thragent_t const *__ta, td_event_msg_t *__msg)
{
    return td_ta_event_getmsg_orig(__ta, __msg);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_setconcurrency(td_thragent_t const *__ta, int __level)
{
    return td_ta_setconcurrency_orig(__ta, __level);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_enable_stats(td_thragent_t const *__ta, int __enable)
{
    return td_ta_enable_stats_orig(__ta, __enable);
}

LIBTHREAD_DB_EXTERN td_err_e td_ta_reset_stats(td_thragent_t const *__ta)
{
    return td_ta_reset_stats_orig(__ta);
}

LIBTHREAD_DB_EXTERN td_err_e
td_ta_get_stats(td_thragent_t const *__ta, td_ta_stats_t *__statsp)
{
    return td_ta_get_stats_orig(__ta, __statsp);
}

LIBTHREAD_DB_EXTERN td_err_e td_thr_validate(td_thrhandle_t const *__th)
{
    return td_thr_validate_orig(__th);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_getfpregs(td_thrhandle_t const *__th, prfpregset_t *__regset)
{
    return td_thr_getfpregs_orig(__th, __regset);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_getxregs(td_thrhandle_t const *__th, void *__xregs)
{
    return td_thr_getxregs_orig(__th, __xregs);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_getxregsize(td_thrhandle_t const *__th, int *__sizep)
{
    return td_thr_getxregsize_orig(__th, __sizep);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_setfpregs(td_thrhandle_t const *__th, prfpregset_t const *__fpregs)
{
    return td_thr_setfpregs_orig(__th, __fpregs);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_setgregs(td_thrhandle_t const *__th, prgregset_t __gregs)
{
    return td_thr_setgregs_orig(__th, __gregs);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_setxregs(td_thrhandle_t const *__th, void const *__addr)
{
    return td_thr_setxregs_orig(__th, __addr);
}

LIBTHREAD_DB_EXTERN td_err_e td_thr_tlsbase(
    td_thrhandle_t const *__th, unsigned long int __modid, psaddr_t *__base)
{
    return td_thr_tlsbase_orig(__th, __modid, __base);
}

LIBTHREAD_DB_EXTERN td_err_e td_thr_tls_get_addr(
    td_thrhandle_t const *__th, psaddr_t __map_address, size_t __offset,
    psaddr_t *__address)
{
    return td_thr_tls_get_addr_orig(__th, __map_address, __offset, __address);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_event_enable(td_thrhandle_t const *__th, int __event)
{
    return td_thr_event_enable_orig(__th, __event);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_set_event(td_thrhandle_t const *__th, td_thr_events_t *__event)
{
    return td_thr_set_event_orig(__th, __event);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_clear_event(td_thrhandle_t const *__th, td_thr_events_t *__event)
{
    return td_thr_clear_event_orig(__th, __event);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_event_getmsg(td_thrhandle_t const *__th, td_event_msg_t *__msg)
{
    return td_thr_event_getmsg_orig(__th, __msg);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_setprio(td_thrhandle_t const *__th, int __prio)
{
    return td_thr_setprio_orig(__th, __prio);
}

LIBTHREAD_DB_EXTERN td_err_e td_thr_setsigpending(
    td_thrhandle_t const *__th, unsigned char __n, sigset_t const *__ss)
{
    return td_thr_setsigpending_orig(__th, __n, __ss);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_sigsetmask(td_thrhandle_t const *__th, sigset_t const *__ss)
{
    return td_thr_sigsetmask_orig(__th, __ss);
}

LIBTHREAD_DB_EXTERN td_err_e
td_thr_tsd(td_thrhandle_t const *__th, thread_key_t const __tk, void **__data)
{
    return td_thr_tsd_orig(__th, __tk, __data);
}

LIBTHREAD_DB_EXTERN td_err_e td_thr_dbsuspend(td_thrhandle_t const *__th)
{
    return td_thr_dbsuspend_orig(__th);
}

LIBTHREAD_DB_EXTERN td_err_e td_thr_dbresume(td_thrhandle_t const *__th)
{
    return td_thr_dbresume_orig(__th);
}
