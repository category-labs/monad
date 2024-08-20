#include <monad/core/cgroup.h>

#include <monad/core/cleanup.h>
#include <monad/core/cpuset.h>

#include <libcgroup.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <threads.h>

#include <sched.h>
#include <sys/sysinfo.h>

#define LOG_CGROUP_ERROR(msg, ...)                                             \
    do {                                                                       \
        fprintf(stderr, "CPU Isolation Failed: " msg "\n", ##__VA_ARGS__);     \
    }                                                                          \
    while (0)

static void monad_cgroup_init_or_exit()
{
    int const result = cgroup_init();

    if (result) {
        LOG_CGROUP_ERROR("cgroup init failed (%s)", cgroup_strerror(result));
        exit(EXIT_FAILURE);
    }
}

void monad_cgroup_init()
{
    static once_flag flag = ONCE_FLAG_INIT;
    call_once(&flag, monad_cgroup_init_or_exit);
}

static char *get_current_cgroup()
{
    FILE *const fp [[gnu::cleanup(cleanup_fclose)]] =
        fopen("/proc/self/cgroup", "r");
    if (!fp) {
        LOG_CGROUP_ERROR("failed to open /proc/self/cgroup");
        return NULL;
    }

    char *cgroup = NULL;
    while (!feof(fp)) {
        int id = 0;
        char *cgroup_path [[gnu::cleanup(cleanup_free)]] = NULL;
        int const result = fscanf(fp, "%d::%ms\n", &id, &cgroup_path);
        if (result != 2) {
            LOG_CGROUP_ERROR("failed to parse /proc/self/cgroup");
            return NULL;
        }
        if (id == 0) {
            cgroup = cgroup_path;
            cgroup_path = NULL;
        }
        else {
            LOG_CGROUP_ERROR("cgroups version 1 not supported");
            return NULL;
        }
    }

    return cgroup;
}

cpu_set_t monad_cgroup_cpuset()
{
    int result;

    monad_cgroup_init();

    char *const path [[gnu::cleanup(cleanup_free)]] = get_current_cgroup();
    if (!path) {
        LOG_CGROUP_ERROR("failed to get current cgroup");
        exit(EXIT_FAILURE);
    }

    struct cgroup *current_cgroup [[gnu::cleanup(cgroup_free)]] =
        cgroup_new_cgroup(path);
    if (!current_cgroup) {
        LOG_CGROUP_ERROR("failed to create cgroup");
        exit(EXIT_FAILURE);
    }

    result = cgroup_get_cgroup(current_cgroup);
    if (result) {
        LOG_CGROUP_ERROR("failed to get cgroup (%s)", cgroup_strerror(result));
        exit(EXIT_FAILURE);
    }

    struct cgroup_controller *const cpuset_controller =
        cgroup_get_controller(current_cgroup, "cpuset");
    if (!cpuset_controller) {
        LOG_CGROUP_ERROR("failed to get cpuset controller");
        exit(EXIT_FAILURE);
    }

    char *value [[gnu::cleanup(cleanup_free)]] = NULL;
    result = cgroup_get_value_string(
        cpuset_controller, "cpuset.cpus.partition", &value);
    if (result) {
        LOG_CGROUP_ERROR(
            "failed to get cpuset partition (%s)", cgroup_strerror(result));
        exit(EXIT_FAILURE);
    }
    if (strcmp(value, "isolated") != 0 && strcmp(value, "root") != 0) {
        LOG_CGROUP_ERROR("cpuset is not isolated");
        exit(EXIT_FAILURE);
    }
    free(value);
    value = NULL;

    result = cgroup_get_value_string(
        cpuset_controller, "cpuset.cpus.effective", &value);
    if (result) {
        LOG_CGROUP_ERROR(
            "failed to get cpuset effective cpus (%s)",
            cgroup_strerror(result));
        exit(EXIT_FAILURE);
    }

    return monad_parse_cpuset(value);
}
