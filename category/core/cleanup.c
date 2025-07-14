#include <category/core/cleanup.h>

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include <unistd.h>

void cleanup_free(char *const *const ptr)
{
    assert(ptr);
    if (*ptr) {
        free(*ptr);
    }
}

void cleanup_close(int *const fd)
{
    assert(fd);
    if (*fd != -1) {
        close(*fd);
        *fd = -1;
    }
}

void cleanup_fclose(FILE *const *const stream)
{
    assert(stream);
    if (*stream) {
        fclose(*stream);
    }
}
