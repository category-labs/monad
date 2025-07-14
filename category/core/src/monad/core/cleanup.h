#pragma once

#include <stdio.h>

#ifdef __cplusplus
extern "C"
{
#endif

void cleanup_free(char *const *);

void cleanup_close(int *);

void cleanup_fclose(FILE *const *);

#ifdef __cplusplus
}
#endif
