#pragma once

#include <stdio.h>

void cleanup_free(char *const *);

void cleanup_close(int *);

void cleanup_fclose(FILE *const *);
