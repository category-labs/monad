#pragma once

static inline unsigned char
get_nibble(unsigned char const *const d, unsigned const n)
{
    unsigned char r = d[n / 2];
    if (n % 2 == 0) {
        r >>= 4;
    }
    else {
        r &= 0xF;
    }
    return r;
}

static inline void
set_nibble(unsigned char *const d, unsigned const n, unsigned char const v)
{
    unsigned char r = d[n / 2];
    if (n % 2 == 0) {
        r &= 0xF;
        r |= (v << 4);
    }
    else {
        r &= 0xF0;
        r |= (v & 0xF);
    }
    d[n / 2] = r;
}
