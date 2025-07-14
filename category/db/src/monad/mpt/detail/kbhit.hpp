#pragma once

#include <cstdarg>
#include <cstdio>
#include <cstring>
#include <iostream>

#include <sys/ioctl.h>
#include <termios.h>
#include <unistd.h>

inline bool kbhit()
{
    termios term;
    tcgetattr(0, &term);

    termios term2 = term;
    term2.c_lflag &= tcflag_t(~ICANON);
    tcsetattr(0, TCSANOW, &term2);

    int byteswaiting;
    ioctl(0, FIONREAD, &byteswaiting);

    tcsetattr(0, TCSANOW, &term);
    return byteswaiting > 0;
}

inline int getch()
{
    termios term;
    tcgetattr(0, &term);

    termios term2 = term;
    term2.c_lflag &= tcflag_t(~ICANON);
    tcsetattr(0, TCSANOW, &term2);

    char ret = 0;
    if (1 == ::read(0, &ret, 1)) {
        tcsetattr(0, TCSANOW, &term);
        return ret;
    }
    tcsetattr(0, TCSANOW, &term);
    return -1;
}

inline char tty_ask_question(char const *msg, ...)
{
    va_list vl;
    termios term;
    tcgetattr(0, &term);

    termios term2 = term;
    term2.c_lflag &= tcflag_t(~ICANON);
    tcsetattr(0, TCSANOW, &term2);

    std::cout << std::flush;
    va_start(vl, msg);
    vprintf(msg, vl);
    va_end(vl);
    fflush(stdout);

    char buffer[256];
    buffer[0] = -1;
    for (;;) {
        auto readed = ::read(0, buffer, sizeof(buffer));
        if (readed < 0) {
            std::cerr << "FATAL: Somehow file descriptor 0 (stdin) is not "
                         "readable! Error was: "
                      << strerror(errno) << std::endl;
            abort();
        }
        if (readed > 0) {
            break;
        }
    }
    tcsetattr(0, TCSANOW, &term);

    return buffer[0];
}
