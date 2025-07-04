#pragma once

#include <chrono>

enum class Timeunit
{
    nano,
    micro,
    milli,
    seconds,
};

std::string short_string_of_timeunit(Timeunit const u)
{
    switch (u) {
    case Timeunit::nano:
        return "ns";
    case Timeunit::micro:
        return "us";
    case Timeunit::milli:
        return "ms";
    case Timeunit::seconds:
        return "s";
    }

    throw std::runtime_error("invalid time unit");
}

Timeunit timeunit_of_short_string(std::string const &s)
{
    if (s == "ns") {
        return Timeunit::nano;
    }
    if (s == "us") {
        return Timeunit::micro;
    }
    if (s == "ms") {
        return Timeunit::milli;
    }
    if (s == "s") {
        return Timeunit::seconds;
    }

    throw std::runtime_error("unsupported time unit");
}

using Clock = std::chrono::high_resolution_clock;

class Stopwatch
{
public:
    Stopwatch()
        : running(false)
        , elapsed_time(std::chrono::nanoseconds::zero())
    {
    }

    void start()
    {
        if (!running) {
            start_time = Clock::now();
            running = true;
        }
    }

    void pause()
    {
        if (running) {
            auto const now = Clock::now();
            elapsed_time += now - start_time;
            running = false;
        }
    }

    std::chrono::nanoseconds elapsed() const
    {
        if (running) {
            return elapsed_time + (Clock::now() - start_time);
        }
        return elapsed_time;
    }

    std::string elapsed_formatted_string(Timeunit u)
    {
        using namespace std::literals;
        switch (u) {
        case Timeunit::nano:
            return std::format("{}", elapsed() / 1ns);
        case Timeunit::micro:
            return std::format("{}", elapsed() / 1us);
        case Timeunit::milli:
            return std::format("{}", elapsed() / 1ms);
        case Timeunit::seconds:
            return std::format("{}", elapsed() / 1s);
        }

        throw std::runtime_error("invalid time unit");
    }

private:
    bool running;
    Clock::time_point start_time;
    std::chrono::nanoseconds elapsed_time;
};

Stopwatch timer{};
