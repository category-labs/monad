#pragma once

enum class InstrumentationDevice
{
    // Use cachegrind to collect measurements.
    Cachegrind,
    // Use a simple wall clock timer to collect measurements.
    WallClock
};
