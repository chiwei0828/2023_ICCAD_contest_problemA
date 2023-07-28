#ifndef TIMER_
#define TIMER_

#include <chrono>

class Timer{
public:
    Timer() : start_time_(std::chrono::high_resolution_clock::now()){}

    void Reset(){
        start_time_ = std::chrono::high_resolution_clock::now();
    }

    double GetElapsedMillseconds() const {
        auto end_time = std::chrono::high_resolution_clock::now();
        std::chrono::duration<double, std::milli> elapsed = end_time - start_time_;
        return elapsed.count();
    }
private:
    std::chrono::time_point<std::chrono::high_resolution_clock> start_time_;
};

#endif