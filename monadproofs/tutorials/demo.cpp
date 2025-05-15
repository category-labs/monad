#include <thread>
//#include <utility>
//#include <iostream>

using uint = unsigned int;

uint x = 0;
uint y;

void foo() {
    y=0;
    y=x+1;
}

int a = 0;
int *ptr;

void fooptr () {
    ptr = &a;
}

int b = 0;
void sfoo() {
    b=a+1;
}



uint twice (uint x) {return 2*x;}
void doubleInPlace (uint & x) {x=2*x;}

/*
 pre |-- loopinv 
 loopinv ** [| loopcond |] {loopbody} loopinv
 loopinv ** [| ~loopcondition |] => postcondition (a'=gcd av ab) */

uint gcd(uint a, uint b) {
    while (b != 0) {
        uint temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

void gcd(const uint &a, const uint &b, uint &result) {
    result=gcd(a,b);
}


template<typename LambdaStruct>
class Thread {
    const LambdaStruct lambda;
    std::thread worker;

public:
    void start() {
        worker = std::thread([this]() {
            lambda();
        });
    }

    void join() {
        if(worker.joinable())
            worker.join();
    }

    ~Thread() {
        if(worker.joinable())
            worker.join();
    }

    Thread(const Thread&) = delete;
    Thread& operator=(const Thread&) = delete;

    Thread(Thread&& other)
        : lambda(std::move(other.lambda)), worker(std::move(other.worker)) {}

    Thread& operator=(Thread&& other) {
        if (this != &other)
        {
            lambda = std::move(other.lambda);
            worker = std::move(other.worker);
        }
        return *this;
    }

    Thread(const LambdaStruct &lambda) : lambda(lambda) {}
};

void parallel_gcd_lcm(const uint &a, const uint &b, uint &gcd_result, uint &lcm_result) {
    Thread t1([&gcd_result, &a, &b]() {
           gcd(a, b, gcd_result);
       });
    t1.start();
    uint product=a*b;// pretend this is expensive, e.g. 1000 bit numbers
    t1.join();
    lcm_result=product/gcd_result;
}
/*
Just Before `t1.start()`:
┌───────────────────────────────────────────────────────────────┐
│  Main Thread owns:                                            │
│  gcd_result |-> anyR "unsigned int" 1                         │
│  lcm_result |-> anyR "unsigned int" 1                         │
│  a |-> primR "unsigned int" qa av                             │
│  b |-> primR "unsigned int" qb bv                             │
└───────────────────────────────────────────────────────────────┘

Just after t1.start:
┌───────────────────────────────────────────┬───────────────────────────────────────────┐
│  Child Thread (t1)                        │  Main Thread (parent)                     │
│  ──────────────────────────────────────   │  ──────────────────────────────────────   │
│  gcd_result |-> anyR "unsigned int" 1     │  lcm_result |-> anyR "unsigned int" 1     │
│  a |-> primR "unsigned int" (qa/2) av     │  a |-> primR "unsigned int" (qa/2) av     │
│  b |-> primR "unsigned int" (qb/2) bv     │  b |-> primR "unsigned int" (qb/2) bv     │
└───────────────────────────────────────────┴───────────────────────────────────────────┘

 */

void parallel_gcd_lcm_wrong(const uint &a, const uint &b, uint &gcd_result, uint &lcm_result) {
    Thread t1([&gcd_result, &a, &b]() {
        gcd(a,b, gcd_result);
    });
    t1.start();
    uint product=a*b;
    lcm_result=product/gcd_result;
    t1.join();
}

uint parallel_gcd_lcm2(uint a, uint b, uint &gcd_result) {
    Thread t1([&gcd_result, a, b]() {
          gcd_result=gcd(a,b);
       });
    t1.start();
    uint product=a*b;// pretend this is expensive, e.g. 1000 bit numbers
    t1.join();
    return product/gcd_result;
}

