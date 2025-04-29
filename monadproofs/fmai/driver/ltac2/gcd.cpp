#define uint unsigned int

uint
gcd(uint a, uint b) {
    while (b != 0) {
        uint temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

struct Point {
    int x;
    int y;
};

struct Node {
    Node(Node *next, int data) : next_(next), data_(data) {}

    Node *next_;
    int data_;
};

typedef Node *List;

void
split(List ab, List &a, List &b) {
    bool which = true;
    while (ab) {
        auto temp = ab->next_;
        if (which) {
            ab->next_ = a;
            a = ab;
        } else {
            ab->next_ = b;
            b = ab;
        }
        ab = temp;
        which = !which;
    }
}

List
reverse(List cur) {
    List prev = nullptr;
    List next = nullptr;
    while (cur != nullptr) {
        next = cur->next_;
        cur->next_ = prev;
        prev = cur;
        cur = next;
    }
    return prev;
}

unsigned long
length(List l) {
    unsigned long i = 0;
    while (l != nullptr) {
        i++;
        l = l->next_;
    }
    return i;
}

/*
#include <zeta/zeta.hpp>

class SpinLock {
public:
    SpinLock() : locked(false) {}

    void lock() {
        while (locked.exchange(true))
            ;
    }

    void unlock() { locked.store(false); }

private:
    atomic<bool> locked;
};

class ConcList {
    void reverse() {
        sp.lock();
        list = ::reverse(list);
        sp.unlock();
    }
    unsigned long length() {
        sp.lock();
        auto l = ::length(list);
        sp.unlock();
        return l;
    }

private:
    SpinLock sp;
    List list;
};

#define uint64 unsigned long long

class ReadWriteLock {
public:
    ReadWriteLock() : rw_count(0) {}

    void lock_read() {
        uint64 expected_rw_count = rw_count;
        do {
            expected_rw_count
                = expected_rw_count - expected_rw_count % 2; // decrement the writer if one exists. there can only be one. we only
                                                             // want the CAS below to succeed if there are no writers
        } while (!rw_count.cas(expected_rw_count, increment_reader_count(expected_rw_count)));
    }

    void unlock_read() { rw_count.fetch_sub(2); }

    void lock_write() {
        uint64 expected_rw_count = rw_count; // atomic load via operator overloading
        do {
            expected_rw_count = 0;           // the CAS below should succeed only if there are no readers and no writers
        } while (!rw_count.cas(expected_rw_count, increment_writer_count(expected_rw_count)));
    }

    void unlock_write() { rw_count.fetch_sub(1); }

private:
    atomic<uint64> rw_count; // rw_count=2*num_readers*num_writer. num_writer =0 or 1
    uint64 num_readers() { return rw_count / 2; }
    uint64 num_writer() { return rw_count % 2; }
    static uint64 increment_writer_count(uint64 old_rw_count) { return old_rw_count + 1; }
    static uint64 increment_reader_count(uint64 old_rw_count) { return old_rw_count + 2; }
};
*/
