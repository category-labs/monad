#include "demo.cpp"
#include <atomic>

uint gcdl (uint * nums, uint length) {
    uint result=0;
    for (uint i=0; i<length; i++) {
        result=gcd(result, nums[i]);
    }
    return result;
}

void ubptr(){
  int arrl[3];
  int *p=arrl;
  p++;
  p++;
  p++;
  p++;
}

void okptr(){
  int arrl[3];
  int *p=arrl;
  p++;
  p++;
  p++;
}
  
uint parallel_gcdl(uint * nums, uint length) {
    uint mid=length/2;
    uint resultl;
    Thread t1([nums, mid, &resultl]() {
        resultl=gcdl(nums, mid);
    });
    t1.start();
    uint resultr=gcdl(nums+mid, length-mid);
    t1.join();
    return gcd(resultl, resultr);
}

uint fold_left(uint * nums, uint length, uint (*f)(uint, uint), uint id) {
    uint result=id;
    for (uint i=0; i<length; i++) {
        result=f(result, nums[i]);
    }
    return result;
}

uint parallel_fold_left(uint * nums, uint length, uint (*f)(uint, uint), uint id) {
    uint mid=length/2;
    uint resultl;
    Thread t1([nums, mid, &resultl, f, id]() {
        resultl=fold_left(nums, mid, f, id);
    });
    t1.start();
    uint resultr=fold_left(nums+mid, length-mid, f, id);
    t1.join();
    return f(resultl, resultr);
}



struct Node {
    Node(Node *next, int data) : next_(next), data_(data) {}

    Node *next_;
    int data_;
    void incdataM(){
      this->data_++;
    }
  ~Node(){}
  
};

typedef Node * List;

List reverse(List l) {
  List prev = nullptr;
  List next = nullptr;
  while (l != nullptr) {
    next = l->next_;
    l->next_ = prev;
    prev = l;
    l = next;
  }
    return prev;
}

void split(List ab, List &a, List &b) {
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

void move_cons(List &from, List &to) {
  auto t = from->next_;
  from->next_ = to;
  to = from;
  from = t;
}

// [rev_append] could be written as a tail-recursive function
// but not all compilation levels will optimize this to constant
// space.
List rev_append(List a, List rest) {
  while (a) {
    move_cons(a, rest);
  }
  return rest;
}

// this does a reverse merge, i.e. it changes the order of the list
List rev_merge(bool dir, List a, List b) {
  List result = nullptr;
  do {
    if (a) {
      if (b) {
        if (a->data_ < b->data_)
          move_cons(dir ? b : a, result);
        else
          move_cons(dir ? a : b, result);
      } else
        return rev_append(a, result);
    } else
      return rev_append(b, result);
  } while (true);
}

List merge(List a, List b) {
  if (not a) return b;
  if (not b) return a;
  if (a->data_ < b->data_) {
    a->next_ = merge(a->next_, b);
    return a;
  } else {
    b->next_ = merge(a, b->next_);
    return b;
  }
}

List merge_sort_rec(List ls) {
  if (ls && ls->next_) {
    List a = nullptr, b = nullptr;
    split(ls, a, b);
    a = merge_sort_rec(a);
    b = merge_sort_rec(b);
    return merge(a, b);
  } else
    return ls;
}

List sort(List l) {
    return merge_sort_rec(l);
}

int z = 0;
void bar() {
    z = 1;
}
                                              
/*
Parent Thread                        
     ├───────────────────────────────────►
     │                            Child Thread
   setU(5)                                │
     │                                setU(6)
     │                                    │
   setU(7)                                │
     │                                    │
*/
std::atomic<int> u;
void setU(int value) {
    u.store(value);
}
                               
/*                                           
Parent Thread                                
     │                                       
     │  Create Concurrent Invariant:                  
     │    ┌───────────────────────────┐    
     │    │  ∃ i: Z, u |-> atomicR 1 i│ 
     │    └───────────────────────────┘  
     ├───────────────────────────────────►
     │                            Child Thread
     │                                    │
   setU(5)                                │
     │                                    │
     │                                setU(6) 
     │                                    │
 */

int setThenGetU(int uvnew) {
  u.store(uvnew);
  //       
  return u.load();
}

int getU() {
  return u.load();
}

class SpinLock {
public:
  SpinLock() : locked(false) {}

// returns only when exchange atomically flips locked FROM false to true
  void lock() {
    while (locked.exchange(true));
  }
  void unlock() { locked.store(false); }

private:
  std::atomic<bool> locked;
};
// foo.exchange(bar): atomically reads foo and sets it to bar. returns the original value.

List cons(int data, List l){
  List res = new (std::nothrow) Node(l, data);
  return res;
}

/*
Parent Thread                        
     ├───────────────────────────────────►
     │                            Child Thread
   push(5)                                │
     │                                    push(4)
     │                                    │
*/

class ConcLList{
  SpinLock lock;
  List head;
  bool push(int data)
  {
    bool success=false;
    lock.lock();
    head=cons(data,head);
    if(head)
      success=true;
    lock.unlock();
    return success;
  }

  void creverse()
  {
    lock.lock();
    head=reverse(head);
    lock.unlock();
  }
};

int testgcdl() {
    uint vec[] = {48, 18, 30};
    return parallel_gcdl(vec, 3);
}

void incdata(Node * n){
  n->data_++;
}

std::atomic<uint> uldkjflkasj;// just to force clang to produce the ast of std::atomic<uint>. there is probably a better way to do it


// uint256.hpp  ── core definition, no #includes
class uint256 {
public:
  using limb_t = unsigned long long;          // assumes 64-bit limbs
  limb_t data[4];                             // little-endian: data[0] is least-significant

  uint256() : data{0, 0, 0, 0} {}
  
  void add(const uint256& other);
};
