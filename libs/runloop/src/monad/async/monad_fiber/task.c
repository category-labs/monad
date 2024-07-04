#include "task.h"
#include "assert.h"
#include <malloc.h>
#include <string.h>

static size_t const monad_fiber_task_queue_chunk = 256;

void monad_fiber_task_queue_init(struct monad_fiber_task_queue *this)
{
    this->memory =
        malloc(sizeof(monad_fiber_task_t *) * monad_fiber_task_queue_chunk);
    this->capacity = monad_fiber_task_queue_chunk;
    this->data = this->memory;
    this->size = 0u;
}

void monad_fiber_task_queue_destroy(struct monad_fiber_task_queue *this)
{
    free(this->memory);
}

void monad_fiber_task_queue_grow(struct monad_fiber_task_queue *this)
{
    size_t const old_cap = this->capacity;
    monad_fiber_task_t **pre = this->memory;

    this->capacity += monad_fiber_task_queue_chunk;

    ptrdiff_t data_offset = (this->data - pre);
    void *new_mem =
        realloc(this->memory, this->capacity * sizeof(monad_fiber_task_t *));

    MONAD_ASSERT(new_mem);
    bool const is_wrapped =
        (this->data + this->size) > (this->memory + old_cap);
    this->memory = new_mem;

    if (this->memory != pre) {
        this->data = this->memory + data_offset;
    }

    // we may have two chunks of memory - if that's the case, we need to memmove
    // the upper part.
    if (is_wrapped) {

        size_t const prev_cap = this->capacity - monad_fiber_task_queue_chunk;
        size_t const wrapped =
            (size_t)((this->data + this->size) - (this->memory + prev_cap));
        size_t const pre_wrapped =
            (size_t)((this->memory + prev_cap) - this->data);

        if (wrapped <= monad_fiber_task_queue_chunk) // we move the smaller one
        {
            MONAD_ASSERT(this->memory);
            memmove(
                this->memory + prev_cap,
                this->memory,
                wrapped * sizeof(monad_fiber_task_t *));
        }
        else {
            MONAD_ASSERT(this->data);
            this->data = memmove(
                this->data + monad_fiber_task_queue_chunk,
                this->data,
                pre_wrapped * sizeof(monad_fiber_task_t *));
        }
    }
}

monad_fiber_task_t *
monad_fiber_task_queue_pop_front(struct monad_fiber_task_queue *this)
{
    MONAD_ASSERT(this->size > 0ull);
    monad_fiber_task_t **t = this->data;
    MONAD_ASSERT(t != NULL);

    this->data++;
    this->size--;
    if (this->data == (this->memory + this->capacity)) {
        this->data = this->memory;
    }

    return *t;
}

void monad_fiber_task_queue_insert(
    struct monad_fiber_task_queue *this, monad_fiber_task_t *task)
{
    if (this->size == this->capacity) { // resize
        monad_fiber_task_queue_grow(this);
    }

    monad_fiber_task_t **itr = this->data, **end = this->data + this->size;

    if (this->size == 0u) {
        this->size++;
        itr = this->data = this->memory;
        *itr = task;
        return;
    }

    // push back & push front
    if ((*this->data)->priority > task->priority) // we can push front
    {
        if (this->data == this->memory) {
            this->data = this->memory + this->capacity;
        }

        itr = --this->data;
        *itr = task;
        this->size++;
        return;
    }

    if (end >= (this->memory + this->capacity)) {
        end -= this->capacity;
    }

    // push back
    if (this->size > 0u) {
        monad_fiber_task_t **last = this->data + (this->size - 1);
        if (last >= (this->memory + this->capacity)) {
            last -= this->capacity;
        }
        if ((*last)->priority <= task->priority) {
            (*end) = task;
            this->size++;
            return;
        }
    }

    MONAD_ASSERT(end >= this->memory);

    // this can potentially be optimized through a binary search algorithm.
    while (itr != end) {
        if ((*itr)->priority > task->priority) {
            break;
        }

        itr++;
        if (itr == (this->memory + this->capacity)) {
            itr = this->memory;
        }
    }

    MONAD_ASSERT(itr <= (this->memory + this->capacity));

    if (itr != end) // we need to shift elements right
    {
        if (end < itr) // are we wrapping around the end of the buffer
        {
            monad_fiber_task_t **mem_end = this->memory + this->capacity;

            // this shifts the lower part (DEF in the below example)
            MONAD_ASSERT(this->memory);
            memmove(
                this->memory + 1,
                this->memory,
                ((size_t)(end - this->memory) * sizeof(monad_fiber_task_t *)));

            if (itr == mem_end) // we're at the end of memory, no need to do a
                                // second shift.
            {
                // that's the insert
                // | D | E | F |   |  | A | B | C |
                // | X | D | E | F |  | A | B | C |
                itr = this->memory;
            }
            else {

                // | D | E | F |   |   | A | B | C |
                // | C | D | E | F |   | A | X | B |
                this->memory[0] =
                    this->memory[this->capacity - 1]; // wrap one element around
                                                      // (C)
                // move B
                // | C | D | E | F |   | A | X | B |
                //                           ^ itr   ^ mem_end
                memmove(
                    itr + 1,
                    itr,
                    (size_t)((mem_end - itr) - 1) *
                        sizeof(monad_fiber_task_t *));
            }
        }
        else {
            memmove(
                itr + 1,
                itr,
                (size_t)(end - itr) * sizeof(monad_fiber_task_t *));
        }
    }
    *itr = task;
    this->size++;
}
