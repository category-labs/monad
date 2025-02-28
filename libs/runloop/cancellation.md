# Cancellation model

Cancellation is one of the most fraught parts of any async i/o executor.
This particular async i/o executor takes an explicit 'cancellation point'
based design whereby specific APIs when invoked by a cancelled task will
return an errored result comparing equivalent to `ECANCELED`. The task
is then responsible for cancelling all outstanding i/o, cleaning itself
up and exiting. It is 100% on the task to regularly call an API which is
a cancellation point to determine whether it has been cancelled -- the
task will not be interrupted or halted otherwise.

Be aware that cancellation is very much considered a slow path both by
this i/o executor and by io_uring. You should expect it to have between
poor and dismal performance.

The explicit 'cancellation point' design is lifted from Microsoft NT
'alertable wait states' exactly the same way as our i/o status design is also
from NT's `IOSTATUS`. We have considerably simplified both over what NT
offers both for efficiency and reduced cognitive load, however if you
are familiar with how NT (or indeed VMS/RSX) implements alertable i/o
including cancellation thereof, it's exactly the same design here minus
function callbacks.


## Cancelling a task

`monad_async_task_cancel()` will cancel a pending, suspended or running
task. This is a threadsafe API which can be invoked from any kernel thread.

If the task has not yet launched, it will no longer launch. If the task
is currently running, it will be told that it has been cancelled the next
time it enters a *cancellation point*. If the task is currently suspended
within a cancellation point, it will be resumed and told it has been
cancelled. If the task is currently suspended in a non-cancellation point,
it will be told that it has been cancelled the next time it resumes and
then suspends on a cancellation point.

The simplest example of task cleanup after receiving cancellation would
be:

```c
for (;;) {
    monad_async_io_status *completed = nullptr;
    monad_c_result r = monad_async_task_suspend_until_completed_io(
        &completed,
        task,
        monad_async_duration_infinite_non_cancelling));
    CHECK_RESULT(r);
    if(r.value == 0) {
        break;
    }
    if (completed == nullptr) {
        continue;
    }
    process_completion(completed);
}
```

This will suspend the task in a non-cancellable wait until all i/o status
based i/o initiated by the task has completed and been reaped.

It is important to note that any new i/o that a cancelled task initiates
will be instantly completed as cancelled, and never initiated with io_uring
at all. This prevents poorly written task code from unintentionally ignoring
cancellation, however it can also be unhelpful e.g. if you need to write out
new data as part of cleanup.

In the case where you do need to initiate new i/o as part of cleanup,
generally it is easiest to do one of:

1. Use your own mechanism of notifying a task of cancellation so your
task isn't officially cancelled when it does i/o as part of cleanup.

2. Use `monad_async_task_suspend_save_detach_and_invoke()` and
`monad_async_task_from_foreign_context()` to detach and reattach yourself
to the current i/o executor, thus resetting the cancellation state.

3. Use non-io_uring i/o e.g. blocking `pwritev()`.

4. Sometimes launching a new throwaway task is just easier.

If you destroy an executor with extant tasks, those tasks will all be
cancelled and the loop run until all tasks have exited before the
destruction of the executor will return. Thus tasks which don't exit
quickly under cancellation can hang the destruction of the executor.
You will especially notice this if the process suddenly exits e.g. due
to test failure, and during process exit the execution destruction
hangs.


## Cancelling i/o

It is important to note cancelling a task has nothing to do with cancelling
i/o, except where a task suspends awaiting i/o or initiates new i/o. If
the task is suspended on a 'suspending' i/o e.g. `monad_async_task_file_range_sync()`,
then cancelling that task will cancel that i/o with io_uring before
resuming the task. Inflight 'non-suspending' i/o i.e. all those taking an i/o
status as their identifier e.g. `monad_async_task_socket_receivev()`
are **never** cancelled by task cancellation, only newly initiated
'non-suspending' i/o. Instead you may explicitly cancel each individual
inflight i/o identified by its `monad_async_io_status *` using
`monad_async_task_io_cancel()` (note that this is not thread safe, and
must be called within the same kernel thread as the run loop).

Be aware that cancelling most file i/o isn't worth it over just waiting
for it to complete normally: io_uring often just ignores the cancellation
request until the i/o completes anyway, then you gets lots of added
overhead for no actual gain. This is particularly the case for non-direct
i.e. kernel cached i/o.

If you attempt to exit a task with i/o initiated still pending or with
i/o completed not reaped, the program will abort. This ensures you don't
accidentally orphan i/o, which as it writes into its i/o status would mean
potential memory corruption. If you stack unwind an i/o status before it
completes, you may see an Address Sanitiser failure as you would be writing
into freed stack or memory.
