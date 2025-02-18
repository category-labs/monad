#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include! {"async.rs"}

#[cfg(test)]
mod tests {
    use super::*;

    unsafe extern "C" fn test_executor_works_user_code(
        task_: monad_context_task,
    ) -> monad_c_result {
        let task = task_ as monad_async_task;
        *((*task).derived.user_ptr as *mut i32) = 1;
        {
            let current_executor: monad_async_executor =
                to_atomic_ptr::<monad_async_executor_head>(&(*task).current_executor)
                    .load(std::sync::atomic::Ordering::Acquire);
            let current_executor_task: monad_async_task =
                to_atomic_ptr::<monad_async_task_head>(&(*current_executor).current_task)
                    .load(std::sync::atomic::Ordering::Acquire);
            assert_eq!(current_executor_task, task);
            assert_eq!((*current_executor).tasks_pending_launch, 0);
            assert_eq!((*current_executor).tasks_running, 1);
            assert_eq!((*current_executor).tasks_suspended, 0);
        }
        unsafe {
            to_result(monad_async_task_suspend_for_duration(
                std::ptr::null_mut(),
                task,
                10000000, /* 10 milliseconds */
            ))
            .unwrap();
        }
        *((*task).derived.user_ptr as *mut i32) = 2;
        {
            let current_executor: monad_async_executor =
                to_atomic_ptr::<monad_async_executor_head>(&(*task).current_executor)
                    .load(std::sync::atomic::Ordering::Acquire);
            let current_executor_task: monad_async_task =
                to_atomic_ptr::<monad_async_task_head>(&(*current_executor).current_task)
                    .load(std::sync::atomic::Ordering::Acquire);
            assert_eq!(current_executor_task, task);
            assert_eq!((*current_executor).tasks_pending_launch, 0);
            assert_eq!((*current_executor).tasks_running, 1);
            assert_eq!((*current_executor).tasks_suspended, 0);
        }
        monad_c_make_success(5)
    }

    #[test]
    fn test_executor_works() {
        {
            let mut ex_attr = monad_async_executor_attr {
                ..Default::default()
            };
            ex_attr.io_uring_ring.entries = 64;
            let ex = monad_async_executor_ptr::new(&mut ex_attr).unwrap();
            println!("ex = {:?}", ex);
            println!("ex->tasks_running = {}", unsafe {
                (*ex.head).tasks_running
            });

            let test = |switcher: &monad_context_switcher_ptr, desc: &str| {
                let mut t_attr = monad_async_task_attr {
                    ..Default::default()
                };
                let mut ts = timespec {
                    ..Default::default()
                };
                println!("\n\n   With {} context switcher ...", desc);
                for n in 0..10 {
                    let task = monad_async_task_ptr::new(switcher.head, &mut t_attr).unwrap();
                    let mut did_run: i32 = 0;
                    unsafe {
                        (*task.head).derived.user_ptr =
                            &mut did_run as *mut _ as *mut ::std::os::raw::c_void
                    };
                    unsafe { (*task.head).derived.user_code = Some(test_executor_works_user_code) };
                    unsafe {
                        to_result(monad_async_task_attach(
                            ex.head,
                            task.head,
                            std::ptr::null_mut(),
                        ))
                        .unwrap();
                    }
                    unsafe {
                        assert_eq!((*task.head).is_pending_launch, true);
                        assert_eq!((*task.head).is_running, false);
                        assert_eq!((*task.head).is_suspended_awaiting, false);
                        assert_eq!((*task.head).is_suspended_completed, false);
                        assert_eq!((*ex.head).current_task, std::ptr::null_mut());
                        assert_eq!((*ex.head).tasks_pending_launch, 1);
                        assert_eq!((*ex.head).tasks_running, 0);
                        assert_eq!((*ex.head).tasks_suspended, 0);
                    }
                    ts.tv_sec = 3; // timeout and fail the test after this
                    let mut r: isize = unsafe {
                        to_result(monad_async_executor_run(ex.head, 1, &mut ts)).unwrap()
                    }; // runs and suspends
                    let ticks_when_resumed = unsafe { (*task.head).ticks_when_resumed };
                    assert_eq!(did_run, 1);
                    unsafe {
                        assert_eq!((*ex.head).tasks_pending_launch, 0);
                        assert_eq!((*ex.head).tasks_running, 0);
                        assert_eq!((*ex.head).tasks_suspended, 1);
                        assert_eq!(r, 1);
                        assert_eq!((*task.head).is_pending_launch, false);
                        assert_eq!((*task.head).is_running, false);
                        assert_eq!((*task.head).is_suspended_awaiting, true);
                        assert_eq!((*task.head).is_suspended_completed, false);
                    }
                    r = unsafe {
                        to_result(monad_async_executor_run(ex.head, 1, &mut ts)).unwrap()
                    }; // returns early when next timeout would fire
                    assert_eq!(did_run, 1);
                    unsafe {
                        assert_eq!((*ex.head).tasks_pending_launch, 0);
                        assert_eq!((*ex.head).tasks_running, 0);
                        assert_eq!((*ex.head).tasks_suspended, 1);
                        assert_eq!(r, 0);
                        assert_eq!((*task.head).is_pending_launch, false);
                        assert_eq!((*task.head).is_running, false);
                        assert_eq!((*task.head).is_suspended_awaiting, true);
                        assert_eq!((*task.head).is_suspended_completed, false);
                    }
                    r = unsafe {
                        to_result(monad_async_executor_run(ex.head, 1, &mut ts)).unwrap()
                    }; // resumes and exits
                    assert_eq!(did_run, 2);
                    unsafe {
                        assert_eq!((*ex.head).tasks_pending_launch, 0);
                        assert_eq!((*ex.head).tasks_running, 0);
                        assert_eq!((*ex.head).tasks_suspended, 0);
                        assert_eq!(r, 1);
                        assert_eq!((*task.head).is_pending_launch, false);
                        assert_eq!((*task.head).is_running, false);
                        assert_eq!((*task.head).is_suspended_awaiting, false);
                        assert_eq!((*task.head).is_suspended_completed, false);
                        assert_eq!(to_result((*task.head).derived.result).unwrap(), 5);
                        if n == 9 {
                            print!(
                                "\n   Task attach to task initiate took {} ticks.",
                                ticks_when_resumed - (*task.head).ticks_when_attached
                            );
                            print!(
                                "\n   Task initiate to task suspend await took {} ticks.",
                                (*task.head).ticks_when_suspended_awaiting - ticks_when_resumed
                            );
                            print!(
                                "\n   Task suspend await to task suspend completed took {} ticks.",
                                (*task.head).ticks_when_suspended_completed
                                    - (*task.head).ticks_when_suspended_awaiting
                            );
                            print!(
                                "\n   Task suspend completed to task resume took {} ticks.",
                                (*task.head).ticks_when_resumed
                                    - (*task.head).ticks_when_suspended_completed
                            );
                            print!(
                                "\n   Task resume to task detach took {} ticks.",
                                (*task.head).ticks_when_detached - (*task.head).ticks_when_resumed
                            );
                            println!(
                                "\n   Task executed for a total of {} ticks.",
                                (*task.head).total_ticks_executed
                            );
                        }
                    }
                }
            };
            {
                let switcher = unsafe {
                    monad_context_switcher_ptr::new(&monad_context_switcher_sjlj).unwrap()
                };
                test(&switcher, "setjmp/longjmp");
            }
        }
    }
}
