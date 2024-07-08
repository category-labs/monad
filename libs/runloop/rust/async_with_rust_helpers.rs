include!{"async.rs"}

// Rust representation of a Boost.Outcome Result
pub type MonadAsyncResult<T> = Result<T, cxx_status_code_system>;

impl std::fmt::Display for cxx_status_code_system {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // This is wrong and needs to be fixed properly later
    write!(f, "{}", std::io::Error::from_raw_os_error(self.value as i32).to_string())
  }
}

fn to_result(res: cxx_result_status_code_system_monad_async) -> MonadAsyncResult<isize> {
  if (res.flags & 1) == 1 {
    return Ok(res.value);
  }
  Err(res.error)
}


// Helper function to form a Rust atomic from what bindgen emits
unsafe fn to_atomic_ptr<'a, T>(p: *mut u64) -> &'a std::sync::atomic::AtomicPtr<T> {
  &*(p as *const std::sync::atomic::AtomicPtr<T>)
}


#[allow(dead_code)]
#[derive(Debug)]
struct monad_async_executor_ptr {
  head: monad_async_executor
}

impl Default for monad_async_executor_ptr {
  fn default() -> Self {
      let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
      unsafe {
          ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
          s.assume_init()
      }
  }
}

impl monad_async_executor_ptr {
  #[allow(dead_code)]
  fn new(ex_attr: &mut monad_async_executor_attr) -> MonadAsyncResult<monad_async_executor_ptr> {
    let mut ret = monad_async_executor_ptr { ..Default::default() }; 
    unsafe { to_result(monad_async_executor_create(&mut ret.head, ex_attr))?; }
    Ok(ret)
  }
}

impl Drop for monad_async_executor_ptr {
  fn drop(&mut self) {
    unsafe {
      if self.head.as_ref().is_some() {
        to_result(monad_async_executor_destroy(self.head)).unwrap();
      }
    }
  }
}


#[allow(dead_code)]
#[derive(Debug)]
struct monad_async_context_switcher_ptr {
  head: monad_async_context_switcher
}

impl Default for monad_async_context_switcher_ptr {
  fn default() -> Self {
      let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
      unsafe {
          ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
          s.assume_init()
      }
  }
}

impl monad_async_context_switcher_ptr {
  #[allow(dead_code)]
  fn new(implem: &monad_async_context_switcher_impl) -> MonadAsyncResult<monad_async_context_switcher_ptr> {
    let mut ret = monad_async_context_switcher_ptr { ..Default::default() }; 
    unsafe { to_result(implem.create.unwrap()(&mut ret.head))?; }
    Ok(ret)
  }
}

impl Drop for monad_async_context_switcher_ptr {
  fn drop(&mut self) {
    unsafe {
      if self.head.as_ref().is_some() {
        to_result((*self.head).self_destroy.unwrap()(self.head)).unwrap();
      }
    }
  }
}


#[allow(dead_code)]
#[derive(Debug)]
struct monad_async_task_ptr {
  head: monad_async_task
}

impl Default for monad_async_task_ptr {
  fn default() -> Self {
      let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
      unsafe {
          ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
          s.assume_init()
      }
  }
}

impl monad_async_task_ptr {
  #[allow(dead_code)]
  fn new(switcher: monad_async_context_switcher, attr: *mut monad_async_task_attr) -> MonadAsyncResult<monad_async_task_ptr> {
    let mut ret = monad_async_task_ptr { ..Default::default() }; 
    unsafe { to_result(monad_async_task_create(&mut ret.head, switcher, attr))?; }
    Ok(ret)
  }
}

impl Drop for monad_async_task_ptr {
  fn drop(&mut self) {
    unsafe {
      if self.head.as_ref().is_some() {
        to_result(monad_async_task_destroy(self.head)).unwrap();
      }
    }
  }
}
