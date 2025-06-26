// Rust representation of a Boost.Outcome Result
pub type MonadCResult<T> = Result<T, cxx_status_code_system>;

unsafe impl Send for cxx_status_code_system {}
unsafe impl Sync for cxx_status_code_system {}

impl std::fmt::Display for cxx_status_code_system {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            String::from_utf8_lossy(unsafe {
                CStr::from_ptr(outcome_status_code_message(
                    self as *const _ as *const ::std::os::raw::c_void,
                ))
                .to_bytes()
            })
        )
    }
}

impl std::fmt::Debug for cxx_status_code_system {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            String::from_utf8_lossy(unsafe {
                CStr::from_ptr(outcome_status_code_message(
                    self as *const _ as *const ::std::os::raw::c_void,
                ))
                .to_bytes()
            })
        )
    }
}

impl std::error::Error for cxx_status_code_system {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}

impl From<cxx_status_code_system> for std::io::Error {
    fn from(val: cxx_status_code_system) -> Self {
        // This is nasty, and we ought to figure out a better way of doing this
        for n in 1..200 {
            if unsafe {
                outcome_status_code_equal_generic(
                    &val as *const cxx_status_code_system as *const ::std::os::raw::c_void,
                    n,
                ) != 0
            } {
                return Self::new(Self::from_raw_os_error(n).kind(), val);
            }
        }
        Self::new(std::io::ErrorKind::Other, val)
    }
}

impl std::fmt::Debug for cxx_result_status_code_system_monad {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if (self.flags & 1) == 1 {
            let v: MonadCResult<isize> = Ok(self.value);
            v.fmt(f)
        } else {
            let v: MonadCResult<isize> = Err(self.error);
            v.fmt(f)
        }
    }
}

pub fn to_result(res: cxx_result_status_code_system_monad) -> MonadCResult<isize> {
    if (res.flags & 1) == 1 {
        return Ok(res.value);
    }
    Err(res.error)
}

pub fn success(val: isize) -> monad_c_result {
    unsafe { monad_c_make_success(val) }
}

pub fn failure_from_errno(val: ::std::os::raw::c_int) -> monad_c_result {
    unsafe { monad_c_make_failure(val) }
}
