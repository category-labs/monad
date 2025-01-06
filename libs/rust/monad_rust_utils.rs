// Rust representation of a Boost.Outcome Result
pub type MonadCResult<T> = Result<T, cxx_status_code_system>;

unsafe impl Send for cxx_status_code_system {}

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

fn to_result(res: cxx_result_status_code_system_monad) -> MonadCResult<isize> {
    if (res.flags & 1) == 1 {
        return Ok(res.value);
    }
    Err(res.error)
}
