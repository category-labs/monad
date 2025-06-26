#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include! {"monad_triedb_driver.rs"}

use std::ffi::OsStr;
use std::os::fd::FromRawFd;
use std::os::unix::ffi::OsStrExt;

extern "C" {
    pub fn monad_make_temporary_file(buffer: *mut ::std::os::raw::c_char, buffer_len: usize)
        -> i32;
}

struct NamedTempFile {
    dbpaths: [PathBuf; 1],
}

impl NamedTempFile {
    #[allow(dead_code)]
    fn new() -> NamedTempFile {
        let mut buffer: [::std::os::raw::c_char; 256] = [Default::default(); 256];
        let fd = unsafe {
            std::fs::File::from_raw_fd(monad_make_temporary_file(buffer.as_mut_ptr(), 256))
        };
        fd.set_len(256 * 1024 * 1024).unwrap();
        let path =
            OsStr::from_bytes(unsafe { CStr::from_ptr(buffer.as_ptr() as *const i8) }.to_bytes());
        NamedTempFile {
            dbpaths: [path.into()],
        }
    }
}

impl Drop for NamedTempFile {
    fn drop(&mut self) {
        std::fs::remove_file(&self.dbpaths[0]).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_result_works() {
        let mut dbdirpaths: [*const ::std::os::raw::c_char; 1] = [std::ptr::null_mut()];
        let mut db: *mut monad_c_triedb = 1 as u64 as *mut monad_c_triedb;
        let raw_result = unsafe { monad_c_triedb_open(dbdirpaths.as_mut_ptr(), &mut db) };
        let result = to_result(raw_result);
        assert!(result.is_err());
        let msg = format!("{}", result.err().unwrap());
        println!(
            "   Error message returned by incorrect use of monad_c_triedb_open() is '{}'",
            msg
        );
        assert_eq!(msg, "Invalid argument");
    }

    #[test]
    fn test_triedb_works() {
        let tempfile = NamedTempFile::new();
        println!(
            "   Temp db file path is '{}'",
            tempfile.dbpaths[0].display()
        );
        let result = TriedbHandle::new(&tempfile.dbpaths);
        assert!(result.is_err());
        let msg = format!("{}", result.err().unwrap());
        println!(
            "   Error message returned by use of monad_c_triedb_open() on invalid DB file is '{}'",
            msg
        );
        assert!(msg.starts_with("Storage pool source"));
        assert!(msg.ends_with("has not been initialised for use with storage pool"));
    }
}
