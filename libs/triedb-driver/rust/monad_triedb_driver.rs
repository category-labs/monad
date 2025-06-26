include! {"monad_triedb_driver_raw_bindings.rs"}
include! {"../../rust/monad_rust_utils.rs"}

use std::{
    ffi::CStr,
    fmt::{Debug, Formatter},
    path::PathBuf,
    sync::{
        atomic::{AtomicUsize, Ordering::AcqRel},
        Arc,
    },
};

#[derive(Debug)]
struct TriedbBytes {
    head: monad_c_triedb_bytes,
}

impl Default for TriedbBytes {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

impl TriedbBytes {
    #[allow(dead_code)]
    fn from_isize(p: isize) -> TriedbBytes {
        TriedbBytes {
            head: p as *const u8 as monad_c_triedb_bytes,
        }
    }
    #[allow(dead_code)]
    fn from_ptr(p: *const u8) -> TriedbBytes {
        TriedbBytes {
            head: p as monad_c_triedb_bytes,
        }
    }
}

impl Drop for TriedbBytes {
    fn drop(&mut self) {
        unsafe {
            if self.head.as_ref().is_some() {
                to_result(monad_c_triedb_finalize(self.head)).unwrap();
            }
        }
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug)]
pub struct TriedbHandle {
    db_ptr: *mut monad_c_triedb,
}

impl Default for TriedbHandle {
    fn default() -> Self {
        let mut s = ::std::mem::MaybeUninit::<Self>::uninit();
        unsafe {
            ::std::ptr::write_bytes(s.as_mut_ptr(), 0, 1);
            s.assume_init()
        }
    }
}

pub trait ReadAsyncSender {
    fn send(&mut self, t: MonadCResult<Vec<u8>>);
}

pub struct SenderContext {
    sender: Box<dyn ReadAsyncSender>,
    completed_counter: Arc<AtomicUsize>,

    // The strong count of this dummy Arc<> reflects the total number of currently executing
    // (concurrent) requests, and this number is used by upstream code to maintain request
    // backpressure.  When this request completes, this Arc<> is implicitly dropped, which
    // causes the concurrent request count to be decremented.
    #[allow(dead_code)]
    concurrency_tracker: Arc<()>,
}

pub trait TraverseAsyncSender {
    fn send(&mut self, t: MonadCResult<Vec<TraverseEntry>>);
}

impl Debug for dyn TraverseAsyncSender {
    fn fmt(&self, _: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        Ok(())
    }
}

#[derive(Debug)]
pub struct TraverseContext {
    // values in traversal order
    data: std::sync::Mutex<Vec<TraverseEntry>>,
    sender: Box<dyn TraverseAsyncSender>,

    // The strong count of this dummy Arc<> reflects the total number of currently executing
    // (concurrent) requests, and this number is used by upstream code to maintain request
    // backpressure.  When this request completes, this Arc<> is implicitly dropped, which
    // causes the concurrent request count to be decremented.
    #[allow(dead_code)]
    concurrency_tracker: Arc<()>,
}

#[derive(Debug)]
pub struct TraverseEntry {
    pub key: Vec<u8>,
    pub value: Vec<u8>,
}

/// # Safety
/// This should be used only as a callback for async TrieDB calls
///
/// This function is called by TrieDB once it proceses a single read async call
pub unsafe extern "C" fn read_async_callback(
    value_ptr: monad_c_result,
    value_len: usize,
    sender_context: *mut std::ffi::c_void,
) {
    // Unwrap the sender context struct
    let mut sender_context = unsafe { Box::from_raw(sender_context as *mut SenderContext) };
    // Increment the completed counter
    sender_context.completed_counter.fetch_add(1, AcqRel);
    let result = to_result(value_ptr);
    if result.is_err() {
        // Send the retrieved result through the channel
        sender_context.sender.send(Err(result.err().unwrap()));
        return;
    }
    let _unvalue_ptr = TriedbBytes::from_isize(value_ptr.value);

    if value_len == 0 {
        // Send the retrieved result through the channel
        sender_context.sender.send(Ok(Vec::new()));
        return;
    }

    let value =
        unsafe { std::slice::from_raw_parts(value_ptr.value as *const u8, value_len).to_vec() };

    // Send the retrieved result through the channel
    sender_context.sender.send(Ok(value));
}

/// # Safety
/// This is used as a callback when traversing the transaction or receipt trie
pub unsafe extern "C" fn traverse_callback(
    kind: monad_c_result,
    context: *mut std::ffi::c_void,
    key_ptr: *const u8,
    key_len: usize,
    value_ptr: *const u8,
    value_len: usize,
) {
    let mut traverse_context = unsafe { Box::from_raw(context as *mut TraverseContext) };

    let r = to_result(kind);
    if let Err(err) = r {
        traverse_context.sender.send(Err(err));
        // traverse_context is freed here, because we don't call Box::into_raw
        return;
    }
    let op_kind = r.unwrap() as triedb_async_traverse_callback;

    if op_kind == triedb_async_traverse_callback_triedb_async_traverse_callback_finished_early {
        traverse_context.sender.send(Ok(Vec::new()));
        // traverse_context is freed here, because we don't call Box::into_raw
        return;
    }
    if op_kind == triedb_async_traverse_callback_triedb_async_traverse_callback_finished_normally {
        // completed
        let mut lock = traverse_context.data.lock().expect("mutex poisoned");
        traverse_context.sender.send(Ok(std::mem::take(&mut *lock)));
        // traverse_context is freed here, because we don't call Box::into_raw
        return;
    }
    assert_eq!(
        op_kind,
        triedb_async_traverse_callback_triedb_async_traverse_callback_value
    );

    let key = unsafe {
        let key = std::slice::from_raw_parts(key_ptr, key_len).to_vec();
        key
    };

    let value = unsafe {
        let value = std::slice::from_raw_parts(value_ptr, value_len).to_vec();
        value
    };

    {
        let mut lock = traverse_context.data.lock().expect("mutex poisoned");
        lock.push(TraverseEntry { key, value });
    }

    // prevent Box<TraverseContext> from dropping
    let _ = Box::into_raw(traverse_context);
}

impl TriedbHandle {
    pub fn new(dbdirpaths: &[PathBuf]) -> MonadCResult<TriedbHandle> {
        let mut ret = TriedbHandle {
            ..Default::default()
        };
        // Turns out PathBuf's internal OSStr doesn't zero terminate. This is
        // absolutely daft design given it's an **OS String**, but I'm not going
        // to judge. We'll need an array of CString copies which are zero
        // terminated.
        let c_dbdirpaths: Vec<std::ffi::CString> = dbdirpaths
            .iter()
            .map(|x| std::ffi::CString::new(x.as_os_str().as_encoded_bytes()).unwrap())
            .collect();
        // And then a C compatible array of pointers to said CString
        let mut cptr_dbdirpaths: Vec<*const ::std::os::raw::c_char> =
            c_dbdirpaths.iter().map(|x| x.as_ptr()).collect();
        cptr_dbdirpaths.push(std::ptr::null());
        unsafe {
            to_result(monad_c_triedb_open(
                cptr_dbdirpaths.as_mut_ptr(),
                &mut ret.db_ptr,
            ))?;
        }
        Ok(ret)
    }

    #[allow(dead_code)]
    pub fn read(&self, key: &[u8], key_len_nibbles: u8, block_id: u64) -> MonadCResult<Vec<u8>> {
        let mut value_ptr = std::ptr::null();
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            panic!("Key length nibbles exceeds maximum allowed value");
        }
        if (key_len_nibbles as usize + 1) / 2 > key.len() {
            panic!("Key length is insufficient for the given nibbles");
        }

        let result = to_result(unsafe {
            monad_c_triedb_read(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                &mut value_ptr,
                block_id,
            )
        })?;
        let _unvalue_ptr = TriedbBytes::from_ptr(value_ptr);

        let value_len = result as usize;
        if value_len == 0 {
            return Ok(Vec::new());
        }

        let value = unsafe {
            let value = std::slice::from_raw_parts(value_ptr, value_len).to_vec();
            value
        };

        Ok(value)
    }

    /// This is used to make an async read call to TrieDB.
    /// It creates a oneshot channel and Boxes its sender and the completed_counter
    /// into a context struct and passes it to TrieDB. When TrieDB completes processing
    /// the call, it will call the `read_async_callback` which will unwrap the context
    /// struct, increment the completed_counter, and send the retrieved TrieDB value
    /// through the channel.
    /// The user needs to poll TrieDB using the `triedb_poll` function to pump the async
    /// reads and wait on the returned receiver for the value.
    /// NOTE: the returned receiver must be resolved before key is dropped
    #[allow(dead_code)]
    pub fn read_async(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        completed_counter: Arc<AtomicUsize>,
        sender: Box<dyn ReadAsyncSender>,
        concurrency_tracker: Arc<()>,
    ) {
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            panic!("Key length nibbles exceeds maximum allowed value");
        }
        if (key_len_nibbles as usize + 1) / 2 > key.len() {
            panic!("Key length is insufficient for the given nibbles");
        }

        // Wrap the sender and completed_counter in a context struct
        let sender_context = Box::new(SenderContext {
            sender,
            completed_counter,
            concurrency_tracker,
        });

        unsafe {
            // Convert the struct into a raw pointer which will be sent to the callback function
            let sender_context_ptr = Box::into_raw(sender_context);

            monad_c_triedb_async_read(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                Some(read_async_callback), // TrieDB read async callback
                sender_context_ptr as *mut std::ffi::c_void,
            );
        }
    }

    /// Used to pump async reads in TrieDB
    /// if blocking is true, the thread will sleep at least until 1 completion is available to process
    /// if blocking is false, poll will return if no completion is available to process
    /// max_completions is used as a bound for maximum completions to process in this poll
    ///
    /// Returns the number of completions processed
    /// NOTE: could call poll internally: number of calls to this functions != number of completions processed
    #[allow(dead_code)]
    pub fn triedb_poll(&self, blocking: bool, max_completions: usize) -> MonadCResult<usize> {
        let res =
            to_result(unsafe { monad_c_triedb_poll(self.db_ptr, blocking, max_completions) })?;
        Ok(res as usize)
    }

    pub fn traverse_triedb_async(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        sender: Box<dyn TraverseAsyncSender>,
        concurrency_tracker: Arc<()>,
    ) {
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            panic!("Key length nibbles exceeds maximum allowed value");
        }
        if (key_len_nibbles as usize + 1) / 2 > key.len() {
            panic!("Key length is insufficient for the given nibbles");
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker,
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            monad_c_triedb_async_traverse(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                context,
                Some(traverse_callback),
            );
        };
    }

    #[allow(dead_code)]
    pub fn traverse_triedb_sync(
        &self,
        key: &[u8],
        key_len_nibbles: u8,
        block_id: u64,
        sender: Box<dyn TraverseAsyncSender>,
    ) {
        // make sure doesn't overflow
        if key_len_nibbles >= u8::MAX - 1 {
            panic!("Key length nibbles exceeds maximum allowed value");
        }
        if (key_len_nibbles as usize + 1) / 2 > key.len() {
            panic!("Key length is insufficient for the given nibbles");
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker: Arc::new(()),
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            // sync result is already handled by traverse_callback
            monad_c_triedb_traverse(
                self.db_ptr,
                key.as_ptr(),
                key_len_nibbles,
                block_id,
                context,
                Some(traverse_callback),
            );
        };
    }

    pub fn range_get_triedb_async(
        &self,
        prefix_key: &[u8],
        prefix_key_len_nibbles: u8,
        min_key: &[u8],
        min_key_len_nibbles: u8,
        max_key: &[u8],
        max_key_len_nibbles: u8,
        block_id: u64,
        sender: Box<dyn TraverseAsyncSender>,
        concurrency_tracker: Arc<()>,
    ) {
        // make sure doesn't overflow
        if min_key_len_nibbles >= u8::MAX - 1 {
            panic!("Min key length nibbles exceeds maximum allowed value");
        }
        if (min_key_len_nibbles as usize + 1) / 2 > min_key.len() {
            panic!("Min key length is insufficient for the given nibbles");
        }
        if max_key_len_nibbles >= u8::MAX - 1 {
            panic!("Max key length nibbles exceeds maximum allowed value");
        }
        if (max_key_len_nibbles as usize + 1) / 2 > max_key.len() {
            panic!("Max key length is insufficient for the given nibbles");
        }

        let traverse_context = Box::new(TraverseContext {
            data: std::sync::Mutex::new(Default::default()),
            sender,
            concurrency_tracker,
        });

        unsafe {
            let context = Box::into_raw(traverse_context) as *mut std::ffi::c_void;
            monad_c_triedb_async_ranged_get(
                self.db_ptr,
                prefix_key.as_ptr(),
                prefix_key_len_nibbles,
                min_key.as_ptr(),
                min_key_len_nibbles,
                max_key.as_ptr(),
                max_key_len_nibbles,
                block_id,
                context,
                Some(traverse_callback),
            );
        };
    }

    #[allow(dead_code)]
    pub fn latest_voted_block(&self) -> MonadCResult<u64> {
        let res = to_result(unsafe { monad_c_triedb_latest_voted_block(self.db_ptr) })?;
        Ok(res as u64)
    }

    pub fn latest_voted_round(&self) -> MonadCResult<u64> {
        let res = to_result(unsafe { monad_c_triedb_latest_voted_round(self.db_ptr) })?;
        Ok(res as u64)
    }

    pub fn latest_finalized_block(&self) -> MonadCResult<u64> {
        let res = to_result(unsafe { monad_c_triedb_latest_finalized_block(self.db_ptr) })?;
        Ok(res as u64)
    }

    pub fn latest_verified_block(&self) -> MonadCResult<u64> {
        let res = to_result(unsafe { monad_c_triedb_latest_verified_block(self.db_ptr) })?;
        Ok(res as u64)
    }

    pub fn earliest_finalized_block(&self) -> MonadCResult<u64> {
        let res = to_result(unsafe { monad_c_triedb_earliest_finalized_block(self.db_ptr) })?;
        Ok(res as u64)
    }
}

impl Drop for TriedbHandle {
    fn drop(&mut self) {
        unsafe {
            if self.db_ptr.as_ref().is_some() {
                to_result(monad_c_triedb_close(self.db_ptr)).unwrap();
            }
        }
    }
}
