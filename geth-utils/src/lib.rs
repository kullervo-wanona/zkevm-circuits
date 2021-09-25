//! Connection to external EVM tracer.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;

extern "C" {
    fn CreateTrace(path: GoString) -> *const c_char;
}

/// A Go string.
#[repr(C)]
struct GoString {
    a: *const c_char,
    b: i64,
}

/// Creates the trace
pub fn create_trace(code: Vec<u8>) -> Result<String, ()> {
    let c_code = unsafe { CString::from_vec_unchecked(code) };
    let ptr = c_code.as_ptr();
    let go_string = GoString {
        a: ptr,
        b: c_code.as_bytes().len() as i64,
    };
    let result = unsafe { CreateTrace(go_string) };
    let c_str = unsafe { CStr::from_ptr(result) };
    let string = c_str
        .to_str()
        .expect("Error translating EVM trace from library");
    match string.is_empty() || string.starts_with("Error") {
        true => Err(()),
        false => Ok(string.to_string()),
    }
}
