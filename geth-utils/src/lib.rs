//! Connection to external EVM tracer.

use std::ffi::{CStr, CString};
use std::os::raw::c_char;

extern "C" {
    fn CreateTrace(config: GoString, code: GoString) -> *const c_char;
}

/// A Go string.
#[repr(C)]
struct GoString {
    a: *const c_char,
    b: i64,
}

/// Creates the trace
pub fn trace(config: &str, code: Vec<u8>) -> Result<String, ()> {
    let c_config = CString::new(config).expect("invalid config");
    let c_code = unsafe { CString::from_vec_unchecked(code) };
    let go_config = to_go_string(&c_config);
    let go_code = to_go_string(&c_code);
    let result = unsafe {
         CreateTrace(
            go_config,
            go_code
        )
    };
    let c_str = unsafe { CStr::from_ptr(result) };
    let string = c_str
        .to_str()
        .expect("Error translating EVM trace from library");
    match string.is_empty() || string.starts_with("Error") {
        true => Err(()),
        false => Ok(string.to_string()),
    }
}

fn to_go_string(data: &CString) -> GoString {
    let ptr = data.as_ptr();
    GoString {
        a: ptr,
        b: data.as_bytes().len() as i64,
    }
}
