//! EVM byte code generator

use crate::evm::OpcodeId;
use num::BigUint;
use std::collections::HashMap;

/// EVM Bytecode
#[derive(Debug)]
pub struct Bytecode {
    code: Vec<u8>,
    num_opcodes: usize,
    markers: HashMap<String, usize>,
}

impl Bytecode {
    /// New Bytecode
    pub fn new() -> Self {
        Bytecode {
            code: vec![],
            num_opcodes: 0,
            markers: HashMap::new(),
        }
    }

    /// Get the generated code
    pub fn to_bytes(&self) -> Vec<u8> {
        self.code.clone()
    }

    /// Append
    pub fn append(&mut self, other: &mut Bytecode) {
        self.code.append(&mut other.code);
        for (key, val) in other.markers.iter() {
            self.insert_marker(key, self.num_opcodes + val);
        }
        self.num_opcodes += other.num_opcodes;
    }

    /// Write op
    pub fn write_op(&mut self, op: OpcodeId) -> &mut Self {
        self.write_op_internal(op.as_u8())
    }

    fn write_op_internal(&mut self, op: u8) -> &mut Self {
        self.num_opcodes += 1;
        self.write(op)
    }

    /// Write byte
    pub fn write(&mut self, byte: u8) -> &mut Self {
        self.code.push(byte);
        self
    }

    /// Push
    pub fn push(&mut self, n: usize, value: BigUint) -> &mut Self {
        assert!(1 <= n && n <= 32, "invalid push");

        // Write the op code
        self.write_op_internal(OpcodeId::PUSH1.as_u8() + ((n - 1) as u8));

        let mut bytes = value.to_bytes_le();
        // Pad to 32 bytes
        for _ in bytes.len()..32 {
            bytes.push(0u8);
        }
        // Write the bytes
        for i in 0..n {
            self.write(bytes[n - 1 - i]);
        }
        // Check if the full value could be pushed
        for i in n..bytes.len() {
            assert!(bytes[i] == 0u8, "value too big for PUSH{}: {}", n, value);
        }
        self
    }

    /// Add marker
    pub fn add_marker(&mut self, marker: String) -> &mut Self {
        self.insert_marker(&marker, self.num_opcodes);
        self
    }

    /// Insert marker
    pub fn insert_marker(&mut self, marker: &String, pos: usize) {
        assert!(!self.markers.contains_key(marker), "marker already used: {}", marker);
        self.markers.insert(marker.clone(), pos);
    }

    /// Get the position of a marker
    pub fn get_pos(&self, marker: &str) -> usize {
        *self.markers.get(&marker.to_string()).expect(format!("marker '{}' not found", marker).as_str())
    }
}

/// EVM code macro
#[macro_export]
macro_rules! bytecode {
    ($($args:tt)*) => {{
        let mut code = Bytecode::new();
        $crate::bytecode_internal!(code, $($args)*);
        code
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! bytecode_internal {
    // Nothing left to do
    ($code:ident, ) => {};
    // Default opcode without any inputs
    ($code:ident, $x:ident; $($rest:tt)*) => {{
        $code.write_op(crate::evm::OpcodeId::$x);
        crate::bytecode_internal!($code, $($rest)*);
    }};
    // PUSHX op codes
    ($code:ident, $x:ident $v: expr; $($rest:tt)*) => {{
        let opcode_id = crate::evm::OpcodeId::$x.as_u8();
        assert!(
            crate::evm::OpcodeId::PUSH1.as_u8() <= opcode_id
                && opcode_id <= crate::evm::OpcodeId::PUSH32.as_u8(),
            "invalid push"
        );
        let n = crate::evm::OpcodeId::$x.as_u8()
            - crate::evm::OpcodeId::PUSH1.as_u8()
            + 1;
        $code.push(n as usize, $v.into());
        crate::bytecode_internal!($code, $($rest)*);
    }};
    // Marker
    ($code:ident, [$marker:tt] $($rest:tt)*) => {{
        $code.add_marker(stringify!($marker).to_string());
        crate::bytecode_internal!($code, $($rest)*);
    }};
}
