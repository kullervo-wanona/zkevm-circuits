//! EVM byte code generator

use bus_mapping::evm::OpcodeId;
use num::BigUint;

/// EVM Bytecode
#[derive(Debug)]
pub struct Bytecode {
    code: Vec<u8>,
}

impl Bytecode {
    /// New Bytecode
    pub fn new() -> Self {
        Bytecode { code: vec![] }
    }

    /// Get the generated code
    pub fn code(&self) -> Vec<u8> {
        self.code.clone()
    }

    /// Append
    pub fn append(&mut self, other: &mut Bytecode) {
        self.code.append(&mut other.code);
    }

    /// Write op
    pub fn write_op(&mut self, op: OpcodeId) -> &mut Self {
        self.write(op.as_u8())
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
        self.write(OpcodeId::PUSH1.as_u8() + ((n - 1) as u8));

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
        for i in n..32 {
            assert!(bytes[i] == 0u8, "value too big for PUSH{}", n);
        }
        self
    }
}

/// EVM code line macro
#[macro_export]
macro_rules! bytecode_line {
    // Default opcode without any inputs
    ($code:expr, $x:ident) => {{
        $code.write_op(bus_mapping::evm::OpcodeId::$x);
    }};
    // PUSHX op codes
    ($code:expr, ($x:ident, $v: expr)) => {{
        let opcode_id = bus_mapping::evm::OpcodeId::$x.as_u8();
        assert!(
            bus_mapping::evm::OpcodeId::PUSH1.as_u8() <= opcode_id
                && opcode_id <= bus_mapping::evm::OpcodeId::PUSH32.as_u8(),
            "invalid push"
        );
        let n = bus_mapping::evm::OpcodeId::$x.as_u8()
            - bus_mapping::evm::OpcodeId::PUSH1.as_u8()
            + 1;
        $code.push(n as usize, $v);
    }};
    // PUSH op codes with X as argument
    ($code:expr, ($x:ident, $n: expr, $v: expr)) => {{
        //assert!($x == "PUSH", "invalid push");
        $code.push($n, $v);
    }};
}

/// EVM code macro
#[macro_export]
macro_rules! bytecode {
    ( $( $x:tt ), * ) => {{
        let mut code = Bytecode::new();
        $(
            crate::bytecode_line!(code, $x);
        )*
        code
    }};
}
