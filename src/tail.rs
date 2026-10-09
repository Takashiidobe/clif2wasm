use std::collections::HashMap;
use wasm_encoder::reencode::Reencode;

use crate::error::{Error, Result};

pub enum Target {
    Direct(u32),
    Indirect(u32, u32),
}

struct TailCalls(HashMap<u32, Target>);

impl Reencode for TailCalls {
    type Error = std::convert::Infallible;

    fn instruction<'a>(
        &mut self,
        op: wasmparser::Operator<'a>,
    ) -> std::result::Result<
        wasm_encoder::Instruction<'a>,
        wasm_encoder::reencode::Error<Self::Error>,
    > {
        if let wasmparser::Operator::Call { function_index } = op
            && let Some(target) = self.0.get(&function_index)
        {
            return Ok(match target {
                Target::Direct(index) => wasm_encoder::Instruction::ReturnCall(*index),
                Target::Indirect(sig, table) => wasm_encoder::Instruction::ReturnCallIndirect {
                    type_index: *sig,
                    table_index: *table,
                },
            });
        }
        wasm_encoder::reencode::utils::instruction(self, op)
    }
}

pub fn rewrite(bytes: &[u8], targets: HashMap<u32, Target>) -> Result<Vec<u8>> {
    if targets.is_empty() {
        return Ok(bytes.to_vec());
    }
    let mut output = wasm_encoder::Module::new();
    TailCalls(targets)
        .parse_core_module(&mut output, wasmparser::Parser::new(0), bytes)
        .map_err(|error| Error::general(error.to_string()))?;
    Ok(output.finish())
}
