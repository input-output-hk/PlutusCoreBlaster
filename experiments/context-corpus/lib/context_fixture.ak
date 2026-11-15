use cardano/script_context.{ScriptContext, Spending}
use cardano/transaction.{OutputReference, placeholder}

pub fn encoded_placeholder() -> Data {
  let context = ScriptContext {
    transaction: placeholder,
    redeemer: 0,
    info: Spending {
      output: OutputReference {
        transaction_id: #"0000000000000000000000000000000000000000000000000000000000000000",
        output_index: 0,
      },
      datum: None,
    },
  }
  let encoded: Data = context
  encoded
}
