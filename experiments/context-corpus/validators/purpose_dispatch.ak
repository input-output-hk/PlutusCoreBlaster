use cardano/script_context.{ScriptContext, Minting, Spending, Withdrawing, Publishing, Voting, Proposing}
use aiken/primitive/bytearray

validator purpose_dispatch {
  else(context: ScriptContext) {
    when context.info is {
      Minting(policy) -> bytearray.length(policy) == 28
      Spending { output, datum: _ } -> output.output_index >= 0
      Withdrawing(_) -> True
      Publishing { at, certificate: _ } -> at >= 0
      Voting(_) -> True
      Proposing { at, proposal_procedure: _ } -> at >= 0
    }
  }
}
