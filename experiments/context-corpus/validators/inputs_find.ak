use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator inputs_find {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.inputs, fn(input) { input.output_reference.output_index == 42 })
  }

  else(_) { False }
}
