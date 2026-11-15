use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/assets

validator reference_inputs_find {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.reference_inputs, fn(input) { assets.lovelace_of(input.output.value) > 0 })
  }

  else(_) { False }
}
