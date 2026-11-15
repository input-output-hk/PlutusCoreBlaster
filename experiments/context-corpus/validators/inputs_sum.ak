use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/assets

validator inputs_sum {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.foldl(self.inputs, 0, fn(input, acc) { acc + assets.lovelace_of(input.output.value) }) >= 3
  }

  else(_) { False }
}
