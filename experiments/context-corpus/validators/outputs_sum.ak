use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/assets

validator outputs_sum {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.foldl(self.outputs, 0, fn(output, acc) { acc + assets.lovelace_of(output.value) }) >= 3
  }

  else(_) { False }
}
