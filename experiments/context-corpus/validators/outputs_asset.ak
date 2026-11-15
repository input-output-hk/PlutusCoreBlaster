use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/assets

validator outputs_asset {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.outputs, fn(output) { assets.quantity_of(output.value, #"33333333333333333333333333333333333333333333333333333333", #"61") == 1 })
  }

  else(_) { False }
}
