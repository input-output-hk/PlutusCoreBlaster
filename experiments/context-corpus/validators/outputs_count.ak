use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator outputs_count {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.length(self.outputs) <= 8
  }

  else(_) { False }
}
