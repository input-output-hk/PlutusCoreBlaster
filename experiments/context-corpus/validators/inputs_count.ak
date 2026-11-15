use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator inputs_count {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.length(self.inputs) <= 4
  }

  else(_) { False }
}
