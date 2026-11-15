use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator certificates_count {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.length(self.certificates) <= 3
  }

  else(_) { False }
}
