use cardano/transaction.{OutputReference, Transaction}
use aiken/interval

validator interval_control {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    interval.contains(self.validity_range, 1000)
  }

  else(_) { False }
}
