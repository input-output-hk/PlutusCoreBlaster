use cardano/transaction.{OutputReference, Transaction}

validator fee_control {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    self.fee <= 2000000
  }

  else(_) { False }
}
