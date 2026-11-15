use cardano/transaction.{OutputReference, Transaction}

validator id_control {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    self.id == #"0000000000000000000000000000000000000000000000000000000000000000"
  }

  else(_) { False }
}
