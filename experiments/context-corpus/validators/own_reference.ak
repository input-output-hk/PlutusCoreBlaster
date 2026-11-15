use cardano/transaction.{OutputReference, Transaction}

validator own_reference {
  spend(_datum: Option<Data>, _redeemer: Data, own_ref: OutputReference, _self: Transaction) {
    own_ref.output_index == 0
  }

  else(_) { False }
}
