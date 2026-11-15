use cardano/transaction.{OutputReference, Transaction}

validator treasury_option {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    when self.current_treasury_amount is { Some(amount) -> amount >= 0 None -> True }
  }

  else(_) { False }
}
