use cardano/transaction.{OutputReference, Transaction}

validator donation_option {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    when self.treasury_donation is { Some(amount) -> amount > 0 None -> False }
  }

  else(_) { False }
}
