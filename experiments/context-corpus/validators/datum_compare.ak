use cardano/transaction.{OutputReference, Transaction}

validator datum_compare {
  spend(datum: Option<Data>, redeemer: Data, _own_ref: OutputReference, _self: Transaction) {
    when datum is { Some(d) -> d == redeemer None -> False }
  }

  else(_) { False }
}
