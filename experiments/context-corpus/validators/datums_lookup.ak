use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/dict

validator datums_lookup {
  spend(_datum: Option<Data>, redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    dict.get(self.datums, #"2222222222222222222222222222222222222222222222222222222222222222") == Some(redeemer)
  }

  else(_) { False }
}
