use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator votes_count {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.length(self.votes) > 0
  }

  else(_) { False }
}
