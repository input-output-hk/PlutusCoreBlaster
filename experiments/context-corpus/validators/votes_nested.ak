use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator votes_nested {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.votes, fn(pair) { let Pair(_, votes) = pair list.length(votes) > 1 })
  }

  else(_) { False }
}
