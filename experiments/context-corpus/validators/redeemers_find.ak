use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator redeemers_find {
  spend(_datum: Option<Data>, redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.redeemers, fn(pair) { let Pair(_, value) = pair value == redeemer })
  }

  else(_) { False }
}
