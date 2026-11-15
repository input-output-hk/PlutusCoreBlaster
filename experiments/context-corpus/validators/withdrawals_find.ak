use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/address.{VerificationKey}

validator withdrawals_find {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.withdrawals, fn(pair) { let Pair(credential, amount) = pair credential == VerificationKey(#"11111111111111111111111111111111111111111111111111111111") && amount > 0 })
  }

  else(_) { False }
}
