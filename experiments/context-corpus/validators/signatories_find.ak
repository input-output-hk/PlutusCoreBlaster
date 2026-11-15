use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator signatories_find {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.has(self.extra_signatories, #"11111111111111111111111111111111111111111111111111111111")
  }

  else(_) { False }
}
