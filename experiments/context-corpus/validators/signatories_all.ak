use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use aiken/primitive/bytearray

validator signatories_all {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.all(self.extra_signatories, fn(signer) { bytearray.length(signer) == 28 })
  }

  else(_) { False }
}
