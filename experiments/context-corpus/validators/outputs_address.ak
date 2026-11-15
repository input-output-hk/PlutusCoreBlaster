use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/address.{VerificationKey}

validator outputs_address {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.outputs, fn(output) { output.address.payment_credential == VerificationKey(#"11111111111111111111111111111111111111111111111111111111") })
  }

  else(_) { False }
}
