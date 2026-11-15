use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator outputs_reference_script {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.outputs, fn(output) { output.reference_script == Some(#"33333333333333333333333333333333333333333333333333333333") })
  }

  else(_) { False }
}
