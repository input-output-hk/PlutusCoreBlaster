use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use cardano/assets

validator value_conservation {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    let incoming = list.foldl(self.inputs, 0, fn(input, acc) { acc + assets.lovelace_of(input.output.value) })
    let outgoing = list.foldl(self.outputs, 0, fn(output, acc) { acc + assets.lovelace_of(output.value) })
    incoming == outgoing + self.fee
  }

  else(_) { False }
}
