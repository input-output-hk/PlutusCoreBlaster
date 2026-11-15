use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list
use aiken/collection/dict
use cardano/transaction.{DatumHash, InlineDatum, NoDatum}

validator outputs_inline_datum {
  spend(_datum: Option<Data>, redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.any(self.outputs, fn(output) { when output.datum is { InlineDatum(d) -> d == redeemer DatumHash(h) -> dict.get(self.datums, h) == Some(redeemer) NoDatum -> False } })
  }

  else(_) { False }
}
