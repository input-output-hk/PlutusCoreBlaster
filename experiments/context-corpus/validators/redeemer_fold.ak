use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator redeemer_fold {
  spend(_datum: Option<Data>, redeemer: Data, _own_ref: OutputReference, _self: Transaction) {
    expect xs: List<Int> = redeemer
    list.foldl(xs, 0, fn(value, acc) { acc + value }) >= 0
  }

  else(_) { False }
}
