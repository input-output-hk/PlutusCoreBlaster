use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator withdrawals_sum {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.foldl(self.withdrawals, 0, fn(pair, acc) { let Pair(_, amount) = pair acc + amount }) > 0
  }

  else(_) { False }
}
