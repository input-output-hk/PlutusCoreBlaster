use cardano/transaction.{OutputReference, Transaction}
use cardano/assets

validator mint_fold {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    assets.reduce(self.mint, 0, fn(_, _, quantity, acc) { acc + quantity }) != 0
  }

  else(_) { False }
}
