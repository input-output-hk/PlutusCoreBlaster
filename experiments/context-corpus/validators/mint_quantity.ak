use cardano/transaction.{OutputReference, Transaction}
use cardano/assets

validator mint_quantity {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    assets.quantity_of(self.mint, #"33333333333333333333333333333333333333333333333333333333", #"61") == 1
  }

  else(_) { False }
}
