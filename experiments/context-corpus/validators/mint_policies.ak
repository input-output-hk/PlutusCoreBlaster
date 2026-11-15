use cardano/transaction.{OutputReference, Transaction}
use cardano/assets
use aiken/collection/list

validator mint_policies {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.length(assets.policies(self.mint)) <= 4
  }

  else(_) { False }
}
