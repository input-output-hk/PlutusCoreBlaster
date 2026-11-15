use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator proposals_count {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.length(self.proposal_procedures) > 0
  }

  else(_) { False }
}
