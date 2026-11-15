use cardano/transaction.{OutputReference, Transaction}
use aiken/collection/list

validator proposals_deposit {
  spend(_datum: Option<Data>, _redeemer: Data, _own_ref: OutputReference, self: Transaction) {
    list.foldl(self.proposal_procedures, 0, fn(proposal, acc) { acc + proposal.deposit }) > 0
  }

  else(_) { False }
}
