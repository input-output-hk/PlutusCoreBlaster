use aiken/collection/list
use aiken/primitive/bytearray
use aiken/crypto.{VerificationKeyHash}
use cardano/transaction.{OutputReference, Transaction}

const beneficiary: VerificationKeyHash =
  #"11111111111111111111111111111111111111111111111111111111"

// Deliberately force validation of every key and reconstruct the list.
// This is a diagnostic control, not a claim about Aiken's default decoder.
fn validate_all(signers: List<VerificationKeyHash>) -> List<VerificationKeyHash> {
  when signers is {
    [] -> []
    [signer, ..rest] -> {
      expect bytearray.length(signer) == 28
      [signer, ..validate_all(rest)]
    }
  }
}

validator eager_beneficiary_signed {
  spend(
    _datum: Option<Data>,
    _redeemer: Data,
    _own_ref: OutputReference,
    tx: Transaction,
  ) {
    list.has(validate_all(tx.extra_signatories), beneficiary)
  }

  else(_) {
    False
  }
}
