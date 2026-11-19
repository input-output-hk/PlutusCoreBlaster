(program 1.1.0
  (lam a (lam b
    [ [ (builtin bls12_381_G1_equal) [ [ (builtin bls12_381_G1_add) a ] b ] ] a ])))
