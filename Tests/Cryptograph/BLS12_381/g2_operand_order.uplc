(program 1.1.0
  (lam a (lam b
    [ [ (builtin bls12_381_G2_equal) [ [ (builtin bls12_381_G2_add) a ] b ] ] a ])))
