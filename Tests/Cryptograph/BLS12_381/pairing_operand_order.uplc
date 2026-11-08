(program 1.1.0
  (lam a (lam b (lam c (lam d
    [ [ (builtin bls12_381_finalVerify)
        [ [ (builtin bls12_381_mulMlResult) [ [ (builtin bls12_381_millerLoop) a ] b ] ]
          [ [ (builtin bls12_381_millerLoop) c ] d ] ] ]
      [ [ (builtin bls12_381_millerLoop) a ] b ] ])))))
