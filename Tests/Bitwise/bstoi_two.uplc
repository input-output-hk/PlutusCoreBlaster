(program 1.1.0
  (lam a (lam b
    [ [ (builtin equalsInteger)
        [ [ (builtin byteStringToInteger) (con bool True) ] a ] ]
      [ [ (builtin byteStringToInteger) (con bool True) ] b ] ])))
