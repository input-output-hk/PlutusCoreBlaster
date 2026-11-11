-- saturate x = go x 0, where go n count = if n <= 0 then count else go (n - 1) (count + 2 * n),
-- so saturate x = x * (x + 1) for x >= 0.
-- Ported from the hand-written `saturate` program of Lean-blaster's
-- Tests/Smt/Benchmarks/UPLC/Examples/Integer/Saturate.lean (commit 49a4886).
(program 1.1.0
  [ (lam go (lam x [ [ go x ] (con integer 0) ]))
    [ (lam s [ s s ])
      (lam s (lam n (lam count
        (force (force
          [ [ [ (force (builtin ifThenElse))
                [ [ (builtin lessThanEqualsInteger) n ] (con integer 0) ] ]
              (delay (delay count)) ]
            (delay (delay
              [ [ (lam x [ [ s s ] x ]) [ [ (builtin subtractInteger) n ] (con integer 1) ] ]
                [ [ (builtin addInteger) count ] [ [ (builtin multiplyInteger) (con integer 2) ] n ] ] ])) ])))))
    ]
  ]
)
