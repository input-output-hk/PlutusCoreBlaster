import PlutusCore.UPLC.Term

/-!
# Symbolic inputs for `#prep_uplc` benchmarks

Input conversion functions that apply a script to free `Data` or `Integer` arguments, so that
`#prep_uplc` has to optimize the script for every possible argument.
-/

namespace Benchmark.PrepUplc.Inputs

open PlutusCore.UPLC.Term (Term)
open PlutusCore.Data (Data)
open PlutusCore.Integer (Integer)

/-- One free `Data` argument, e.g. the script context of a PlutusV3 validator. -/
def dataArgs1 (a : Data) : List Term := [.Const (.Data a)]

/-- Two free `Data` arguments, e.g. the redeemer and script context of a PlutusV1/V2 minting
    policy, or a parameter and the script context of a parameterized PlutusV3 validator. -/
def dataArgs2 (a b : Data) : List Term := [.Const (.Data a), .Const (.Data b)]

/-- Three free `Data` arguments, e.g. the datum, redeemer and script context of a PlutusV1/V2
    spending validator. -/
def dataArgs3 (a b c : Data) : List Term := [.Const (.Data a), .Const (.Data b), .Const (.Data c)]

/-- One free `Integer` argument, e.g. the `n` of a function computing on integers. -/
def integerArgs1 (x : Integer) : List Term := [.Const (.Integer x)]

end Benchmark.PrepUplc.Inputs
