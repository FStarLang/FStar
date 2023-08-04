module FStar.Stubs.TypeChecker.Core

type tot_or_ghost = 
  | E_Total
  | E_Ghost


type unfold_side =
  | Left
  | Right
  | Both
  | Neither
