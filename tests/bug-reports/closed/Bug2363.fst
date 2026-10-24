module Bug2363

open FStar.Tactics.V2

// Resugaring may combine adjacent quantifiers only when they have the same kind.
// Issue #2363 incorrectly printed forall/forall/exists as a single forall.
let check (t:term) (expected:string) : Tac unit =
  let actual = term_to_string t in
  if actual <> expected then
    fail ("Expected: " ^ expected ^ "\nGot: " ^ actual)

let _ = assert True by begin
  // All eight combinations of three forall/exists quantifiers.
  check
    (`(forall (x1:int). forall (x2:int). forall (x3:int). x1 + x2 == x3))
    "forall (x1: int) (x2: int) (x3: int). x1 + x2 == x3";
  check
    (`(forall (x1:int). forall (x2:int). exists (x3:int). x1 + x2 == x3))
    "forall (x1: int) (x2: int). exists (x3: int). x1 + x2 == x3";
  check
    (`(forall (x1:int). exists (x2:int). forall (x3:int). x1 + x2 == x3))
    "forall (x1: int). exists (x2: int). forall (x3: int). x1 + x2 == x3";
  check
    (`(forall (x1:int). exists (x2:int). exists (x3:int). x1 + x2 == x3))
    "forall (x1: int). exists (x2: int) (x3: int). x1 + x2 == x3";
  check
    (`(exists (x1:int). forall (x2:int). forall (x3:int). x1 + x2 == x3))
    "exists (x1: int). forall (x2: int) (x3: int). x1 + x2 == x3";
  check
    (`(exists (x1:int). forall (x2:int). exists (x3:int). x1 + x2 == x3))
    "exists (x1: int). forall (x2: int). exists (x3: int). x1 + x2 == x3";
  check
    (`(exists (x1:int). exists (x2:int). forall (x3:int). x1 + x2 == x3))
    "exists (x1: int) (x2: int). forall (x3: int). x1 + x2 == x3";
  check
    (`(exists (x1:int). exists (x2:int). exists (x3:int). x1 + x2 == x3))
    "exists (x1: int) (x2: int) (x3: int). x1 + x2 == x3";
  trivial ()
end
