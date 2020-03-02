module Steel.Semantics.Instantiate

module S = Steel.Semantics.Hoare.MST
open Steel.Memory
open Steel.Actions

let state0 (uses:Set.set lock_addr) : S.st0 =
  { S.mem = mem;
    S.core = core_mem;
    S.locks_preorder = mem_evolves;
    S.hprop = hprop;
    S.locks_invariant = locks_invariant uses;

    S.disjoint = disjoint;
    S.join = join;

    S.interp = interp;

    S.emp = emp;
    S.star = star;

    S.equals = equiv
  }

val state_obeys_st_laws (uses:Set.set lock_addr) : Lemma (S.st_laws (state0 uses))

let state : S.st = state_obeys_st_laws Set.empty; state0 Set.empty
