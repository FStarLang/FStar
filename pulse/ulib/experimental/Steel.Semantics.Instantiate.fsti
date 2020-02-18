module Steel.Semantics.Instantiate

module S = Steel.Semantics.Hoare.MST
open Steel.Memory
open Steel.Actions

type state0 : S.st0 =
  { S.mem = mem;
    S.core = core_mem;
    S.locks_preorder = mem_evolves;
    S.hprop = hprop;
    S.locks_invariant = locks_invariant;

    S.disjoint = disjoint_mem;
    S.join = join_mem;

    S.interp = interp_mem;

    S.emp = emp;
    S.star = star;

    S.equals = equiv
  }

val state_obeys_st_laws (_:unit) : Lemma (S.st_laws state0)

let state : S.st = state_obeys_st_laws (); state0
