module IntOrBool

open AggregateRef
open FStar.PCM
open FStar.PCM.Extras
open FStar.PCM.POD
open Steel.Effect
module M = Steel.Memory
module A = Steel.Effect.Atomic

/// union int_or_bool { int i; bool b; };
///
/// Carrier of PCM for int_or_bool:

type int_or_bool_case = | I | B

let int_or_bool_cases k = match k with
  | I -> pod int
  | B -> pod bool
let int_or_bool = union int_or_bool_cases

/// PCM for int_or_bool:

let int_or_bool_cases_pcm k: refined_one_pcm (int_or_bool_cases k) = match k with
  | I -> pod_pcm int
  | B -> pod_pcm bool
  
let int_or_bool_pcm: refined_one_pcm int_or_bool = union_pcm int_or_bool_cases_pcm

/// (mk_int i) represents (union int_or_bool){.i = i}
/// (mk_bool b) represents (union int_or_bool){.b = b}

//val mk: tag -> Ghost.erased (int_or_bool_cases tag) -> Ghost.erased int_or_bool

val mk_int (i: Ghost.erased (pod int)): Ghost.erased int_or_bool
val mk_bool (i: Ghost.erased (pod bool)): Ghost.erased int_or_bool

/// Refinements for cases

val re_i : pcm_refinement int_or_bool_pcm
val re_b : pcm_refinement int_or_bool_pcm

/// Lenses for cases

val _i : pcm_lens (refined_pcm re_i) (pod_pcm int)
val _b : pcm_lens (refined_pcm re_b) (pod_pcm bool)

/// Taking pointers to the i and b cases of an int_or_bool

//val addr_of_i (#i: Ghost.erased (pod int){case u == I}) (p: ref 'a int_or_bool_pcm)
//: SteelT (q:ref 'a (pod_pcm int){q == ref_focus (ref_refine p re_i) _i})
//    (p `pts_to` u)
//    (fun q -> q `pts_to` proj2 u)

val addr_of_i (#i: Ghost.erased (pod int)) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm int){q == ref_focus (ref_refine p re_i) _i})
    (p `pts_to` mk_int i)
    (fun q -> q `pts_to` i)

val unaddr_of_i (#i: Ghost.erased (pod int)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus (ref_refine p re_i) _i})
: A.SteelGhostT unit opened (q `pts_to` i) (fun _ -> p `pts_to` mk_int i)

val addr_of_b (#b: Ghost.erased (pod bool)) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm bool){q == ref_focus (ref_refine p re_b) _b})
    (p `pts_to` mk_bool b)
    (fun q -> q `pts_to` b)

val unaddr_of_b (#b: Ghost.erased (pod bool)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm bool){q == ref_focus (ref_refine p re_b) _b})
: A.SteelGhostT unit opened (q `pts_to` b) (fun _ -> p `pts_to` mk_bool b)

/// Switching the case

val switch_to_bool (#i: Ghost.erased int)
  (p: ref 'a int_or_bool_pcm) (b: bool)
: SteelT unit (p `pts_to` mk_int (some i)) (fun _ -> p `pts_to` mk_bool (some b))

val switch_to_int (#b: Ghost.erased bool)
  (p: ref 'a int_or_bool_pcm) (i: int)
: SteelT unit (p `pts_to` mk_bool (some b)) (fun _ -> p `pts_to` mk_int (some i))
