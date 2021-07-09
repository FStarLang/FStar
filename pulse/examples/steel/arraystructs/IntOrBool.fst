module IntOrBool

open AggregateRef
open FStar.PCM
open FStar.PCM.Extras
open FStar.PCM.POD
open Steel.Effect
module M = Steel.Memory
module A = Steel.Effect.Atomic

type int_or_bool_case = | I | B
let int_or_bool_cases k = match k with
  | I -> pod int
  | B -> pod bool
let int_or_bool = union int_or_bool_cases

let int_or_bool_cases_pcm k : refined_one_pcm (int_or_bool_cases k) = match k with
  | I -> pod_pcm int
  | B -> pod_pcm bool
let int_or_bool_pcm = union_pcm int_or_bool_cases_pcm

let mk_int i = Some (|I, Ghost.reveal i|)
let mk_bool b = Some (|B, Ghost.reveal b|)

let re_i = case_refinement int_or_bool_cases_pcm I
let re_b = case_refinement int_or_bool_cases_pcm B

/// Lenses for cases

let _i = case int_or_bool_cases_pcm I
let _b = case int_or_bool_cases_pcm B

/// Taking pointers to the i and b cases of an int_or_bool

let addr_of_i (#i: Ghost.erased (pod int)) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm int){q == ref_focus (ref_refine p re_i) _i})
    (p `pts_to` mk_int i)
    (fun q -> q `pts_to` i)
= let mk_int_i : Ghost.erased (refine_t (refinement_f re_i)) = Some (|I, Ghost.reveal i|) in
  A.change_equal_slprop (p `pts_to` mk_int i) (p `pts_to` Ghost.reveal mk_int_i);
  addr_of_union_lens p _i (Ghost.reveal mk_int_i)

let unaddr_of_i (#i: Ghost.erased (pod int)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus (ref_refine p re_i) _i})
: A.SteelGhostT unit opened (q `pts_to` i) (fun _ -> p `pts_to` mk_int i)
= unaddr_of_union_lens q p _i i

let addr_of_b (#b: Ghost.erased (pod bool)) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm bool){q == ref_focus (ref_refine p re_b) _b})
    (p `pts_to` mk_bool b)
    (fun q -> q `pts_to` b)
= let mk_bool_b : Ghost.erased (refine_t (refinement_f re_b)) = Some (|B, Ghost.reveal b|) in
  A.change_equal_slprop (p `pts_to` mk_bool b) (p `pts_to` Ghost.reveal mk_bool_b);
  addr_of_union_lens p _b (Ghost.reveal mk_bool_b)

let unaddr_of_b (#b: Ghost.erased (pod bool)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm bool){q == ref_focus (ref_refine p re_b) _b})
: A.SteelGhostT unit opened (q `pts_to` b) (fun _ -> p `pts_to` mk_bool b)
= unaddr_of_union_lens q p _b b
