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

[@@erasable]
noeq type tag = | I' | B'

val int_or_bool : Type0

/// PCM for int_or_bool:

val int_or_bool_pcm : refined_one_pcm int_or_bool

/// (mk_int i) represents (union int_or_bool){.i = i}
/// (mk_bool b) represents (union int_or_bool){.b = b}

let int_or_bool_cases k : Type = match k with
  | I' -> pod int
  | B' -> pod bool

val mk: tag -> Ghost.erased (int_or_bool_cases tag) -> Ghost.erased int_or_bool

//val mk_int (i: Ghost.erased (pod int)): Ghost.erased int_or_bool
//val mk_bool (i: Ghost.erased (pod bool)): Ghost.erased int_or_bool

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

/// Laws (compare with FStar.PCM.POD.fsti)

val case: Ghost.erased int_or_bool -> GTot (option tag)
val case_ok1: u:Ghost.erased int_or_bool -> t:tag -> x:typeof_pcm t ->
  Lemma (case (mk t i) == Some t) [SMTPat (case (mk t i))]
val case_ok2: u -> Lemma (case u == None <==> u = one _) [SMTPat (case u)]
val case_ok3: u: _ ->
  Lemma
    (requires Some? (case u))
    (ensures exists i. u == mk (Some?.v (case u)) i) [SMTPat (case u)]

// let is_int_int (i:Ghost.erased (pod int)): Lemma (is_int (mk_int i)) = ()
// let is_bool_bool (b:Ghost.erased (pod bool)): Lemma (is_bool (mk_bool b)) = ()
// 
// let int_not_bool (u: Ghost.erased int_or_bool)
// : Lemma (requires is_int u) (ensures ~ (is_bool u)) 
// = ()
// 
// let bool_not_int (u: Ghost.erased int_or_bool)
// : Lemma (requires is_bool u) (ensures ~ (is_int u)) 
// = ()
// 
// val int_compatible (v w: Ghost.erased int_or_bool)
// : Lemma (requires compatible int_or_bool_pcm v w /\ is_int v) (ensures is_int w)
//   [SMTPat (compatible int_or_bool_pcm v w); SMTPat (is_int v)]
// 
// val bool_compatible (v w: Ghost.erased int_or_bool)
// : Lemma (requires compatible int_or_bool_pcm v w /\ is_bool v) (ensures is_bool w)
//   [SMTPat (compatible int_or_bool_pcm v w); SMTPat (is_bool v)]
//   
// val int_valid_write (v w: Ghost.erased (pod int))
// : Lemma
//     (requires AggregateRef.valid_write (pod_pcm int) v w)
//     (ensures AggregateRef.valid_write int_or_bool_pcm (mk_int v) (mk_int w))
//   [SMTPat (AggregateRef.valid_write (pod_pcm int) v w)]
// 
// v, w whole
// I != J
// valid_write (mk I v) (mk J w) 
