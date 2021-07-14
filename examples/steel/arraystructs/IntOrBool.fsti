module IntOrBool

open FStar.PCM
open FStar.PCM.POD
open Steel.C.PCM
open Steel.Effect
module M = Steel.Memory
module A = Steel.Effect.Atomic

/// union int_or_bool { int i; bool b; };
///
/// PCM for int_or_bool:

type int_or_bool_case = | I | B

let int_or_bool_cases k = match k with
  | I -> pod int
  | B -> pod bool
  
let int_or_bool_cases_pcm k: pcm (int_or_bool_cases k) = match k with
  | I -> pod_pcm int
  | B -> pod_pcm bool
let int_or_bool = union int_or_bool_cases_pcm
let int_or_bool_pcm: pcm int_or_bool = union_pcm int_or_bool_cases_pcm

/// (mk_int i) represents (union int_or_bool){.i = i}
/// (mk_bool b) represents (union int_or_bool){.b = b}

val mk_int (i: Ghost.erased (pod int)): Ghost.erased int_or_bool
val mk_bool (i: Ghost.erased (pod bool)): Ghost.erased int_or_bool

/// Connections for cases

val _i : connection int_or_bool_pcm (pod_pcm int)
val _b : connection int_or_bool_pcm (pod_pcm bool)

// Construct using strong_excluded_middle
//val case_of : int_or_bool -> GTot (option int_or_bool_case)

/// Taking pointers to the i and b cases of an int_or_bool

val addr_of_i (#i: Ghost.erased (pod int)) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm int){q == ref_focus p _i})
    (p `pts_to` mk_int i)
    (fun q -> q `pts_to` i)

val unaddr_of_i (#i: Ghost.erased (pod int)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus p _i})
: A.SteelGhostT unit opened (q `pts_to` i) (fun _ -> p `pts_to` mk_int i)

val addr_of_b (#b: Ghost.erased (pod bool)) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm bool){q == ref_focus p _b})
    (p `pts_to` mk_bool b)
    (fun q -> q `pts_to` b)

val unaddr_of_b (#b: Ghost.erased (pod bool)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm bool){q == ref_focus p _b})
: A.SteelGhostT unit opened (q `pts_to` b) (fun _ -> p `pts_to` mk_bool b)

/// Switching the case

val switch_to_bool (#i: Ghost.erased int)
  (p: ref 'a int_or_bool_pcm) (b: bool)
: SteelT unit (p `pts_to` mk_int (some i)) (fun _ -> p `pts_to` mk_bool (some b))

val switch_to_int (#b: Ghost.erased bool)
  (p: ref 'a int_or_bool_pcm) (i: int)
: SteelT unit (p `pts_to` mk_bool (some b)) (fun _ -> p `pts_to` mk_int (some i))

/// Laws about unions

//compatible p (mk_int i) v
//==> exists j. v = mk_int j
