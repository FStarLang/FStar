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

val int_or_bool: Type

/// PCM for node:

val int_or_bool_pcm: pcm int_or_bool

/// (mk_int i) represents (union int_or_bool){.i = i}
/// (mk_bool b) represents (union int_or_bool){.b = b}

val mk_int (i: Ghost.erased (pod int)): Ghost.erased int_or_bool
val mk_bool (i: Ghost.erased (pod bool)): Ghost.erased int_or_bool

/// Connections for cases

val _i : int_or_bool_pcm `connection` pod_pcm int
val _b : int_or_bool_pcm `connection` pod_pcm bool

/// Getting the case of a union in GTot

// Construct using strong LEM
val case_of_int_or_bool (u: Ghost.erased int_or_bool): GTot (option int_or_bool_case)

val case_of_int_or_bool_int (i: Ghost.erased (pod int))
: Lemma (case_of_int_or_bool (mk_int i) == Some I) [SMTPat (mk_int i)]

val case_of_int_or_bool_bool (b: Ghost.erased (pod bool))
: Lemma (case_of_int_or_bool (mk_bool b) == Some B) [SMTPat (mk_bool b)]

val case_of_int_or_bool_one
: squash (case_of_int_or_bool (one int_or_bool_pcm) == None)

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

val switch_to_int (#u: Ghost.erased int_or_bool)
  (p: ref 'a int_or_bool_pcm) (i: int)
: Steel unit
    (p `pts_to` u)
    (fun _ -> p `pts_to` mk_int (some i))
    (requires fun _ -> Some? (case_of_int_or_bool u))
    (requires fun _ _ _ -> True)

val switch_to_bool (#u: Ghost.erased int_or_bool)
  (p: ref 'a int_or_bool_pcm) (b: bool)
: Steel unit
    (p `pts_to` u)
    (fun _ -> p `pts_to` mk_bool (some b))
    (requires fun _ -> Some? (case_of_int_or_bool u))
    (requires fun _ _ _ -> True)
