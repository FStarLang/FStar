module IntOrBool

open FStar.PCM
open FStar.PCM.POD
open Steel.C.PCM
open Steel.C.Ref
open Steel.C.Connection
open Steel.Effect
module M = Steel.Memory
module A = Steel.Effect.Atomic

/// union int_or_bool { int i; bool b; };
///
/// PCM for int_or_bool:

type int_or_bool_case = | I | B

val int_or_bool: Type0

/// PCM for node:

val int_or_bool_pcm: pcm int_or_bool

/// (mk_int i) represents (union int_or_bool){.i = i}
/// (mk_bool b) represents (union int_or_bool){.b = b}

val mk_int (i: Ghost.erased (pod int)): Ghost.erased int_or_bool
val mk_bool (b: Ghost.erased (pod bool)): Ghost.erased int_or_bool

/// Connections for cases

val _i : int_or_bool_pcm `connection` pod_pcm int
val _b : int_or_bool_pcm `connection` pod_pcm bool

/// Getting the case of a union in GTot

val case_of_int_or_bool (u: Ghost.erased int_or_bool):
  GTot (k:option int_or_bool_case{
    match k with
    | Some I -> exists i. u == mk_int i
    | Some B -> exists b. u == mk_bool b
    | None -> Ghost.reveal u == one int_or_bool_pcm
  })

val case_of_int_or_bool_int (i: Ghost.erased (pod int))
: Lemma
    (requires ~ (i == none))
    (ensures case_of_int_or_bool (mk_int i) == Some I) [SMTPat (mk_int i)]

val case_of_int_or_bool_bool (b: Ghost.erased (pod bool))
: Lemma
    (requires ~ (b == none))
    (ensures case_of_int_or_bool (mk_bool b) == Some B) [SMTPat (mk_bool b)]

val case_of_int_or_bool_one
: squash (case_of_int_or_bool (one int_or_bool_pcm) == None)

val mk_int_exclusive (i: Ghost.erased (pod int))
: Lemma
    (requires exclusive (pod_pcm int) i /\ ~ (i == none))
    (ensures exclusive int_or_bool_pcm (mk_int i))
  [SMTPat (exclusive (pod_pcm int) i)]

val mk_bool_exclusive (b: Ghost.erased (pod bool))
: Lemma
    (requires exclusive (pod_pcm bool) b /\ ~ (b == none))
    (ensures exclusive int_or_bool_pcm (mk_bool b))
  [SMTPat (exclusive (pod_pcm bool) b)]

/// Taking pointers to the i and b cases of an int_or_bool

val addr_of_i (#i: Ghost.erased (pod int)) (p: ref 'a int_or_bool_pcm)
: Steel (q:ref 'a (pod_pcm int){q == ref_focus p _i})
    (p `pts_to` mk_int i)
    (fun q -> q `pts_to` i)
    (requires fun _ -> ~ (i == none))
    (ensures fun _ _ _ -> True)

val unaddr_of_i (#i: Ghost.erased (pod int)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus p _i})
: A.SteelGhost unit opened
    (q `pts_to` i)
    (fun _ -> p `pts_to` mk_int i)
    (requires fun _ -> ~ (i == none))
    (ensures fun _ _ _ -> True)

val addr_of_b (#b: Ghost.erased (pod bool)) (p: ref 'a int_or_bool_pcm)
: Steel (q:ref 'a (pod_pcm bool){q == ref_focus p _b})
    (p `pts_to` mk_bool b)
    (fun q -> q `pts_to` b)
    (requires fun _ -> ~ (b == none))
    (ensures fun _ _ _ -> True)

val unaddr_of_b (#b: Ghost.erased (pod bool)) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm bool){q == ref_focus p _b})
: A.SteelGhost unit opened
    (q `pts_to` b)
    (fun _ -> p `pts_to` mk_bool b)
    (requires fun _ -> ~ (b == none))
    (ensures fun _ _ _ -> True)

/// Switching the case

val switch_to_int (#u: Ghost.erased int_or_bool)
  (p: ref 'a int_or_bool_pcm) (i: int)
: Steel unit
    (p `pts_to` u)
    (fun _ -> p `pts_to` mk_int (some (Ghost.hide i)))
    (requires fun _ -> exclusive int_or_bool_pcm u)
    (ensures fun _ _ _ -> True)

val switch_to_bool (#u: Ghost.erased int_or_bool)
  (p: ref 'a int_or_bool_pcm) (b: bool)
: Steel unit
    (p `pts_to` u)
    (fun _ -> p `pts_to` mk_bool (some (Ghost.hide b)))
    (requires fun _ -> exclusive int_or_bool_pcm u)
    (ensures fun _ _ _ -> True)
