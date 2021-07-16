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

val int_or_bool: Type0

/// PCM for node:

val int_or_bool_pcm: pcm int_or_bool

/// (mk_int i) represents (union int_or_bool){.i = i}
/// (mk_bool b) represents (union int_or_bool){.b = b}

let nonunit (p: pcm 'a) = x:'a{~ (x == one p)}

val mk_int (i: Ghost.erased (nonunit (pod_pcm int))): Ghost.erased int_or_bool
val mk_bool (b: Ghost.erased (nonunit (pod_pcm bool))): Ghost.erased int_or_bool

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

val case_of_int_or_bool_int (i: Ghost.erased (nonunit (pod_pcm int)))
: Lemma (case_of_int_or_bool (mk_int i) == Some I) [SMTPat (mk_int i)]

val case_of_int_or_bool_bool (b: Ghost.erased (nonunit (pod_pcm bool)))
: Lemma (case_of_int_or_bool (mk_bool b) == Some B) [SMTPat (mk_bool b)]

val case_of_int_or_bool_one
: squash (case_of_int_or_bool (one int_or_bool_pcm) == None)

val mk_int_exclusive (i: Ghost.erased (nonunit (pod_pcm int)))
: Lemma (requires exclusive (pod_pcm int) i) (ensures exclusive int_or_bool_pcm (mk_int i))
  [SMTPat (exclusive (pod_pcm int) i)]

val mk_bool_exclusive (b: Ghost.erased (nonunit (pod_pcm bool)))
: Lemma (requires exclusive (pod_pcm bool) b) (ensures exclusive int_or_bool_pcm (mk_bool b))
  [SMTPat (exclusive (pod_pcm bool) b)]

/// Taking pointers to the i and b cases of an int_or_bool

val addr_of_i (#i: Ghost.erased (nonunit (pod_pcm int))) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm int){q == ref_focus p _i})
    (p `pts_to` mk_int i)
    (fun q -> q `pts_to` Ghost.reveal i)

val unaddr_of_i (#i: Ghost.erased (nonunit (pod_pcm int))) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus p _i})
: A.SteelGhostT unit opened (q `pts_to` Ghost.reveal i) (fun _ -> p `pts_to` mk_int i)

val addr_of_b (#b: Ghost.erased (nonunit (pod_pcm bool))) (p: ref 'a int_or_bool_pcm)
: SteelT (q:ref 'a (pod_pcm bool){q == ref_focus p _b})
    (p `pts_to` mk_bool b)
    (fun q -> q `pts_to` Ghost.reveal b)

val unaddr_of_b (#b: Ghost.erased (nonunit (pod_pcm bool))) (#opened: M.inames)
  (p: ref 'a int_or_bool_pcm)
  (q: ref 'a (pod_pcm bool){q == ref_focus p _b})
: A.SteelGhostT unit opened (q `pts_to` Ghost.reveal b) (fun _ -> p `pts_to` mk_bool b)

/// Switching the case

val switch_to_int (#u: Ghost.erased int_or_bool)
  (p: ref 'a int_or_bool_pcm) (i: int)
: Steel unit
    (p `pts_to` u)
    (fun _ -> p `pts_to` mk_int (Ghost.hide (Ghost.reveal (some i))))
    (requires fun _ -> Some? (case_of_int_or_bool u) /\ exclusive int_or_bool_pcm u)
    (ensures fun _ _ _ -> True)

val switch_to_bool (#u: Ghost.erased int_or_bool)
  (p: ref 'a int_or_bool_pcm) (b: bool)
: Steel unit
    (p `pts_to` u)
    (fun _ -> p `pts_to` mk_bool (Ghost.hide (Ghost.reveal (some b))))
    (requires fun _ -> Some? (case_of_int_or_bool u) /\ exclusive int_or_bool_pcm u)
    (ensures fun _ _ _ -> True)
