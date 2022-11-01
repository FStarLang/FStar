module Steel.TypeDictionary

module FP = FStar.Preorder
module R = Steel.GhostMonotonicHigherReference

let n_up_to (size: nat) : Type0 = (n: nat { n < size })

[@@erasable]
noeq
type dictionary = {
  size: nat;
  type_of_nat: (n_up_to size -> Type0);
  type_of_nat_inj: squash (forall n1 n2 . type_of_nat n1 == type_of_nat n2 ==> n1 == n2);
}

let nat_of_type
  (d: dictionary)
  (t: Type0)
: Ghost nat
  (requires (exists n . d.type_of_nat n == t))
  (ensures (fun _ -> True))
= FStar.IndefiniteDescription.indefinite_description_ghost _ (fun (n: n_up_to d.size) -> d.type_of_nat n == t)

let nat_of_type_of_nat
  (d: dictionary)
  (n: n_up_to d.size)
: Lemma
  (nat_of_type d (d.type_of_nat n) == n)
= ()

let type_of_nat_of_type
  (d: dictionary)
  (t: Type0)
: Lemma
  (requires (exists n . d.type_of_nat n == t))
  (ensures (d.type_of_nat (nat_of_type d t) == t))
= ()

let preorder : FP.preorder dictionary =
  (fun d1 d2 ->
    d1.size <= d2.size /\
    (forall (n: n_up_to d1.size) . d1.type_of_nat n == d2.type_of_nat n)
  )

open Steel.Effect.Common
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission

module S = Steel.Effect.Common

let dict_and_inv_f (opened: _) : SteelGhostT
  (Ghost.erased (dict: R.ref dictionary preorder & S.inv (h_exists (R.pts_to dict full_perm))))
  opened emp (fun _ -> emp)
=
  let d = ({ size = 0; type_of_nat = (fun _ -> unit); type_of_nat_inj = () }) in
  let dict = R.alloc preorder d in
  intro_exists _ (R.pts_to dict full_perm);
  let i = new_invariant (h_exists (R.pts_to dict full_perm)) in
  Ghost.hide (| dict, i |)

// let dict_and_inv = dict_and_inv_f _
assume val dict_and_inv : Ghost.erased (dict: R.ref dictionary preorder & S.inv (h_exists (R.pts_to dict full_perm)))

let dict : R.ref dictionary preorder = dfst dict_and_inv
let inv : S.inv (h_exists (R.pts_to dict full_perm)) = dsnd dict_and_inv

let token_has_type_in (n: nat) (t: Type0) (d: dictionary) : GTot prop =
  n < d.size /\
  d.type_of_nat n == t

let token_has_type (n: nat) (t: Type0) : GTot prop =
  R.witnessed dict (token_has_type_in n t)

let token_has_some_type (n: nat) : GTot prop =
  exists (t: Type0) . token_has_type n t

let token : Type0 = (n: Ghost.erased nat { token_has_some_type n })

let type_of_token
  (n: token)
: Tot Type0
= FStar.IndefiniteDescription.indefinite_description_ghost Type0 (fun t -> token_has_type n t)

let token_has_type_inj_type_with (#opened: _) (n: nat) (t1 t2: Type0) : SteelGhostT unit opened
  (h_exists (R.pts_to dict full_perm) `star` pure (token_has_type n t1 /\ token_has_type n t2))
  (fun _ -> h_exists (R.pts_to dict full_perm) `star` pure (t1 == t2))
= elim_pure _;
  let gd : Ghost.erased dictionary = witness_exists () in
  let d : dictionary = Ghost.reveal gd in
  rewrite_slprop (R.pts_to dict full_perm _) (R.pts_to dict full_perm d) (fun _ -> ());
  R.recall (token_has_type_in n t1) dict d;
  R.recall (token_has_type_in n t2) dict d;
  intro_exists d (R.pts_to dict full_perm);
  intro_pure _

let token_has_type_inj_token_with (#opened: _) (n1 n2: nat) (t: Type0) : SteelGhostT unit opened
  (h_exists (R.pts_to dict full_perm) `star` pure (token_has_type n1 t /\ token_has_type n2 t))
  (fun _ -> h_exists (R.pts_to dict full_perm) `star` pure (n1 == n2))
= elim_pure _;
  let gd : Ghost.erased dictionary = witness_exists () in
  let d : dictionary = Ghost.reveal gd in
  rewrite_slprop (R.pts_to dict full_perm _) (R.pts_to dict full_perm d) (fun _ -> ());
  R.recall (token_has_type_in n1 t) dict d;
  R.recall (token_has_type_in n2 t) dict d;
  intro_exists d (R.pts_to dict full_perm);
  intro_pure _

#push-options "--split_queries"

#restart-solver
let get_token_from_true
  (#opened: _)
  (d: dictionary)
  (t: Type0)
: SteelGhost token opened
    (R.pts_to dict full_perm d)
    (fun n -> h_exists (R.pts_to dict full_perm) `star` pure (type_of_token n == t))
    (fun _ -> exists (n: n_up_to d.size) . d.type_of_nat n == t)
    (fun _ _ _ -> True)
= let n = FStar.IndefiniteDescription.indefinite_description_ghost (n_up_to d.size) (fun n -> d.type_of_nat n == t) in
  R.witness dict (token_has_type_in n t) d ();
  intro_exists d (R.pts_to dict full_perm);
  intro_pure _;
  token_has_type_inj_type_with n t (type_of_token n);
  elim_pure _;
  let n' : token = n in
  intro_pure (type_of_token n' == t);
  n'

let get_token_from_false
  (#opened: _)
  (d: dictionary)
  (t: Type0)
: SteelGhost token opened
    (R.pts_to dict full_perm d)
    (fun n -> h_exists (R.pts_to dict full_perm) `star` pure (type_of_token n == t))
    (fun _ -> ~ (exists (n: n_up_to d.size) . d.type_of_nat n == t))
    (fun _ _ _ -> True)
= let n = d.size in
  let d' = {size = n+1; type_of_nat = (fun n' -> if n = n'  then t else d.type_of_nat n'); type_of_nat_inj = () } in
  R.write dict d';
  let n' : n_up_to d'.size = n in
  assert (d'.type_of_nat n' == t);
  get_token_from_true d' t

#pop-options

let get_token_from
  (#opened: _)
  (t: Type0)
  ()
: SteelGhostT token opened
    (h_exists (R.pts_to dict full_perm) `star` emp)
    (fun n -> h_exists (R.pts_to dict full_perm) `star` pure (type_of_token n == t))
= let gd : Ghost.erased dictionary = witness_exists () in
  let d : dictionary = Ghost.reveal gd in
  rewrite_slprop (R.pts_to dict full_perm _) (R.pts_to dict full_perm d) (fun _ -> ());
  if FStar.StrongExcludedMiddle.strong_excluded_middle (exists (n: n_up_to d.size) . d.type_of_nat n == t)
  then
    get_token_from_true d t
  else
    get_token_from_false d t

let get_token
  (#opened: _)
  (t: Type0)
: SteelGhost token opened emp (fun _ -> emp) (fun _ -> Ghost.reveal (mem_inv opened inv) == false) (fun _ n _ -> type_of_token n == t)
= let n = with_invariant_g
    inv
    (get_token_from t)
  in
  elim_pure (type_of_token n == t);
  n
