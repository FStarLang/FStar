(** This module offers a limited form of untagged unions that gets special
    treatment in the KreMLin compiler. *)
module LowStar.Union

#set-options "--max_fuel 0 --max_ifuel 0"

/// Some helpers
/// ============

/// I seem to recall that if helpers like this one are not bound to a top-level
/// name in the SMT solver, then we rely on hash-consing at the level of the SMT
/// encoding, which is fragile.
let find_fst (#a: eqtype) (x: a) (x', _) =
  x = x'

/// The desired behavior for this one is to not have a pattern, so as not to
/// pollute the client's context.
val existsb_assoc_some: #a:eqtype -> #b:Type -> x:a -> l:list (a & b) -> Lemma
  (requires (List.Tot.existsb (find_fst x) l))
  (ensures (~(None? (List.Tot.assoc x l))))

/// The normalize_term here is essential so that membership in cases can be
/// computed via normalization.
let one_of (#key: eqtype) (cases: list (key & Type)): Type =
  case: key { b2t (normalize_term (List.Tot.existsb (find_fst case) cases ))}

#push-options "--max_fuel 1"
let type_of (#key: eqtype) (cases: list (key & Type)) (case: one_of cases) =
  normalize_term (Some?.v (existsb_assoc_some case cases; List.Tot.assoc case cases))
#pop-options

#push-options "--max_fuel 1 --max_ifuel 1"
let rec pairwise_first_disjoint (#a: eqtype) #b (l: list (a & b)): Tot bool =
  match l with
  | [] -> true
  | [ _ ] -> true
  | (x, _) :: xs ->
      List.Tot.for_all (fun (x', _) -> x <> x') xs &&
      pairwise_first_disjoint xs
#pop-options

/// Key definitions
/// ===============

// TODO: find a way to define ``let case_list = list (key & Type u#a) ...``
// while preserving the universe variable.

/// This module offers a particular flavor of union, which is already indexed by
/// a user-provided type of keys. It's up to the user to give meaning to these
/// keys, for instance by tying a key to a particular property of interest.
val union: #key:eqtype ->
  cases:list (key & Type u#a) { normalize (pairwise_first_disjoint cases) } ->
  case:one_of cases ->
  Type u#a

/// The injection of a value ``v: t``, where the pair ``(case, t)`` is found in
/// ``cases``.
val mk: #key:eqtype ->
  cases:list (key & Type u#a) { normalize (pairwise_first_disjoint cases) } ->
  case:one_of cases ->
  v:type_of cases case ->
  union cases case

val proj: #key:eqtype ->
  cases:list (key & Type u#a) { normalize (pairwise_first_disjoint cases) } ->
  case:one_of cases ->
  u:union cases case ->
  Tot (type_of cases case)
