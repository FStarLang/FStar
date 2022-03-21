module Bug1855

#set-options "--max_fuel 0 --max_ifuel 0"

/// Some helpers
/// ============

/// I seem to recall that if helpers like this one are not bound to a top-level
/// name in the SMT solver, then we rely on hash-consing at the level of the SMT
/// encoding, which is fragile.
let find_fst (#a: eqtype) (x: a) (x', _) =
  x = x'

/// The normalize_term here is essential so that membership in cases can be
/// computed via normalization.
let one_of (#key: eqtype) (cases: list (key & Type)): Type =
  case: key { b2t (normalize_term (List.Tot.existsb (find_fst case) cases ))}

/// The desired behavior for this one is to not have a pattern, so as not to
/// pollute the client's context.
assume val existsb_assoc_some: #a:eqtype -> #b:Type -> x:a -> l:list (a & b) -> Lemma
  (requires (List.Tot.existsb (find_fst x) l))
  (ensures (~(None? (List.Tot.assoc x l))))

#push-options "--max_fuel 1 --max_ifuel 1"
let rec pairwise_first_disjoint (#a: eqtype) #b (l: list (a & b)): Tot bool
  (decreases (List.Tot.length l))
=
  match l with
  | [] -> true
  | [ _ ] -> true
  | (x, _) :: xs ->
      List.Tot.for_all (fun (x', _) -> x <> x') xs &&
      pairwise_first_disjoint xs
#pop-options

/// Key definitions
/// ===============

/// This module offers a particular flavor of union, which is already indexed by
/// a user-provided type of keys. It's up to the user to give meaning to these
/// keys, for instance by tying a key to a particular property of interest.
assume val union: #key:eqtype ->
  cases:list (key & Type u#a) { b2t (normalize_term (pairwise_first_disjoint cases)) } ->
  case:one_of cases ->
  Type u#a

/// The injection of a value ``v: t``, where the pair ``(case, t)`` is found in
/// ``cases``.
#set-options "--admit_smt_queries true"
assume
val mk: #key:eqtype ->
  cases:list (key & Type) ->
  case:one_of cases ->
  (v: normalize_term (Some?.v (existsb_assoc_some case cases; List.Tot.assoc case cases))) ->
  union cases case
