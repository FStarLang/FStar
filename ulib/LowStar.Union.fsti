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

#push-options "--max_ifuel 1"
let rec pairwise_first_disjoint (#a: eqtype) #b (l: list (a & b)): Tot bool =
  match l with
  | [] -> true
  | [ _ ] -> true
  | (x, _) :: xs ->
      List.Tot.for_all (fun (x', _) -> x <> x') xs &&
      pairwise_first_disjoint xs
#pop-options


/// Base types
/// ==========

let field_name =
  string

let case_list (key: eqtype): Type u#(a + 1) =
  cases:list (key & (field_name & Type u#a)) { normalize (pairwise_first_disjoint cases) }

/// The normalize_term here is essential so that membership in cases can be
/// computed via normalization.
let one_of (#key: eqtype) (cases: case_list key): Type =
  case: key { b2t (normalize_term (List.Tot.existsb (find_fst case) cases ))}

#push-options "--max_fuel 1"
let lookup_case (#key: eqtype)
  (cases: case_list u#a key)
  (case: one_of cases):
  field_name & Type u#a
=
  Some?.v (existsb_assoc_some case cases; List.Tot.assoc case cases)
#pop-options

let type_of (#key: eqtype) (cases: case_list u#a key) (case: one_of cases): Type u#a =
  normalize_term (snd (lookup_case cases case))

let label_of (#key: eqtype) (cases: case_list u#a key) (case: one_of cases): string =
  normalize_term (fst (lookup_case cases case))


/// Constructors and projectors
/// ===========================

/// This module offers a particular flavor of union, which is already indexed by
/// a user-provided type of keys. It's up to the user to give meaning to these
/// keys, for instance by tying a key to a particular property of interest.
val union (#key: eqtype)
  (cases: case_list u#a key)
  (case: one_of cases):
  Type u#a

/// The injection of a value ``v: t``, where the pair ``(case, t)`` is found in
/// ``cases``.
val mk (#key: eqtype)
  (cases: case_list key)
  (case: one_of cases)
  (v: type_of cases case):
  union cases case

module T = FStar.Tactics

/// Small call to tactics to automatically fill in the label so that at least
/// the user doesn't have to type it in (note: I couldn't figure out a way to
/// make cases implicit based on u).
let resolve_label (#key: eqtype) (cases: case_list key) (case: one_of cases): T.Tac unit =
  // Note: inlining the definition of s causes a tactic error.
  let s: string = label_of cases case in
  T.exact (quote s)

/// Note that ``u`` must be a constant, so that the reduction in ``type_of`` can
/// proceed properly. This could potentially be enforced with an implicit unit
/// argument where the tactic intentionally fails if the argument doesn't have
/// the right shape.
val proj (#key:eqtype)
  (cases: case_list key)
  (case: one_of cases)
  (#[resolve_label cases case] label: string)
  (u: union cases case):
  Tot (type_of cases case)
