module Steel.C.Types
open Steel.C.Typenat
open Steel.C.Typestring
// open Steel.C.StdInt // for size_t
include Steel.Effect.Common
include Steel.Effect
include Steel.Effect.Atomic

module P = Steel.FractionalPermission

/// Helper to compose two permissions into one
val prod_perm (p1 p2: P.perm) : Pure P.perm
  (requires True)
  (ensures (fun p ->
    ((p1 `P.lesser_equal_perm` P.full_perm /\ p2 `P.lesser_equal_perm` P.full_perm) ==>
    p `P.lesser_equal_perm` P.full_perm) /\
    p.v == (let open FStar.Real in p1.v *. p2.v)
  ))

[@@noextract_to "krml"] // proof-only
val typedef (t: Type0) : Type u#1

inline_for_extraction [@@noextract_to "krml"]
let typeof (#t: Type0) (td: typedef t) : Tot Type0 = t

val fractionable (#t: Type0) (td: typedef t) (x: t) : GTot prop

val mk_fraction (#t: Type0) (td: typedef t) (x: t) (p: P.perm) : Ghost t
  (requires (fractionable td x))
  (ensures (fun y -> p `P.lesser_equal_perm` P.full_perm ==> fractionable td y))

val mk_fraction_full (#t: Type0) (td: typedef t) (x: t) : Lemma
  (requires (fractionable td x))
  (ensures (mk_fraction td x P.full_perm == x))
  [SMTPat (mk_fraction td x P.full_perm)]

val mk_fraction_compose (#t: Type0) (td: typedef t) (x: t) (p1 p2: P.perm) : Lemma
  (requires (fractionable td x /\ p1 `P.lesser_equal_perm` P.full_perm /\ p2 `P.lesser_equal_perm` P.full_perm))
  (ensures (mk_fraction td (mk_fraction td x p1) p2 == mk_fraction td x (p1 `prod_perm` p2)))

val full (#t: Type0) (td: typedef t) (v: t) : GTot prop

val uninitialized (#t: Type0) (td: typedef t) : Ghost t
  (requires True)
  (ensures (fun y -> full td y /\ fractionable td y))

val unknown (#t: Type0) (td: typedef t) : Ghost t
  (requires True)
  (ensures (fun y -> fractionable td y))

val mk_fraction_unknown (#t: Type0) (td: typedef t) (p: P.perm) : Lemma
  (ensures (mk_fraction td (unknown td) p == unknown td))

val mk_fraction_eq_unknown (#t: Type0) (td: typedef t) (v: t) (p: P.perm) : Lemma
  (requires (fractionable td v /\ mk_fraction td v p == unknown td))
  (ensures (v == unknown td))


// To be extracted as: *t
[@@noextract_to "krml"] // primitive
val ptr (#t: Type) (td: typedef t) : Tot Type0
[@@noextract_to "krml"] // primitive
val null (#t: Type) (td: typedef t) : Tot (ptr td)
inline_for_extraction [@@noextract_to "krml"]
let ref (#t: Type) (td: typedef t) : Tot Type0 = (p: ptr td { ~ (p == null td) })

val _pts_to (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t) : Steel.Memory.slprop u#1
let trivial_selector (hp: Steel.Memory.slprop u#1) : selector unit hp = fun _ -> ()
[@@__steel_reduce__]
let pts_to (#t: Type) (#td: typedef t) (r: ref td) ([@@@ smt_fallback ] v: Ghost.erased t) : vprop = VUnit ({
  hp = _pts_to r v;
  t = _;
  sel = trivial_selector _;
})

val mk_fraction_split_gen
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t { fractionable td v }) (p p1 p2: P.perm) : SteelGhost unit opened
  (pts_to r (mk_fraction td v p))
  (fun _ -> pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (fun _ -> p == p1 `P.sum_perm` p2 /\ p `P.lesser_equal_perm` P.full_perm)
  (fun _ _ _ -> True)

let mk_fraction_split
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t { fractionable td v }) (p1 p2: P.perm) : SteelGhost unit opened
  (pts_to r v)
  (fun _ -> pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (fun _ -> P.full_perm == p1 `P.sum_perm` p2)
  (fun _ _ _ -> True)
= mk_fraction_full td v;
  change_equal_slprop (pts_to _ _) (pts_to _ _);
  mk_fraction_split_gen r v P.full_perm p1 p2

val mk_fraction_join
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p1 p2: P.perm)
: SteelGhostT unit opened
  (pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (fun _ -> pts_to r (mk_fraction td v (p1 `P.sum_perm` p2)))

// To be extracted as: t
[@@noextract_to "krml"] // primitive
val scalar_t (t: Type0) : Type0
[@@noextract_to "krml"] // proof-only
val scalar (t: Type) : typedef (scalar_t t)
val mk_scalar (#t: Type) (v: t) : Ghost (scalar_t t)
  (requires True)
  (ensures (fun y ->
    fractionable (scalar t) y /\
    full (scalar t) y
  ))

val mk_scalar_fractionable
  (#t: Type)
  (v: t)
  (p: P.perm)
: Lemma
  (requires (fractionable (scalar t) (mk_fraction (scalar t) (mk_scalar v) p)))
  (ensures (p `P.lesser_equal_perm` P.full_perm))

val mk_scalar_inj
  (#t: Type)
  (v1 v2: t)
  (p1 p2: P.perm)
: Lemma
  (requires (mk_fraction (scalar t) (mk_scalar v1) p1 == mk_fraction (scalar t) (mk_scalar v2) p2))
  (ensures (v1 == v2 /\ p1 == p2))
  [SMTPat [mk_fraction (scalar t) (mk_scalar v1) p1; mk_fraction (scalar t) (mk_scalar v2) p2]]

val scalar_unique
  (#opened: _)
  (#t: Type)
  (v1 v2: t)
  (p1 p2: P.perm)
  (r: ref (scalar t))
: SteelGhost unit opened
    (pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) `star` pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
    (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar v1) p1) `star` pts_to r (mk_fraction (scalar t) (mk_scalar v2) p2))
    (fun _ -> True)
    (fun _ _ _ -> v1 == v2 /\ (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm)

[@@noextract_to "krml"] // primitive
val read0 (#t: Type) (#v: Ghost.erased t) (#p: P.perm) (r: ref (scalar t)) : Steel t
  (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v)) p))
  (fun _ -> True)
  (fun _ v' _ -> v' == Ghost.reveal v)

let mk_fraction_full_scalar (#t: Type) (v: t) : Lemma
  (mk_scalar v == mk_fraction (scalar t) (mk_scalar v) P.full_perm)
  [SMTPat (mk_scalar v)]
= ()

inline_for_extraction [@@noextract_to "krml"]
let read (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) : Steel t
  (pts_to r v)
  (fun _ -> pts_to r v)
  (fun _ -> exists v0 p . Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p)
  (fun _ v1 _ -> forall v0 p . (* {:pattern (mk_fraction (scalar t) (mk_scalar v0) p)} *) Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p ==> v0 == v1)
= let v0 = FStar.IndefiniteDescription.indefinite_description_tot _ (fun v0 -> exists p . Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0) p) in
  let p = FStar.IndefiniteDescription.indefinite_description_tot _ (fun p -> Ghost.reveal v == mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p) in
  let prf v0' p' : Lemma
    (requires (Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0') p'))
    (ensures (v0' == Ghost.reveal v0 /\ p' == Ghost.reveal p))
  = mk_scalar_inj (Ghost.reveal v0) v0' p p'
  in
  let prf' v0' p' : Lemma
    (Ghost.reveal v == mk_fraction (scalar t) (mk_scalar v0') p' ==> (v0' == Ghost.reveal v0 /\ p' == Ghost.reveal p))
  = Classical.move_requires (prf v0') p'
  in
  Classical.forall_intro_2 prf';
  change_equal_slprop (pts_to _ _) (pts_to r (mk_fraction (scalar t) (mk_scalar (Ghost.reveal v0)) p));
  let v1 = read0 r in
  change_equal_slprop (pts_to _ _) (pts_to r v);
  return v1

[@@noextract_to "krml"] // primitive
val write (#t: Type) (#v: Ghost.erased (scalar_t t)) (r: ref (scalar t)) (v': t) : Steel unit
  (pts_to r v)
  (fun _ -> pts_to r (mk_fraction (scalar t) (mk_scalar v') P.full_perm))
  (fun _ -> Ghost.reveal v == uninitialized (scalar t) \/ (exists (v0: t) . Ghost.reveal v == mk_scalar v0))
  (fun _ _ _ -> True)

// To be extracted as: struct t { fields ... }
[@@noextract_to "krml"] // primitive
val field_t_nil: Type0
[@@noextract_to "krml"] // primitive
val field_t_cons (fn: Type0) (ft: Type0) (fc: Type0): Type0

val norm_field_attr : unit

noextract
let norm_field_steps = [
  delta_attr [`%norm_field_attr];
  iota; zeta; primops;
]

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
noeq
type field_description_t (t: Type0) : Type u#1 = {
  fd_def: (string -> GTot bool);
  fd_empty: (fd_empty: bool { fd_empty == true <==> (forall s . fd_def s == false) });
  fd_type: (string -> Type0);
  fd_typedef: ((s: string) -> Pure (typedef (fd_type s)) (requires (fd_def s)) (ensures (fun _ -> True)));
}

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let nonempty_field_description_t (t: Type0) =
  (fd: field_description_t t { fd.fd_empty == false })

[@@noextract_to "krml"] // proof-only
let field_t (#t: Type0) (fd: field_description_t t) = (s: string { fd.fd_def s })

inline_for_extraction [@@noextract_to "krml"]
let field_description_nil : field_description_t field_t_nil = {
  fd_def = (fun _ -> false);
  fd_empty = true;
  fd_type = (fun _ -> unit);
  fd_typedef = (fun _ -> false_elim ());
}

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let field_description_cons0
  (fn: Type0) (#ft: Type0) (#fc: Type0) (n: string) (t: typedef ft) (fd: field_description_t fc)
: Tot (field_description_t (field_t_cons fn ft fc))
= {
    fd_def = (fun n' -> n = n' || fd.fd_def n');
    fd_empty = false;
    fd_type = (fun n' -> if n = n' then ft else fd.fd_type n');
    fd_typedef = (fun n' -> if n = n' then t else fd.fd_typedef n');
  }

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let field_description_cons (#ft: Type0) (#fc: Type0) (n: string) (#fn: Type0) (# [ solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == fn))) (t: typedef ft) (fd: field_description_t fc) : Tot (field_description_t (field_t_cons fn ft fc)) =
  field_description_cons0 fn #ft #fc n t fd

[@@noextract_to "krml"] // primitive
val define_struct0 (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let define_struct (n: string) (#tf: Type0) (#tn: Type0) (#[solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: field_description_t tf) : Tot Type0
= define_struct0 tn #tf n fields

// To be extracted as: struct t
[@@noextract_to "krml"] // primitive
val struct_t0 (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let struct_t (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: field_description_t tf) : Tot Type0
= struct_t0 tn #tf n fields

val struct_set_field (#tn: Type0) (#tf: Type0) (#n: string) (#fields: field_description_t tf) (f: field_t fields) (v: fields.fd_type f) (s: struct_t0 tn n fields) : GTot (struct_t0 tn n fields)

val struct_get_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
: GTot (fields.fd_type field)

val struct_eq
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s1 s2: struct_t0 tn n fields)
: Ghost prop
  (requires True)
  (ensures (fun y ->
    (y <==> (s1 == s2)) /\
    (y <==> (forall field . struct_get_field s1 field == struct_get_field s2 field))
  ))

val struct_get_field_same
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
  (v: fields.fd_type field)
: Lemma
  (struct_get_field (struct_set_field field v s) field == v)
  [SMTPat (struct_get_field (struct_set_field field v s) field)]

val struct_get_field_other
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
  (v: fields.fd_type field)
  (field': field_t fields)
: Lemma
  (requires (field' <> field))
  (ensures (struct_get_field (struct_set_field field v s) field' == struct_get_field s field'))
  [SMTPat (struct_get_field (struct_set_field field v s) field')]

[@@noextract_to "krml"] // proof-only
val struct0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot (typedef (struct_t0 tn n fields))

[@@noextract_to "krml"] // proof-only
let struct (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: field_description_t tf) : Pure (typedef (struct_t0 tn n fields))
  (requires (fields.fd_empty == false))
  (ensures (fun _ -> True))
= struct0 tn #tf n fields

val struct_get_field_unknown
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
  (field: field_t fields)
: Lemma
  (struct_get_field (unknown (struct0 tn n fields)) field == unknown (fields.fd_typedef field))
  [SMTPat (struct_get_field (unknown (struct0 tn n fields)) field)]

val struct_get_field_uninitialized
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
  (field: field_t fields)
: Lemma
  (struct_get_field (uninitialized (struct0 tn n fields)) field == uninitialized (fields.fd_typedef field))
  [SMTPat (struct_get_field (uninitialized (struct0 tn n fields)) field)]

val g_struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: GTot (ref (fields.fd_typedef field))

val ghost_struct_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: SteelGhostT unit opened
    (pts_to r v)
    (fun _ -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to (g_struct_field r field) (struct_get_field v field))

[@@noextract_to "krml"] // primitive
val struct_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#opened: _)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: SteelAtomicBase (ref td') false opened Unobservable
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> r' == g_struct_field r field)

inline_for_extraction [@@noextract_to "krml"] // primitive
let struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#opened: _)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: SteelAtomicBase (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field)) false opened Unobservable
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (struct_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> r' == g_struct_field r field)
= struct_field0
    (norm norm_field_steps (fields.fd_type field))
    r
    field
    (fields.fd_typedef field)

val unstruct_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#v': Ghost.erased (fields.fd_type field))
  (r': ref (fields.fd_typedef field))
: SteelGhost unit opened
    (pts_to r v `star` pts_to r' v')
    (fun _ -> pts_to r (struct_set_field field v' v))
    (fun _ ->
      r' == g_struct_field r field /\
      struct_get_field v field == unknown (fields.fd_typedef field)
    )
    (fun _ _ _ -> True)

val fractionable_struct
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: Lemma
  (fractionable (struct0 tn n fields) s <==> (forall field . fractionable (fields.fd_typedef field) (struct_get_field s field)))
  [SMTPat (fractionable (struct0 tn n fields) s)]

val mk_fraction_struct
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (p: P.perm)
  (field: field_t fields)
: Lemma
  (requires (fractionable (struct0 tn n fields) s))
  (ensures (struct_get_field (mk_fraction (struct0 tn n fields) s p) field == mk_fraction (fields.fd_typedef field) (struct_get_field s field) p))
  [SMTPat (struct_get_field (mk_fraction (struct0 tn n fields) s p) field)]

(*
val mk_fraction_struct_recip
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (p: P.perm)
: Ghost (struct_t0 tn n fields)
  (requires (
    (forall field . exists v . fractionable (fields.fd_typedef field) v /\ struct_get_field s field == mk_fraction (fields.fd_typedef field) v p)
  ))
  (ensures (fun s' ->
    fractionable (struct0 tn n fields) s' /\
    s == mk_fraction (struct0 tn n fields) s' p
  ))
*)

val full_struct
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: Lemma
  (full (struct0 tn n fields) s <==> (forall field . full (fields.fd_typedef field) (struct_get_field s field)))
  [SMTPat (full (struct0 tn n fields) s)]

[@@noextract_to "krml"] // primitive
val define_union0 (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let define_union (n: string) (#tf: Type0) (#tn: Type0) (#[solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: field_description_t tf) : Tot Type0
= define_union0 tn #tf n fields

// To be extracted as: union t
[@@noextract_to "krml"] // primitive
val union_t0 (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let union_t (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: field_description_t tf) : Tot Type0
= union_t0 tn #tf n fields

val union_set_field (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf) (f: field_t fields) (v: fields.fd_type f) : GTot (union_t0 tn n fields)

val union_get_case
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (u: union_t0 tn n fields)
: GTot (option (field_t fields))

val union_get_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (u: union_t0 tn n fields)
  (field: field_t fields)
: Ghost (fields.fd_type field)
    (requires (union_get_case u == Some field))
    (ensures (fun _ -> True))

val union_get_field_same
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
  (field: field_t fields)
  (v: fields.fd_type field)
: Lemma
  (requires (~ (v == unknown (fields.fd_typedef field))))
  (ensures (
    let u = union_set_field tn n fields field v in
    union_get_case u == Some field /\
    union_get_field u field == v
  ))
  [SMTPatOr [
    [SMTPat (union_get_case (union_set_field tn n fields field v))];
    [SMTPat (union_get_field (union_set_field tn n fields field v) field)];
  ]]

val union_set_field_same
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (field: field_t fields)
: Lemma
  (requires (union_get_case s == Some field))
  (ensures (
    union_set_field tn n fields field (union_get_field s field) == s
  ))
  [SMTPat (union_set_field tn n fields (union_get_field s field))]

[@@noextract_to "krml"] // proof-only
val union0 (tn: Type0) (#tf: Type0) (n: string) (fields: field_description_t tf) : Tot (typedef (union_t0 tn n fields))

[@@noextract_to "krml"] // proof-only
let union (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: field_description_t tf) : Tot (typedef (union_t0 tn n fields))
= union0 tn #tf n fields

val union_get_case_unknown
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
: Lemma
  (union_get_case (unknown (union0 tn n fields)) == None)
  [SMTPat (unknown (union0 tn n fields))]

val union_set_field_unknown
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
  (field: field_t fields)
: Lemma
  (union_set_field tn n fields field (unknown (fields.fd_typedef field)) == unknown (union0 tn n fields))
  [SMTPat (union_set_field tn n fields field (unknown (fields.fd_typedef field)))]

val union_get_case_uninitialized
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
: Lemma
  (union_get_case (uninitialized (union0 tn n fields)) == None)
  [SMTPat (uninitialized (union0 tn n fields))]

val mk_fraction_union_get_case
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (p: P.perm)
: Lemma
  (requires (fractionable (union0 tn n fields) s))
  (ensures (
    union_get_case (mk_fraction (union0 tn n fields) s p) == union_get_case s
  ))
  [SMTPat (union_get_case (mk_fraction (union0 tn n fields) s p))]

val fractionable_union_get_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (field: field_t fields)
: Lemma
  (requires (union_get_case s == Some field))
  (ensures (
    fractionable (union0 tn n fields) s <==> fractionable (fields.fd_typedef field) (union_get_field s field)
  ))
  [SMTPat (fractionable (union0 tn n fields) s); SMTPat (union_get_field s field)]

val mk_fraction_union_get_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (p: P.perm)
  (field: field_t fields)
: Lemma
  (requires (fractionable (union0 tn n fields) s /\ union_get_case s == Some field))
  (ensures (union_get_field (mk_fraction (union0 tn n fields) s p) field == mk_fraction (fields.fd_typedef field) (union_get_field s field) p))
  [SMTPat (union_get_field (mk_fraction (union0 tn n fields) s p) field)]

val mk_fraction_union_set_field
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: field_description_t tf)
  (field: field_t fields)
  (v: fields.fd_type field)
  (p: P.perm)
: Lemma
  (requires (fractionable (fields.fd_typedef field) v))
  (ensures (
    fractionable (union0 tn n fields) (union_set_field tn n fields field v) /\
    mk_fraction (union0 tn n fields) (union_set_field tn n fields field v) p == union_set_field tn n fields field (mk_fraction (fields.fd_typedef field) v p)
  ))

val full_union
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (s: union_t0 tn n fields)
  (field: field_t fields)
: Lemma
  (requires (union_get_case s == Some field))
  (ensures (
    full (union0 tn n fields) s <==> full (fields.fd_typedef field) (union_get_field s field)
  ))
  [SMTPat (full (union0 tn n fields) s); SMTPat (union_get_field s field)]

val g_union_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
: GTot (ref (fields.fd_typedef field))

val ghost_union_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: SteelGhostT unit opened
    (pts_to r v)
    (fun _ -> pts_to (g_union_field r field) (union_get_field v field))

[@@noextract_to "krml"] // primitive
val union_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#opened: _)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: SteelAtomicBase (ref td') false opened Unobservable
    (pts_to r v)
    (fun r' -> pts_to r' (union_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> r' == g_union_field r field)

inline_for_extraction [@@noextract_to "krml"] // primitive
let union_field
  (#tn: Type0)
  (#tf: Type0)
  (#opened: _)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: SteelAtomicBase (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field)) false opened Unobservable
    (pts_to r v)
    (fun r' -> pts_to #(norm norm_field_steps (fields.fd_type field)) r' (union_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> r' == g_union_field r field)
= union_field0
    (norm norm_field_steps (fields.fd_type field))
    r
    field
    (fields.fd_typedef field)

val ununion_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#v': Ghost.erased (fields.fd_type field))
  (r': ref (fields.fd_typedef field))
: SteelGhost unit opened
    (pts_to r' v')
    (fun _ -> pts_to r (union_set_field tn n fields field v'))
    (fun _ ->
      r' == g_union_field r field
    )
    (fun _ _ _ -> True)

// NOTE: we DO NOT support preservation of struct prefixes

[@@noextract_to "krml"] // primitive
val union_switch_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: Steel (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> pts_to r' (uninitialized (fields.fd_typedef field)))
    (fun _ -> full (union0 tn n fields) v)
    (fun _ r' _ -> r' == g_union_field r field)

inline_for_extraction [@@noextract_to "krml"]
let union_switch_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
: Steel (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field)) // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> pts_to #(norm norm_field_steps (fields.fd_type field)) r' (uninitialized (fields.fd_typedef field)))
    (fun _ -> full (union0 tn n fields) v)
    (fun _ r' _ -> r' == g_union_field r field)
= union_switch_field0
    (norm norm_field_steps (fields.fd_type field))
    r
    field
    (fields.fd_typedef field)

(*
// To be extracted as: t[tn]
val base_array_t (t: Type0) (tn: Type0 (* using Typenat *)) (n: size_t) : Type0
noextract
val base_array0 (#t: Type0) (tn: Type0) (td: typedef t) (n: size_t) : Tot (typedef (base_array_t t tn n))
let base_array (#t: Type0) (td: typedef t) (n: size_t) (#tn: Type0) (# [ solve_nat_t_of_nat () ] prf: squash (norm norm_typenat (nat_t_of_nat (size_v n) == tn))) : Tot (typedef (base_array_t t tn n)) =
  base_array0 #t tn td n
val mk_base_array (#t: Type) (tn: Type0) (n: size_t) (v: Seq.seq t) : Ghost (base_array_t t tn n)
  (requires (
    Seq.length v == size_v n
  ))
  (ensures (fun y -> True))
val mk_base_array_fractionable (#t: Type) (tn: Type0) (td: typedef t) (n: size_t) (v: Seq.seq t) : Lemma
  (requires (Seq.length v == size_v n))
  (ensures (
    Seq.length v == size_v n /\  
    fractionable (base_array0 tn td n) (mk_base_array tn n v) <==> (forall (i: nat) . i < Seq.length v ==> fractionable td (Seq.index v i))
  ))
// and that's all. users are not supposed to manipulate an array directly from its base reference. they should use an array instead.
*)
