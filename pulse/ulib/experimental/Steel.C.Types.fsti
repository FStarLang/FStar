module Steel.C.Types
open Steel.C.Typenat
open Steel.C.Typestring
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
val typedef (t: Type0) : Type0

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


(*
// To be extracted as: void*

// FIXME: Currently, Karamel does not directly support
// void*. examples/steel/arraystructs currently has a stopgap in
// lib/steel_c.h, whose contents should be moved to krmllib.h, unless
// direct support for void* is added to Karamel.

[@@noextract_to "krml"] // primitive
val void_ptr : Type0
 
// To be extracted as: NULL
[@@noextract_to "krml"] // primitive
val void_null: void_ptr

[@@noextract_to "krml"] // proof-only
val type_of_ptr (p: void_ptr { ~ (p == void_null) }) : GTot Type0
val typedef_of_ptr (p: void_ptr { ~ (p == void_null) }) : GTot (typedef (type_of_ptr p))

// To be extracted as: *t
[@@noextract_to "krml"] // primitive
let ptr (#t: Type) (td: typedef t) : Tot Type0 = (p: void_ptr { (~ (p == void_null)) ==> (type_of_ptr p == t /\ typedef_of_ptr p == td) })
[@@noextract_to "krml"] // primitive
let null (#t: Type) (td: typedef t) : Tot (ptr td) = void_null
*)

val ptr (#t: Type) (td: typedef t) : Tot Type0
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

let pts_to_or_null' 
  (#t: Type) (#td: typedef t) (p: ptr td) (v: Ghost.erased t) : vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (p == null _)
  then emp
  else pts_to p v

[@@__steel_reduce__]
let pts_to_or_null (#t: Type) (#td: typedef t) (p: ptr td) ([@@@ smt_fallback ] v: Ghost.erased t) : vprop = VUnit ({
  hp = hp_of (pts_to_or_null' p v);
  t = _;
  sel = trivial_selector _;
})

[@@noextract_to "krml"] // primitive
val is_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: SteelAtomicBase bool false opened Unobservable
    (pts_to_or_null p v)
    (fun _ -> pts_to_or_null p v)
    (fun _ -> True)
    (fun _ res _ -> res == true <==> p == null _)

let assert_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: SteelGhost unit opened
    (pts_to_or_null p v)
    (fun _ -> emp)
    (fun _ -> p == null _)
    (fun _ _ _ -> True)
= rewrite_slprop (pts_to_or_null p v) emp (fun _ -> ())

let assert_not_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: SteelGhost (squash (~ (p == null _))) opened
    (pts_to_or_null p v)
    (fun _ -> pts_to p v)
    (fun _ -> ~ (p == null _))
    (fun _ _ _ -> True)
= change_equal_slprop (pts_to_or_null p v) (pts_to p v)

val ref_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: Tot vprop

val pts_to_equiv
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
  (v: Ghost.erased t)
: SteelGhostT unit opened
    (ref_equiv r1 r2 `star` pts_to r1 v)
    (fun _ -> ref_equiv r1 r2 `star` pts_to r2 v)

val freeable
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: Tot vprop

val freeable_dup
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: SteelGhostT unit opened
    (freeable r)
    (fun _ -> freeable r `star` freeable r)

val freeable_equiv
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: SteelGhostT unit opened
    (ref_equiv r1 r2 `star` freeable r1)
    (fun _ -> ref_equiv r1 r2 `star` freeable r2)

let freeable_or_null'
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
: Tot vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == null _)
  then emp
  else freeable r

[@@__steel_reduce__]
let freeable_or_null (#t: Type) (#td: typedef t) (p: ptr td) : vprop = VUnit ({
  hp = hp_of (freeable_or_null' p);
  t = _;
  sel = trivial_selector _;
})

(*
let freeable_or_null_dup
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
: SteelGhostT vprop opened
    (freeable_or_null r)
    (fun _ -> freeable_or_null r `star` freeable_or_null r)
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == null _)
  then ()
  else freeable r
*)

[@@noextract_to "krml"] // primitive
val alloc
  (#t: Type)
  (td: typedef t)
: SteelT (ptr td)
    emp
    (fun p -> pts_to_or_null p (uninitialized td) `star` freeable_or_null p)

[@@noextract_to "krml"] // primitive
val free
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: Steel unit
    (pts_to r v `star` freeable r)
    (fun _ -> emp)
    (fun _ ->
      full td v
    )
    (fun _ _ _ -> True)

val mk_fraction_split_gen
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p p1 p2: P.perm) : SteelGhost unit opened
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
  (fun _ -> full (scalar t) v)
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
let field_t (#t: Type0) (fd: field_description_t t) : Tot eqtype = (s: string { fd.fd_def s })

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
: Tot (nonempty_field_description_t (field_t_cons fn ft fc))
= {
    fd_def = (fun n' -> n = n' || fd.fd_def n');
    fd_empty = false;
    fd_type = (fun n' -> if n = n' then ft else fd.fd_type n');
    fd_typedef = (fun n' -> if n = n' then t else fd.fd_typedef n');
  }

inline_for_extraction [@@noextract_to "krml"; norm_field_attr]
let field_description_cons (#ft: Type0) (#fc: Type0) (n: string) (#fn: Type0) (# [ solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == fn))) (t: typedef ft) (fd: field_description_t fc) : Tot (nonempty_field_description_t (field_t_cons fn ft fc)) =
  field_description_cons0 fn #ft #fc n t fd

[@@noextract_to "krml"] // primitive
val define_struct0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let define_struct (n: string) (#tf: Type0) (#tn: Type0) (#[solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: nonempty_field_description_t tf) : Tot Type0
= define_struct0 tn #tf n fields

// To be extracted as: struct t
[@@noextract_to "krml"] // primitive
val struct_t0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot Type0
inline_for_extraction [@@noextract_to "krml"]
let struct_t (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: nonempty_field_description_t tf) : Tot Type0
= struct_t0 tn #tf n fields

val struct_set_field (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf) (f: field_t fields) (v: fields.fd_type f) (s: struct_t0 tn n fields) : GTot (struct_t0 tn n fields)

val struct_get_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
: GTot (fields.fd_type field)

val struct_eq
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
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
  (#fields: nonempty_field_description_t tf)
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
  (#fields: nonempty_field_description_t tf)
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
let struct (#tf: Type0) (n: string) (#tn: Type0) (# [solve_mk_string_t ()] prf: squash (norm norm_typestring (mk_string_t n == tn))) (fields: nonempty_field_description_t tf) : Tot (typedef (struct_t0 tn n fields))
= struct0 tn #tf n fields

val struct_get_field_unknown
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: nonempty_field_description_t tf)
  (field: field_t fields)
: Lemma
  (struct_get_field (unknown (struct0 tn n fields)) field == unknown (fields.fd_typedef field))
  [SMTPat (struct_get_field (unknown (struct0 tn n fields)) field)]

val struct_get_field_uninitialized
  (tn: Type0)
  (#tf: Type0)
  (n: string)
  (fields: nonempty_field_description_t tf)
  (field: field_t fields)
: Lemma
  (struct_get_field (uninitialized (struct0 tn n fields)) field == uninitialized (fields.fd_typedef field))
  [SMTPat (struct_get_field (uninitialized (struct0 tn n fields)) field)]

val has_struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: Tot vprop

val has_struct_field_dup
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_struct_field r field r')
    (fun _ -> has_struct_field r field r' `star` has_struct_field r field r')

val has_struct_field_inj
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (r1 r2: ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_struct_field r field r1 `star` has_struct_field r field r2)
    (fun _ -> has_struct_field r field r1 `star` has_struct_field r field r2 `star` ref_equiv r1 r2)

val has_struct_field_equiv_from
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r1: ref (struct0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
  (r2: ref (struct0 tn n fields))
: SteelGhostT unit opened
    (ref_equiv r1 r2 `star` has_struct_field r1 field r')
    (fun _ -> ref_equiv r1 r2 `star` has_struct_field r2 field r')

val has_struct_field_equiv_to
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (r1': ref (fields.fd_typedef field))
  (r2': ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (ref_equiv r1' r2' `star` has_struct_field r field r1')
    (fun _ -> ref_equiv r1' r2' `star` has_struct_field r field r2')

val ghost_struct_field_focus
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_struct_field r field r' `star` pts_to r v)
    (fun _ -> has_struct_field r field r' `star` pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field))

val ghost_struct_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: SteelGhostT (Ghost.erased (ref (fields.fd_typedef field))) opened
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field) `star` has_struct_field r field r')

[@@noextract_to "krml"] // primitive
val struct_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: Steel (ref td')
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field) `star` has_struct_field r field r')
    (fun _ -> True)
    (fun _ _ _ -> True)

inline_for_extraction [@@noextract_to "krml"] // primitive
let struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: Steel (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (struct_get_field v field) `star` has_struct_field r field r')
    (fun _ -> True)
    (fun _ _ _ -> True)
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
    (has_struct_field r field r' `star` pts_to r v `star` pts_to r' v')
    (fun _ -> has_struct_field r field r' `star` pts_to r (struct_set_field field v' v))
    (fun _ ->
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

val has_union_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: Tot vprop

val has_union_field_dup
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_union_field r field r')
    (fun _ -> has_union_field r field r' `star` has_union_field r field r')

val has_union_field_inj
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (r1 r2: ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_union_field r field r1 `star` has_union_field r field r2)
    (fun _ -> has_union_field r field r1 `star` has_union_field r field r2 `star` ref_equiv r1 r2)

val has_union_field_equiv_from
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r1 r2: ref (union0 tn n fields))
  (field: field_t fields)
  (r': ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_union_field r1 field r' `star` ref_equiv r1 r2)
    (fun _ -> has_union_field r2 field r' `star` ref_equiv r1 r2)

val has_union_field_equiv_to
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (r1 r2: ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_union_field r field r1 `star` ref_equiv r1 r2)
    (fun _ -> has_union_field r field r2 `star` ref_equiv r1 r2)

val ghost_union_field_focus
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
  (r': ref (fields.fd_typedef field))
: SteelGhostT unit opened
    (has_union_field r field r' `star` pts_to r v)
    (fun _ -> has_union_field r field r' `star` pts_to r' (union_get_field v field))

val ghost_union_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: SteelGhostT (Ghost.erased (ref (fields.fd_typedef field))) opened
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))

[@@noextract_to "krml"] // primitive
val union_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: Steel (ref td')
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> True)

inline_for_extraction [@@noextract_to "krml"] // primitive
let union_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: Steel (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (union_get_field v field))
    (fun _ -> True)
    (fun _ r' _ -> True) 
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
: SteelGhostT unit opened
    (has_union_field r field r' `star` pts_to r' v')
    (fun _ -> has_union_field r field r' `star` pts_to r (union_set_field tn n fields field v'))

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
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized (fields.fd_typedef field)))
    (fun _ -> full (union0 tn n fields) v)
    (fun _ r' _ -> True)

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
    (fun r' -> has_union_field r field r' `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (uninitialized (fields.fd_typedef field)))
    (fun _ -> full (union0 tn n fields) v)
    (fun _ r' _ -> True)
= union_switch_field0
    (norm norm_field_steps (fields.fd_type field))
    r
    field
    (fields.fd_typedef field)

module SZ = FStar.SizeT

// To be extracted as: t[tn]
// Per the C standard, base array types must be of nonzero size
inline_for_extraction [@@noextract_to "krml"]
let array_size_t = (n: SZ.t { SZ.v n > 0 })
val base_array_t (t: Type0) (tn: Type0 (* using Typenat (or Typestring for `#define`d constants) *)) (n: array_size_t) : Type0
inline_for_extraction [@@noextract_to "krml"] // MUST be syntactically equal to Steel.C.Model.Array.array_domain
let base_array_index_t (n: array_size_t) : Tot eqtype = (i: SZ.t { SZ.v i < SZ.v n })
[@@noextract_to "krml"]
val base_array0 (#t: Type0) (tn: Type0) (td: typedef t) (n: array_size_t) : Tot (typedef (base_array_t t tn n))
val base_array_index (#t: Type0) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (i: base_array_index_t n) : GTot t
val base_array_eq (#t: Type0) (#tn: Type0) (#n: array_size_t) (a1 a2: base_array_t t tn n) : Ghost prop
  (requires True)
  (ensures (fun y ->
    (y <==> (a1 == a2)) /\
    (y <==> (forall (i: base_array_index_t n) . base_array_index a1 i == base_array_index a2 i))
  ))
val mk_base_array (#t: Type) (tn: Type0) (n: array_size_t) (v: Seq.seq t) : Ghost (base_array_t t tn n)
  (requires (
    Seq.length v == SZ.v n
  ))
  (ensures (fun y -> True))
val mk_base_array_index (#t: Type) (tn: Type) (n: array_size_t) (v: Seq.seq t) (i: base_array_index_t n) : Lemma
  (requires (Seq.length v == SZ.v n))
  (ensures (
    Seq.length v == SZ.v n /\
    base_array_index (mk_base_array tn n v) i == Seq.index v (SZ.v i)
  ))
  [SMTPat (base_array_index (mk_base_array tn n v) i)]

let mk_base_array_inj  (#t: Type) (tn: Type0) (n: array_size_t) (v1 v2: Seq.seq t) : Lemma
  (requires (
    Seq.length v1 == SZ.v n /\
    Seq.length v2 == SZ.v n /\
    mk_base_array tn n v1 == mk_base_array tn n v2
  ))
  (ensures (v1 == v2))
  [SMTPat (mk_base_array tn n v1); SMTPat (mk_base_array tn n v2)]
= assert (forall (i: nat) . i < SZ.v n ==> base_array_index (mk_base_array tn n v1) (SZ.uint_to_t i) == base_array_index (mk_base_array tn n v2) (SZ.uint_to_t i));
  assert (v1 `Seq.equal` v2)
val base_array_fractionable (#t: Type) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (td: typedef t) : Lemma
  (
    fractionable (base_array0 tn td n) a <==>
      (forall (i: base_array_index_t n) . fractionable td (base_array_index a i))
  )
  [SMTPat (fractionable (base_array0 tn td n) a)]
val base_array_mk_fraction   (#t: Type) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (td: typedef t) (p: P.perm) (i: base_array_index_t n) : Lemma
  (requires (
    fractionable (base_array0 tn td n) a
  ))
  (ensures (
    fractionable (base_array0 tn td n) a /\
    base_array_index (mk_fraction (base_array0 tn td n) a p) i == mk_fraction td (base_array_index a i) p
  ))
  [SMTPat (base_array_index (mk_fraction (base_array0 tn td n) a p) i)]

val base_array_index_unknown (#t: Type) (tn: Type0) (n: array_size_t) (td: typedef t) (i: base_array_index_t n) : Lemma
  (base_array_index (unknown (base_array0 tn td n)) i == unknown td)
  [SMTPat (base_array_index (unknown (base_array0 tn td n)) i)]

val base_array_index_uninitialized (#t: Type) (tn: Type0) (n: array_size_t) (td: typedef t) (i: base_array_index_t n) : Lemma
  (base_array_index (uninitialized (base_array0 tn td n)) i == uninitialized td)
  [SMTPat (base_array_index (uninitialized (base_array0 tn td n)) i)]

val base_array_index_full (#t: Type) (#tn: Type0) (#n: array_size_t) (td: typedef t) (x: base_array_t t tn n) : Lemma
  (full (base_array0 tn td n) x <==> (forall (i: base_array_index_t n) . full td (base_array_index x i)))
  [SMTPat (full (base_array0 tn td n) x)]

val has_base_array_cell
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: Tot vprop

val has_base_array_cell_post
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: SteelGhost unit opened
    (has_base_array_cell r i r')
    (fun _ -> has_base_array_cell r i r')
    (fun _ -> True)
    (fun _ _ _ -> SZ.v i < SZ.v n)

val has_base_array_cell_dup
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: SteelGhostT unit opened
    (has_base_array_cell r i r')
    (fun _ -> has_base_array_cell r i r' `star` has_base_array_cell r i r')

val has_base_array_cell_inj
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
: SteelGhostT unit opened
    (has_base_array_cell r i r1 `star` has_base_array_cell r i r2)
    (fun _ -> has_base_array_cell r i r1 `star` has_base_array_cell r i r2 `star` ref_equiv r1 r2)

val has_base_array_cell_equiv_from
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r1 r2: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: SteelGhostT unit opened
    (has_base_array_cell r1 i r' `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell r2 i r' `star` ref_equiv r1 r2)

val has_base_array_cell_equiv_to
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
: SteelGhostT unit opened
    (has_base_array_cell r i r1 `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell r i r2 `star` ref_equiv r1 r2)

// contrary to array fields, one is not supposed to take an array cell directly from a base array. one should use arrays instead

// To be extracted to: t*  (array type decays to pointer type)

// We still want to prove that cutting off some cell range on the
// right-hand end of an array won't change the C pointer to which an
// array extracts to. This is why we separately introduce `array_ref`
// to represent the "base+offset" pointer, and `array` which holds the
// ghost length of an array.

[@@noextract_to "krml"] // primitive
val array_ref (#t: Type) (td: typedef t) : Tot Type0
(*
val array_ref_base_size_type (#t: Type) (#td: typedef t) (a: array_ref td) : GTot Type0
*)
val array_ref_base_size (#t: Type) (#td: typedef t) (a: array_ref td) : GTot array_size_t
val has_array_ref_base (#t: Type) (#td: typedef t) (a: array_ref td) (#ty: Type) (r: ref (base_array0 ty td (array_ref_base_size a))) : GTot prop
val has_array_ref_base_inj (#t: Type) (#td: typedef t) (a: array_ref td) (#ty: Type) (r1 r2: ref (base_array0 ty td (array_ref_base_size a))) : Lemma
  (requires (has_array_ref_base a r1 /\ has_array_ref_base a r2))
  (ensures (r1 == r2))
val array_ref_offset (#t: Type) (#td: typedef t) (a: array_ref td) : Ghost SZ.t
  (requires True)
  (ensures (fun y -> SZ.v y <= SZ.v (array_ref_base_size a)))
val array_ref_base_offset_inj (#t: Type) (#td: typedef t) (#ty: Type) (a1: array_ref td) (r1: ref (base_array0 ty td (array_ref_base_size a1))) (a2: array_ref td) (r2: ref (base_array0 ty td (array_ref_base_size a2))) : Lemma
  (requires (
    array_ref_base_size a1 == array_ref_base_size a2 /\
    has_array_ref_base a1 r1 /\
    has_array_ref_base a2 r2 /\
    r1 == coerce_eq () r2 /\
    array_ref_offset a1 == array_ref_offset a2
  ))
  (ensures (a1 == a2))

inline_for_extraction [@@noextract_to "krml"]
let array_len_t (#t: Type) (#td: typedef t) (r: array_ref td) : Tot Type0 =
  (len: Ghost.erased SZ.t { SZ.v (array_ref_offset r) + SZ.v len <= SZ.v (array_ref_base_size r) })

inline_for_extraction [@@noextract_to "krml"]
let array (#t: Type) (td: typedef t) : Tot Type0 = (r: array_ref td & array_len_t r)

val array_pts_to'
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: Tot vprop

[@@__steel_reduce__]
let array_pts_to
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: Tot vprop
= VUnit ({
    hp = hp_of (array_pts_to' r v);
    t = _;
    sel = trivial_selector _;
  })

val array_pts_to_length
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: SteelGhost unit opened
    (array_pts_to r v)
    (fun _ -> array_pts_to r v)
    (fun _ -> True)
    (fun _ _ _ -> Seq.length v == SZ.v (dsnd r))

#set-options "--print_implicits"

let has_array_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (a: array td)
: GTot prop
=   let (| al, len |) = a in
    array_ref_base_size al == n /\
    has_array_ref_base al #tn r /\
    array_ref_offset al == 0sz /\
    Ghost.reveal len == n

let has_array_of_base_inj
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (a1 a2: array td)
: Lemma
  (requires (
      has_array_of_base #t #tn #n #td r a1 /\
      has_array_of_base #t #tn #n #td r a2
  ))
  (ensures (a1 == a2))
= let (| ar1, _ |) = a1 in
  let (| ar2, _ |) = a2 in
  array_ref_base_offset_inj #t #td #tn ar1 r ar2 r

let seq_of_base_array
  (#t: Type)
  (#tn: Type)
  (#n: array_size_t)
  (v: base_array_t t tn n)
: GTot (Seq.lseq t (SZ.v n))
= Seq.init_ghost (SZ.v n) (fun i -> base_array_index v (SZ.uint_to_t i))

val ghost_array_of_base_focus
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
  (a: array td)
: SteelGhost unit opened
    (pts_to r v)
    (fun _ -> array_pts_to a (seq_of_base_array v))
    (fun _ -> has_array_of_base r a)
    (fun _ _ _ -> True)

val ghost_array_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: SteelGhostT (a: Ghost.erased (array td) { has_array_of_base r a }) opened
    (pts_to r v)
    (fun a -> array_pts_to a (seq_of_base_array v))

// to be extracted to just r
[@@noextract_to "krml"] // primitive
val array_ref_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: SteelAtomicBase (array_ref td) false opened Unobservable
    (pts_to r v)
    (fun a -> h_exists (fun (ar: array td) ->
      array_pts_to ar (seq_of_base_array v) `star` pure (
        dfst ar == a /\
        array_ref_base_size a == Ghost.reveal n /\
        array_ref_offset a == 0sz /\
        has_array_of_base r ar /\
        Ghost.reveal (dsnd ar) == Ghost.reveal n
    )))
    (fun _ -> True)
    (fun _ _ _ -> True)

inline_for_extraction [@@noextract_to "krml"]
let array_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: SteelAtomicBase (a: array td { has_array_of_base r a }) false opened Unobservable
    (pts_to r v)
    (fun a -> array_pts_to a (seq_of_base_array v))
    (fun _ -> True)
    (fun _ _ _ -> True)
= let al = array_ref_of_base r in
  let _ = witness_exists () in
  elim_pure _;
  let a = (| al, Ghost.hide (n <: SZ.t) |) in
  change_equal_slprop (array_pts_to _ _) (array_pts_to _ _);
  return a

val unarray_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: ref (base_array0 tn td n))
  (a: array td)
: SteelGhost (Ghost.erased (base_array_t t tn n)) opened
    (array_pts_to a v)
    (fun v' -> pts_to r v')
    (fun _ ->
      has_array_of_base r a
    )
    (fun _ v' _ -> Ghost.reveal v `Seq.equal` seq_of_base_array v')

(*
val has_array_of_ref
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a: array td)
: Tot vprop

val has_array_of_ref_post
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a: array td)
: SteelGhost unit opened
    (has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a)
    (fun _ -> True)
    (fun _ _ _ ->
      let (| al, len |) = a in
      array_ref_base_size al == 1sz /\
      array_ref_offset al == 0sz /\
      Ghost.reveal len == 1sz
    )

val has_array_of_ref_inj
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a1 a2: array td)
: Lemma
    (requires (
      has_array_of_ref r a1 /\
      has_array_of_ref r a2
    ))
    (ensures a1 == a2)

val ghost_array_of_ref_focus
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
  (a: array td)
: SteelGhostT unit opened
    (pts_to r v `star` has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a `star` array_pts_to a (Seq.create 1 (Ghost.reveal v)))

val ghost_array_of_ref
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: SteelGhostT (Ghost.erased (array td)) opened
    (pts_to r v)
    (fun a -> array_pts_to a (Seq.create 1 (Ghost.reveal v)) `star` has_array_of_ref r a)

// to be extracted to just r
[@@noextract_to "krml"] // primitive
val array_ref_of_ref
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: Steel (a: array_ref td { array_ref_base_size a == 1sz /\ array_ref_offset a == 0sz })
    (pts_to r v)
    (fun a -> array_pts_to (| a, Ghost.hide 1sz |) (Seq.create 1 (Ghost.reveal v)) `star` has_array_of_ref r (| a, Ghost.hide 1sz |))
    (fun _ -> True)
    (fun _ _ _ -> True)

inline_for_extraction [@@noextract_to "krml"]
let array_of_ref
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: Steel (array td)
    (pts_to r v)
    (fun a -> array_pts_to a (Seq.create 1 (Ghost.reveal v)) `star` has_array_of_ref r a)
    (fun _ -> True)
    (fun _ _ _ -> True)
= let al = array_ref_of_ref r in
  let a : array td = (| al, Ghost.hide 1sz |) in
  change_equal_slprop (array_pts_to _ _) (array_pts_to _ _);
  change_equal_slprop (has_array_of_ref _ _) (has_array_of_ref r a);
  return a

val unarray_of_ref
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (r: ref td)
  (a: array td)
: SteelGhostT (squash (Seq.length s == 1)) opened
    (array_pts_to a s `star` has_array_of_ref r a)
    (fun _ -> pts_to r (Seq.index s 0) `star` has_array_of_ref r a)
*)

val has_array_cell
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: Tot vprop
(*
= SZ.v i < SZ.v (dsnd a) /\
  has_base_array_cell (array_ref_base (dfst a)) (array_ref_offset (dfst a) `SZ.add` i) r
*)

val has_array_cell_post
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r': ref td)
: SteelGhost unit opened
    (has_array_cell a i r')
    (fun _ -> has_array_cell a i r')
    (fun _ -> True)
    (fun _ _ _ -> SZ.v i < SZ.v (dsnd a))

val has_array_cell_has_base_array_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (dfst a))))
: SteelGhost (Ghost.erased SZ.t) opened
    (has_array_cell a i r)
    (fun j -> has_base_array_cell br j r)
    (fun _ -> has_array_ref_base (dfst a) br)
    (fun _ j _ ->
      SZ.v j == SZ.v (array_ref_offset (dfst a)) + SZ.v i
    )

val has_base_array_cell_has_array_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (dfst a))))
: SteelGhost (Ghost.erased SZ.t) opened
    (has_base_array_cell br i r)
    (fun j -> has_array_cell a j r)
    (fun _ -> has_array_ref_base (dfst a) br /\
      SZ.v i >= SZ.v (array_ref_offset (dfst a)) /\
      SZ.v i < SZ.v (array_ref_offset (dfst a)) + SZ.v (dsnd a)
    )
    (fun _ j _ ->
      SZ.v i == SZ.v (array_ref_offset (dfst a)) + SZ.v j
    )

val has_array_cell_inj
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r1 r2: ref td)
: SteelGhostT unit opened
    (
      has_array_cell a i r1 `star`
      has_array_cell a i r2
    )
    (fun _ ->
      has_array_cell a i r1 `star`
      has_array_cell a i r2 `star`
      ref_equiv r1 r2
    )
// = has_base_array_cell_inj (array_ref_base (dfst a)) (array_ref_offset (dfst a) `SZ.add` i) r1 r2

(*
val has_array_cell_array_of_ref
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a: array td)
: SteelGhostT unit opened
    (has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a `star` has_array_cell a 0sz r)
*)

val ghost_array_cell_focus
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: SteelGhostT (squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a))) opened
    (array_pts_to a s `star` has_array_cell a i r)
    (fun _ -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)

val ghost_array_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: SteelGhost (r: Ghost.erased (ref td) { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) }) opened
    (array_pts_to a s)
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)
    (fun _ ->
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
    )
    (fun _ _ _ -> True)

[@@noextract_to "krml"] // primitive
val array_ref_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array_ref td)
  (len: array_len_t a)
  (i: SZ.t)
: Steel (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v len })
    (array_pts_to (| a, len |) s)
    (fun r -> array_pts_to (| a, len |) (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell (| a, len |) i r)
    (fun _ ->
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v len)
    )
    (fun _ _ _ -> True)

inline_for_extraction [@@noextract_to "krml"]
let array_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: Steel (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
    (array_pts_to a s)
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)
    (fun _ ->
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
    )
    (fun _ _ _ -> True)
= let (| al, len |) = a in
  change_equal_slprop (array_pts_to _ _) (array_pts_to _ s);
  let r = array_ref_cell al len i in
  change_equal_slprop (array_pts_to _ _) (array_pts_to _ _);
  change_equal_slprop (has_array_cell _ _ _) (has_array_cell a i r);
  return r

val unarray_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (#v: Ghost.erased t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: SteelGhost (squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a))) opened
    (array_pts_to a s `star` pts_to r v `star` has_array_cell a i r)
    (fun _ -> array_pts_to a (Seq.upd s (SZ.v i) v) `star` has_array_cell a i r)
    (fun _ ->
      (SZ.v i < Seq.length s ==> Seq.index s (SZ.v i) == unknown td)
    )
    (fun _ _ _ -> True)

val array_ref_shift
  (#t: Type)
  (#td: typedef t)
  (a: array_ref td)
  (i: SZ.t)
: Ghost (array_ref td)
    (requires (SZ.v (array_ref_offset a) + SZ.v i <= SZ.v (array_ref_base_size a)))
    (ensures (fun y -> 
      array_ref_base_size y == array_ref_base_size a /\
      (forall ty r . has_array_ref_base a #ty r ==> has_array_ref_base y #ty (coerce_eq () r)) /\
      array_ref_offset y == array_ref_offset a `SZ.add` i
    ))

inline_for_extraction [@@noextract_to "krml"]
let array_split_l
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
: Pure (array td)
   (requires (SZ.v i <= SZ.v (dsnd a)))
   (ensures (fun _ -> True))
= let (| al, _ |) = a in
  (| al, Ghost.hide i |)

let array_split_r
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
: Ghost (array td)
   (requires (SZ.v i <= SZ.v (dsnd a)))
   (ensures (fun _ -> True))
= let (| al, len |) = a in
  (| array_ref_shift al i, Ghost.hide (len `SZ.sub` i) |)

val ghost_array_split
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: SteelGhost (squash (SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a))) opened
    (array_pts_to a s)
    (fun _ -> array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)) `star`
      array_pts_to (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s)))
    (fun _ -> SZ.v i <= SZ.v (dsnd a) \/ SZ.v i <= Seq.length s)
    (fun _ _ _ -> True)

[@@noextract_to "krml"] // primitive
val array_ref_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (al: array_ref td)
  (len: array_len_t al)
  (i: SZ.t)
: Steel (ar: array_ref td { SZ.v i <= SZ.v len /\ Seq.length s == SZ.v len})
    (array_pts_to (| al, len |) s)
    (fun _ -> array_pts_to (array_split_l (| al, len |) i) (Seq.slice s 0 (SZ.v i)) `star`
      array_pts_to (array_split_r (| al, len |) i) (Seq.slice s (SZ.v i) (Seq.length s)))
    (fun _ -> SZ.v i <= SZ.v len \/ SZ.v i <= Seq.length s)
    (fun _ ar _ -> ar == dfst (array_split_r (| al, len |) i))

inline_for_extraction [@@noextract_to "krml"]
let array_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: Steel (a': array td {SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a)})
    (array_pts_to a s)
    (fun a' -> array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)) `star`
      array_pts_to a' (Seq.slice s (SZ.v i) (Seq.length s)))
    (fun _ -> SZ.v i <= SZ.v (dsnd a) \/ SZ.v i <= Seq.length s)
    (fun _ a' _ -> a' == array_split_r a i)
= let (| al, len |) = a in
  change_equal_slprop (array_pts_to _ _) (array_pts_to _ s);
  let ar = array_ref_split al len i in
  let a' = (| ar, Ghost.hide (len `SZ.sub` i) |) in
  change_equal_slprop (array_pts_to (array_split_l _ _) _) (array_pts_to (array_split_l a _) _);
  change_equal_slprop (array_pts_to (array_split_r _ _) _) (array_pts_to a' _);
  return a'

val array_join
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#sl #sr: Ghost.erased (Seq.seq t))
  (a al ar: array td)
  (i: SZ.t)
: SteelGhost unit opened
    (array_pts_to al sl `star` array_pts_to ar sr)
    (fun _ -> array_pts_to a (sl `Seq.append` sr))
    (fun _ ->
      SZ.v i <= SZ.v (dsnd a) /\
      al == array_split_l a i /\
      ar == array_split_r a i
    )
    (fun _ _ _ -> True)

let fractionable_seq (#t: Type) (td: typedef t) (s: Seq.seq t) : GTot prop =
  forall (i: nat). i < Seq.length s ==> fractionable td (Seq.index s i)

let mk_fraction_seq (#t: Type) (td: typedef t) (s: Seq.seq t) (p: P.perm) : Ghost (Seq.seq t)
  (requires (fractionable_seq td s))
  (ensures (fun _ -> True))
= Seq.init_ghost (Seq.length s) (fun i -> mk_fraction td (Seq.index s i) p)

let mk_fraction_seq_full (#t: Type0) (td: typedef t) (x: Seq.seq t) : Lemma
  (requires (fractionable_seq td x))
  (ensures (mk_fraction_seq td x P.full_perm == x))
  [SMTPat (mk_fraction_seq td x P.full_perm)]
= assert (mk_fraction_seq td x P.full_perm `Seq.equal` x)

val mk_fraction_seq_split_gen
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p p1 p2: P.perm) : SteelGhost unit opened
  (array_pts_to r (mk_fraction_seq td v p))
  (fun _ -> array_pts_to r (mk_fraction_seq td v p1) `star` array_pts_to r (mk_fraction_seq td v p2))
  (fun _ -> p == p1 `P.sum_perm` p2 /\ p `P.lesser_equal_perm` P.full_perm)
  (fun _ _ _ -> True)

let mk_fraction_seq_split
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: array td) (v: Ghost.erased (Seq.seq t) { fractionable_seq td v }) (p1 p2: P.perm) : SteelGhost unit opened
  (array_pts_to r v)
  (fun _ -> array_pts_to r (mk_fraction_seq td v p1) `star` array_pts_to r (mk_fraction_seq td v p2))
  (fun _ -> P.full_perm == p1 `P.sum_perm` p2)
  (fun _ _ _ -> True)
= mk_fraction_seq_full td v;
  change_equal_slprop (array_pts_to _ _) (array_pts_to _ _);
  mk_fraction_seq_split_gen r v P.full_perm p1 p2

val mk_fraction_seq_join
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p1 p2: P.perm)
: SteelGhostT unit opened
  (array_pts_to r (mk_fraction_seq td v p1) `star` array_pts_to r (mk_fraction_seq td v p2))
  (fun _ -> array_pts_to r (mk_fraction_seq td v (p1 `P.sum_perm` p2)))
