module Steel.ST.C.Types.Union
open Steel.ST.Util
include Steel.ST.C.Types.Fields
open Steel.C.Typestring

module P = Steel.FractionalPermission

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

inline_for_extraction
[@@noextract_to "krml"; norm_field_attr] // proof-only
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

let full_union_set_field_intro
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (field: field_t fields)
  (v: fields.fd_type field)
: Lemma
  (requires (full (fields.fd_typedef field) v))
  (ensures (
    full (union0 tn n fields) (union_set_field tn n fields field v)
  ))
= full_union (union_set_field tn n fields field v) field

let full_union_set_field_elim
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (field: field_t fields)
  (v: fields.fd_type field)
: Lemma
  (requires (
    full (union0 tn n fields) (union_set_field tn n fields field v)
  ))
  (ensures (
    full (fields.fd_typedef field) v
  ))
= full_union (union_set_field tn n fields field v) field

let full_union_set_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (field: field_t fields)
  (v: fields.fd_type field)
: Lemma
  (requires True)
  (ensures (
    full (union0 tn n fields) (union_set_field tn n fields field v) <==> full (fields.fd_typedef field) v
  ))
  [SMTPat (full (union0 tn n fields) (union_set_field tn n fields field v))]
= Classical.move_requires (full_union_set_field_intro #tn #tf #n #fields field) v;
  Classical.move_requires (full_union_set_field_elim #tn #tf #n #fields field) v

val has_union_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: Tot vprop

val has_union_field_prop
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: STGhost unit opened
    (has_union_field r field r')
    (fun _ -> has_union_field r field r')
    True
    (fun _ ->
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
    )

val has_union_field_dup
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: STGhostT unit opened
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
  (#t1: Type0)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type0)
  (#td2: typedef t2)
  (r2: ref td2)
: STGhostT (squash (t1 == t2 /\ td1 == td2)) opened
    (has_union_field r field r1 `star` has_union_field r field r2)
    (fun _ -> has_union_field r field r1 `star` has_union_field r field r2 `star` ref_equiv r1 (coerce_eq () r2))

val has_union_field_equiv_from
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r1 r2: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: STGhostT unit opened
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
  (#t': Type0)
  (#td': typedef t')
  (r1 r2: ref td')
: STGhostT unit opened
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
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: STGhostT (squash (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
  )) opened
    (has_union_field r field r' `star` pts_to r v)
    (fun _ -> has_union_field r field r' `star` pts_to r' (Ghost.hide (coerce_eq () (union_get_field v field))))

val ghost_union_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
: STGhostT (Ghost.erased (ref (fields.fd_typedef field))) opened
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
: STT (ref td')
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (Ghost.hide (coerce_eq () (union_get_field v field))))

inline_for_extraction [@@noextract_to "krml"]
let union_field1
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
  (td': typedef t')
  (sq_t': squash (t' ==  fields.fd_type field))
  (sq_td': squash (td' == fields.fd_typedef field))
: STT (ref td')
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))
= union_field0 t' r field td'

inline_for_extraction [@@noextract_to "krml"] // primitive
let union_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
  (#t': Type0)
  (#td': typedef t')
  (# [ norm_fields () ] sq_t': squash (t' ==  fields.fd_type field))
  (# [ norm_fields () ] sq_td': squash (td' == fields.fd_typedef field))
  ()
: STT (ref td')
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))
= union_field0
    t'
    r
    field
    td'

val ununion_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (#v': Ghost.erased t')
  (r': ref td')
: STGhost (Ghost.erased (union_t0 tn n fields)) opened
    (has_union_field r field r' `star` pts_to r' v')
    (fun res -> has_union_field r field r' `star` pts_to r res)
    True
    (fun res ->
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field /\
      Ghost.reveal res == union_set_field tn n fields field (coerce_eq () (Ghost.reveal v'))
    )

let ununion_field_and_drop
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (#v': Ghost.erased t')
  (r': ref td')
: STGhost (Ghost.erased (union_t0 tn n fields)) opened
    (has_union_field r field r' `star` pts_to r' v')
    (fun res -> pts_to r res)
    True
    (fun res ->
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field /\
      Ghost.reveal res == union_set_field tn n fields field (coerce_eq () (Ghost.reveal v'))
    )
= let res = ununion_field r field r' in
  drop (has_union_field _ _ _);
  res

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
: ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized td'))
    (full (union0 tn n fields) v)
    (fun r' -> True)

inline_for_extraction [@@noextract_to "krml"]
let union_switch_field1
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (td': typedef t')
  (sq_t': squash (t' ==  fields.fd_type field))
  (sq_td': squash (td' == fields.fd_typedef field))
: ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized td'))
    (full (union0 tn n fields) v)
    (fun r' -> True)
= union_switch_field0 t' r field td'

inline_for_extraction [@@noextract_to "krml"]
let union_switch_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (# [ norm_fields () ] sq_t': squash (t' ==  fields.fd_type field))
  (# [ norm_fields () ] sq_td': squash (td' == fields.fd_typedef field))
  ()
: ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized td'))
    (full (union0 tn n fields) v)
    (fun r' -> True)
= union_switch_field0
    t'
    r
    field
    td'
