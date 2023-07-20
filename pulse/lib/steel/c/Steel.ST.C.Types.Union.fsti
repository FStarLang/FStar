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
  (r1 r2: ref (fields.fd_typedef field))
: STGhostT unit opened
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
  (r1 r2: ref (fields.fd_typedef field))
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
  (r': ref (fields.fd_typedef field))
: STGhostT unit opened
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
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field v field))

[@@noextract_to "krml"] // primitive
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
: STT (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (union_get_field v field))
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
: STGhostT unit opened
    (has_union_field r field r' `star` pts_to r' v')
    (fun _ -> has_union_field r field r' `star` pts_to r (union_set_field tn n fields field v'))

let ununion_field_and_drop
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#v': Ghost.erased (fields.fd_type field))
  (r': ref (fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r field r' `star` pts_to r' v')
    (fun _ -> pts_to r (union_set_field tn n fields field v'))
= ununion_field r field r';
  drop (has_union_field _ _ _)

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
    (fun r' -> has_union_field r field r' `star` pts_to r' (uninitialized (fields.fd_typedef field)))
    (full (union0 tn n fields) v)
    (fun r' -> True)

inline_for_extraction [@@noextract_to "krml"]
let union_switch_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields)
: ST (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field)) // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (uninitialized (fields.fd_typedef field)))
    (full (union0 tn n fields) v)
    (fun r' -> True)
= union_switch_field0
    (norm norm_field_steps (fields.fd_type field))
    r
    field
    (fields.fd_typedef field)
