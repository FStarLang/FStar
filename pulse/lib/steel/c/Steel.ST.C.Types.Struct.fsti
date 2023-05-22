module Steel.ST.C.Types.Struct
open Steel.ST.Util
include Steel.ST.C.Types.Fields
open Steel.C.Typestring

module P = Steel.FractionalPermission

// To be extracted as: struct t { fields ... }

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

let struct_get_field_pat
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
  (field: field_t fields)
  (v: fields.fd_type field)
  (field': field_t fields)
: Lemma
  (struct_get_field (struct_set_field field v s) field' == (if field' = field then v else struct_get_field s field'))
  [SMTPat (struct_get_field (struct_set_field field v s) field')]
= if field' = field
  then ()
  else struct_get_field_other s field v field'

[@@noextract_to "krml"] // proof-only
val struct0 (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf) : Tot (typedef (struct_t0 tn n fields))

inline_for_extraction
[@@noextract_to "krml"; norm_field_attr] // proof-only
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
: STGhostT unit opened
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
: STGhostT unit opened
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
: STGhostT unit opened
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
: STGhostT unit opened
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
: STGhostT unit opened
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
: STGhostT (Ghost.erased (ref (fields.fd_typedef field))) opened
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
: STT (ref td')
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to r' (struct_get_field v field) `star` has_struct_field r field r')

inline_for_extraction [@@noextract_to "krml"] // primitive
let struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
: STT (ref #(norm norm_field_steps (fields.fd_type field)) (fields.fd_typedef field))
    (pts_to r v)
    (fun r' -> pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) `star` pts_to #(norm norm_field_steps (fields.fd_type field)) r' (struct_get_field v field) `star` has_struct_field r field r')
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
: STGhost unit opened
    (has_struct_field r field r' `star` pts_to r v `star` pts_to r' v')
    (fun _ -> has_struct_field r field r' `star` pts_to r (struct_set_field field v' v))
    (
      struct_get_field v field == unknown (fields.fd_typedef field)
    )
    (fun _ -> True)

let unstruct_field_alt
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
: STGhost (Ghost.erased (struct_t0 tn n fields)) opened
    (has_struct_field r field r' `star` pts_to r v `star` pts_to r' v')
    (fun s' -> has_struct_field r field r' `star` pts_to r s')
    (
      struct_get_field v field == unknown (fields.fd_typedef field)
    )
    (fun s' -> 
      Ghost.reveal s' == struct_set_field field v' v
    )
= unstruct_field r field r';
  _

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
