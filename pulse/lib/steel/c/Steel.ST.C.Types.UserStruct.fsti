module Steel.ST.C.Types.UserStruct
open Steel.ST.Util
open Steel.ST.C.Types.Struct.Aux

module Set = FStar.Set

(* This library allows the user to define their own struct type, with
a constructor from field values, and a destructor to field values for
each field. This may be necessary for recursive structs *)

let set_def
  (#t: eqtype)
  (s: FStar.Set.set t)
  (x: t)
: Tot bool
= FStar.Set.mem x s

noextract
let nonempty_set (t: eqtype) =
  (s: Set.set t { exists x . set_def s x == true })

noextract
let set_snoc // for associativity reasons
(#t: eqtype) (q: FStar.Set.set t) (a: t) : Pure (nonempty_set t)
  (requires True)
  (ensures (fun s ->
    (forall (x: t). {:pattern FStar.Set.mem x s} FStar.Set.mem x s == (x = a || FStar.Set.mem x q))
  ))
= q `FStar.Set.union` FStar.Set.singleton a

[@@noextract_to "krml"]
let field_t (s: Set.set string) : Tot eqtype =
  (f: string { Set.mem f s })

[@@noextract_to "krml"; norm_field_attr]
inline_for_extraction // for field_desc.fd_type
noeq
type struct_def (t: Type) = {
  fields: Set.set string;
  field_desc: field_description_gen_t (field_t fields);
  mk: ((f: field_t fields) -> Tot (field_desc.fd_type f)) -> Tot t;
  get: (t -> (f: field_t fields) -> Tot (field_desc.fd_type f));
  get_mk: (phi: ((f: field_t fields) -> Tot (field_desc.fd_type f))) -> (f: field_t fields) -> Lemma
    (get (mk phi) f == phi f);
  extensionality: (x1: t) -> (x2: t) -> ((f: field_t fields) -> Lemma (get x1 f == get x2 f)) -> Lemma (x1 == x2);
}

let nonempty_set_nonempty_type (x: string) (s: Set.set string) : Lemma
  (requires (x `Set.mem` s))
  (ensures (exists (x: field_t s) . True))
= Classical.exists_intro (fun (_: field_t s) -> True) x

[@@noextract_to "krml"]
let set_aux
  (#t: Type) (sd: struct_def t) (x: t) (f: field_t sd.fields) (v: sd.field_desc.fd_type f) (f': field_t sd.fields)
: Tot (sd.field_desc.fd_type f')
= if f = f' then v else sd.get x f'

[@@noextract_to "krml"]
let set (#t: Type) (sd: struct_def t) (x: t) (f: field_t sd.fields) (v: sd.field_desc.fd_type f) : Tot t =
  sd.mk (set_aux sd x f v)

let get_set (#t: Type) (sd: struct_def t) (x: t) (f: field_t sd.fields) (v: sd.field_desc.fd_type f) (f' : field_t sd.fields) : Lemma
  (sd.get (set sd x f v) f' == (if f = f' then v else sd.get x f'))
  [SMTPat (sd.get (set sd x f v) f')]
= sd.get_mk (set_aux sd x f v) f'

[@@noextract_to "krml"]
val struct_typedef
  (#t: Type)
  (sd: struct_def t)
: Tot (typedef t)

val has_struct_field
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
: Tot vprop

val has_struct_field_dup
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
: STGhostT unit opened
    (has_struct_field r field r')
    (fun _ -> has_struct_field r field r' `star` has_struct_field r field r')

val has_struct_field_inj
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r1 r2: ref (sd.field_desc.fd_typedef field))
: STGhostT unit opened
    (has_struct_field r field r1 `star` has_struct_field r field r2)
    (fun _ -> has_struct_field r field r1 `star` has_struct_field r field r2 `star` ref_equiv r1 r2)

val has_struct_field_equiv_from
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (r1: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
  (r2: ref (struct_typedef sd))
: STGhostT unit opened
    (ref_equiv r1 r2 `star` has_struct_field r1 field r')
    (fun _ -> ref_equiv r1 r2 `star` has_struct_field r2 field r')

val has_struct_field_equiv_to
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r1' r2': ref (sd.field_desc.fd_typedef field))
: STGhostT unit opened
    (ref_equiv r1' r2' `star` has_struct_field r field r1')
    (fun _ -> ref_equiv r1' r2' `star` has_struct_field r field r2')

val ghost_struct_field_focus
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
: STGhostT unit opened
    (has_struct_field r field r' `star` pts_to r v)
    (fun _ -> has_struct_field r field r' `star` pts_to r (set sd v field (unknown (sd.field_desc.fd_typedef field))) `star` pts_to r' (sd.get v field))

val ghost_struct_field
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
: STGhostT (Ghost.erased (ref (sd.field_desc.fd_typedef field))) opened
    (pts_to r v)
    (fun r' -> has_struct_field r field r' `star` pts_to r (set sd v field (unknown (sd.field_desc.fd_typedef field))) `star` pts_to r' (sd.get v field))

[@@noextract_to "krml"] // primitive
val struct_field0
  (#t: Type)
  (t': Type0)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (td': typedef t' {
    t' ==  sd.field_desc.fd_type field /\
    td' == sd.field_desc.fd_typedef field
  })
: STT (ref td')
    (pts_to r v)
    (fun r' -> has_struct_field r field (coerce_eq () r') `star` pts_to r (set sd (Ghost.reveal v) field (unknown (sd.field_desc.fd_typedef field))) `star` pts_to #_ #(sd.field_desc.fd_typedef field) (coerce_eq () r') (sd.get (Ghost.reveal v) field))

inline_for_extraction [@@noextract_to "krml"] // primitive
let struct_field
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
: STT (ref #(norm norm_field_steps (sd.field_desc.fd_type field)) (sd.field_desc.fd_typedef field))
    (pts_to r v)
    (fun r' -> pts_to r (set sd v field (unknown (sd.field_desc.fd_typedef field))) `star` pts_to #(norm norm_field_steps (sd.field_desc.fd_type field)) r' (sd.get v field) `star` has_struct_field r field r')
= struct_field0
    (norm norm_field_steps (sd.field_desc.fd_type field))
    r
    field
    (sd.field_desc.fd_typedef field)

val unstruct_field
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (#v': Ghost.erased (sd.field_desc.fd_type field))
  (r': ref (sd.field_desc.fd_typedef field))
: STGhost unit opened
    (has_struct_field r field r' `star` pts_to r v `star` pts_to r' v')
    (fun _ -> has_struct_field r field r' `star` pts_to r (set sd v field v'))
    (
      sd.get v field == unknown (sd.field_desc.fd_typedef field)
    )
    (fun _ -> True)

let unstruct_field_alt
  (#opened: _)
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (#v': Ghost.erased (sd.field_desc.fd_type field))
  (r': ref (sd.field_desc.fd_typedef field))
: STGhost (Ghost.erased t) opened
    (has_struct_field r field r' `star` pts_to r v `star` pts_to r' v')
    (fun s' -> has_struct_field r field r' `star` pts_to r s')
    (
      sd.get v field == unknown (sd.field_desc.fd_typedef field)
    )
    (fun s' -> Ghost.reveal s' == set sd v field v')
= unstruct_field r field r';
  _

val fractionable_struct
  (#t: Type)
  (sd: struct_def t)
  (s: t)
: Lemma
  (fractionable (struct_typedef sd) s <==> (forall field . fractionable (sd.field_desc.fd_typedef field) (sd.get s field)))
  [SMTPat (fractionable (struct_typedef sd) s)]

module P = Steel.FractionalPermission

val mk_fraction_struct
  (#t: Type)
  (sd: struct_def t)
  (s: t)
  (p: P.perm)
  (field: field_t sd.fields)
: Lemma
  (requires (fractionable (struct_typedef sd) s))
  (ensures (sd.get (mk_fraction (struct_typedef sd) s p) field == mk_fraction (sd.field_desc.fd_typedef field) (sd.get s field) p))
  [SMTPat (sd.get (mk_fraction (struct_typedef sd) s p) field)]

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
  (#t: Type)
  (sd: struct_def t)
  (s: t)
: Lemma
  (full (struct_typedef sd) s <==> (forall field . full (sd.field_desc.fd_typedef field) (sd.get s field)))
  [SMTPat (full (struct_typedef sd) s)]
