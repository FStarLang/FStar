module Pulse.C.Types.Union
#lang-pulse

(* Model implementation of Pulse.C.Types.Union: verified, but never extracted.
   A union value is either unknown, uninitialized, or a single active field
   holding a value that is not unknown. *)

open Pulse.Lib.Pervasives
friend Pulse.C.Types.Base
open Pulse.C.Types.Base
open Pulse.C.Types.Fields

let define_union0 _ _ _ = bool

noeq
type union_t1 (#tf: Type0) (fields: field_description_t tf) : Type0 =
| UUnknown: union_t1 fields
| UUninit: union_t1 fields
| UField:
    (f: field_t fields) ->
    (v: fields.fd_type f { ~ (v == (fields.fd_typedef f).td_unknown) }) ->
    union_t1 fields

let union_t0 tn #tf n fields = union_t1 #tf fields

let union_set_field tn #tf n fields f v =
  if FStar.IndefiniteDescription.strong_excluded_middle (v == (fields.fd_typedef f).td_unknown)
  then UUnknown
  else UField f v

let union_get_case #tn #tf #n #fields u =
  match u with
  | UField f _ -> Some f
  | _ -> None

let union_get_field #tn #tf #n #fields u field =
  let UField _ v = u <: union_t1 fields in
  (v <: fields.fd_type field)

let union_get_field_same tn n fields field v = ()

let union_set_field_same s field = ()

let u_fractionable (#tf: Type0) (#fields: field_description_t tf) (u: union_t1 fields) : prop =
  match u with
  | UField f v -> (fields.fd_typedef f).td_fractionable v
  | _ -> True

let u_mk_fraction (#tf: Type0) (#fields: field_description_t tf) (u: union_t1 fields) (p: perm)
: Pure (union_t1 fields)
  (requires (u_fractionable u))
  (ensures (fun y -> p <=. 1.0R ==> u_fractionable y))
= match u with
  | UField f v ->
    Classical.move_requires ((fields.fd_typedef f).td_mk_fraction_eq_unknown v) p;
    UField f ((fields.fd_typedef f).td_mk_fraction v p)
  | _ -> u

let u_full (#tf: Type0) (#fields: field_description_t tf) (u: union_t1 fields) : prop =
  match u with
  | UUnknown -> False
  | UUninit -> True
  | UField f v -> (fields.fd_typedef f).td_full v

let u_mk_fraction_full (#tf: Type0) (#fields: field_description_t tf) (u: union_t1 fields)
: Lemma
  (requires (u_fractionable u))
  (ensures (u_mk_fraction u 1.0R == u))
= match u with
  | UField f v -> (fields.fd_typedef f).td_mk_fraction_full v
  | _ -> ()

let u_mk_fraction_compose (#tf: Type0) (#fields: field_description_t tf) (u: union_t1 fields) (p1 p2: perm)
: Lemma
  (requires (u_fractionable u /\ p1 <=. 1.0R /\ p2 <=. 1.0R))
  (ensures (u_mk_fraction (u_mk_fraction u p1) p2 == u_mk_fraction u (p1 `prod_perm` p2)))
= match u with
  | UField f v -> (fields.fd_typedef f).td_mk_fraction_compose v p1 p2
  | _ -> ()

let union0 tn #tf n fields = {
  td_fractionable = u_fractionable #tf #fields;
  td_mk_fraction = u_mk_fraction #tf #fields;
  td_mk_fraction_full = u_mk_fraction_full #tf #fields;
  td_mk_fraction_compose = u_mk_fraction_compose #tf #fields;
  td_full = u_full #tf #fields;
  td_uninitialized = UUninit;
  td_unknown = UUnknown;
  td_full_not_unknown = (fun _ -> ());
  td_mk_fraction_unknown = (fun _ -> ());
  td_mk_fraction_eq_unknown = (fun _ _ -> ());
}

let union_get_case_unknown tn n fields = ()

let union_set_field_unknown tn n fields field = ()

let union_get_case_uninitialized tn n fields = ()

let mk_fraction_union_get_case s p = ()

let fractionable_union_get_field s field = ()

let mk_fraction_union_get_field s p field = ()

let mk_fraction_union_set_field tn #tf n fields field v p =
  let td = fields.fd_typedef field in
  td.td_mk_fraction_unknown p;
  Classical.move_requires (td.td_mk_fraction_eq_unknown v) p

let full_union s field = ()

let has_union_field _ _ _ = pure False

ghost
fn has_union_field_prop
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
requires has_union_field r field r'
ensures has_union_field r field r' ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
    )
{
  unfold (has_union_field r field r');
  unreachable ()
}

ghost
fn has_union_field_dup
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
requires has_union_field r field r'
ensures has_union_field r field r' ** has_union_field r field r'
{
  unfold (has_union_field r field r');
  unreachable ()
}

ghost
fn has_union_field_inj
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
requires has_union_field r field r1 ** has_union_field r field r2
returns _: squash (t1 == t2 /\ td1 == td2)
ensures has_union_field r field r1 ** has_union_field r field r2 ** ref_equiv r1 (coerce_eq () r2)
{
  unfold (has_union_field r field r1);
  unreachable ()
}

ghost
fn has_union_field_equiv_from
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r1 r2: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
requires has_union_field r1 field r' ** ref_equiv r1 r2
ensures has_union_field r2 field r' ** ref_equiv r1 r2
{
  unfold (has_union_field r1 field r');
  unreachable ()
}

ghost
fn has_union_field_equiv_to
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (union0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r1 r2: ref td')
requires has_union_field r field r1 ** ref_equiv r1 r2
ensures has_union_field r field r2 ** ref_equiv r1 r2
{
  unfold (has_union_field r field r1);
  unreachable ()
}

ghost
fn ghost_union_field_focus
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
requires has_union_field r field r' ** pts_to r v
returns _: squash (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
  )
ensures has_union_field r field r' ** pts_to r' (Ghost.hide (coerce_eq () (union_get_field v field)))
{
  unfold (has_union_field r field r');
  unreachable ()
}

ghost
fn ghost_union_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: field_description_t tf)
  (#v: Ghost.erased (union_t0 tn n fields))
  (r: ref (union0 tn n fields))
  (field: field_t fields {union_get_case v == Some field})
requires pts_to r v
returns r': Ghost.erased (ref (fields.fd_typedef field))
ensures has_union_field r field r' ** pts_to r' (union_get_field v field)
{
  unfold (pts_to r v);
  unreachable ()
}

fn union_field0
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
requires pts_to r v
returns r': ref td'
ensures has_union_field r field r' ** pts_to r' (Ghost.hide (coerce_eq () (union_get_field v field)))
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn ununion_field
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
requires has_union_field r field r' ** pts_to r' v'
returns res: Ghost.erased (union_t0 tn n fields)
ensures has_union_field r field r' ** pts_to r res ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field /\
      Ghost.reveal res == union_set_field tn n fields field (coerce_eq () (Ghost.reveal v'))
    )
{
  unfold (has_union_field r field r');
  unreachable ()
}

fn union_switch_field0
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
requires pts_to r v ** pure (full (union0 tn n fields) v)
returns r': ref td'
ensures has_union_field r field r' ** pts_to r' (uninitialized td')
{
  unfold (pts_to r v);
  unreachable ()
}
