module Pulse.C.Types.Struct
#lang-pulse

(* Model implementation of Pulse.C.Types.Struct: verified, but never extracted.
   A struct value is a (restricted) dependent function from fields to field
   values; all typedef operations are defined pointwise. *)

open Pulse.Lib.Pervasives
friend Pulse.C.Types.Base
open Pulse.C.Types.Base
open Pulse.C.Types.Fields
module F = FStar.FunctionalExtensionality

let define_struct0 _ _ _ = bool

let s_ty (#tf: Type0) (fields: nonempty_field_description_t tf) (f: field_t fields) : Type0 =
  fields.fd_type f

let struct_t0 tn #tf n fields = F.restricted_t (field_t fields) (s_ty fields)

let struct_set_field #tn #tf #n #fields f v s =
  F.on_dom (field_t fields) #(s_ty fields) (fun (f': field_t fields) ->
    if f' = f then (v <: fields.fd_type f') else s f'
  )

let struct_get_field s field = s field

let struct_eq #tn #tf #n #fields s1 s2 =
  F.extensionality (field_t fields) (s_ty fields) s1 s2;
  s1 == s2

let struct_get_field_same s field v = ()

let struct_get_field_other s field v field' = ()

let s_fractionable
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: prop
= forall (f: field_t fields) . (fields.fd_typedef f).td_fractionable (s f)

let s_mk_fraction
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields) (p: perm)
: Pure (struct_t0 tn n fields)
  (requires (s_fractionable s))
  (ensures (fun y -> p <=. 1.0R ==> s_fractionable y))
= F.on_dom (field_t fields) #(s_ty fields) (fun (f: field_t fields) -> (fields.fd_typedef f).td_mk_fraction (s f) p)

let s_full
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: prop
= forall (f: field_t fields) . (fields.fd_typedef f).td_full (s f)

let s_ext
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf)
  (s1 s2: struct_t0 tn n fields)
: Lemma
  (requires (forall (f: field_t fields) . s1 f == s2 f))
  (ensures (s1 == s2))
= F.extensionality (field_t fields) (s_ty fields) s1 s2

let s_uninitialized
  (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf)
: Tot (y: struct_t0 tn n fields { s_full y /\ s_fractionable y })
= F.on_dom (field_t fields) #(s_ty fields) (fun (f: field_t fields) -> (fields.fd_typedef f).td_uninitialized <: fields.fd_type f)

let s_unknown
  (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf)
: Tot (y: struct_t0 tn n fields { s_fractionable y })
= F.on_dom (field_t fields) #(s_ty fields) (fun (f: field_t fields) -> (fields.fd_typedef f).td_unknown <: fields.fd_type f)

let s_mk_fraction_full
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields)
: Lemma
  (requires (s_fractionable s))
  (ensures (s_mk_fraction s 1.0R == s))
= let aux (f: field_t fields) : Lemma (s_mk_fraction s 1.0R f == s f) =
    (fields.fd_typedef f).td_mk_fraction_full (s f)
  in
  Classical.forall_intro aux;
  s_ext (s_mk_fraction s 1.0R) s

let s_mk_fraction_compose
  (#tn: Type0) (#tf: Type0) (#n: string) (#fields: nonempty_field_description_t tf)
  (s: struct_t0 tn n fields) (p1 p2: perm)
: Lemma
  (requires (s_fractionable s /\ p1 <=. 1.0R /\ p2 <=. 1.0R))
  (ensures (s_mk_fraction (s_mk_fraction s p1) p2 == s_mk_fraction s (p1 `prod_perm` p2)))
= let aux (f: field_t fields) : Lemma (s_mk_fraction (s_mk_fraction s p1) p2 f == s_mk_fraction s (p1 `prod_perm` p2) f) =
    (fields.fd_typedef f).td_mk_fraction_compose (s f) p1 p2
  in
  Classical.forall_intro aux;
  s_ext (s_mk_fraction (s_mk_fraction s p1) p2) (s_mk_fraction s (p1 `prod_perm` p2))

let s_full_not_unknown
  (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf)
  (v: struct_t0 tn n fields)
: Lemma
  (requires (s_full v))
  (ensures (~ (v == s_unknown tn n fields)))
= assert (exists (s: string) . fields.fd_def s == true);
  eliminate exists (s: string) . fields.fd_def s == true
  with (fields.fd_typedef s).td_full_not_unknown (v s)

let s_mk_fraction_unknown
  (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf)
  (p: perm)
: Lemma
  (s_mk_fraction (s_unknown tn n fields) p == s_unknown tn n fields)
= let aux (f: field_t fields) : Lemma (s_mk_fraction (s_unknown tn n fields) p f == s_unknown tn n fields f) =
    (fields.fd_typedef f).td_mk_fraction_unknown p
  in
  Classical.forall_intro aux;
  s_ext (s_mk_fraction (s_unknown tn n fields) p) (s_unknown tn n fields)

let s_mk_fraction_eq_unknown
  (tn: Type0) (#tf: Type0) (n: string) (fields: nonempty_field_description_t tf)
  (v: struct_t0 tn n fields) (p: perm)
: Lemma
  (requires (s_fractionable v /\ s_mk_fraction v p == s_unknown tn n fields))
  (ensures (v == s_unknown tn n fields))
= let aux (f: field_t fields) : Lemma (v f == s_unknown tn n fields f) =
    assert (s_mk_fraction v p f == s_unknown tn n fields f);
    (fields.fd_typedef f).td_mk_fraction_eq_unknown (v f) p
  in
  Classical.forall_intro aux;
  s_ext v (s_unknown tn n fields)

let struct0 tn #tf n fields = {
  td_fractionable = s_fractionable #tn #tf #n #fields;
  td_mk_fraction = s_mk_fraction #tn #tf #n #fields;
  td_mk_fraction_full = s_mk_fraction_full #tn #tf #n #fields;
  td_mk_fraction_compose = s_mk_fraction_compose #tn #tf #n #fields;
  td_full = s_full #tn #tf #n #fields;
  td_uninitialized = s_uninitialized tn n fields;
  td_unknown = s_unknown tn n fields;
  td_full_not_unknown = s_full_not_unknown tn n fields;
  td_mk_fraction_unknown = s_mk_fraction_unknown tn n fields;
  td_mk_fraction_eq_unknown = s_mk_fraction_eq_unknown tn n fields;
}

let struct_get_field_unknown tn n fields field = ()

let struct_get_field_uninitialized tn n fields field = ()

let has_struct_field _ _ _ = pure False

ghost
fn has_struct_field_prop
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
requires has_struct_field r field r'
ensures has_struct_field r field r' ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
    )
{
  unfold (has_struct_field r field r');
  unreachable ()
}

ghost
fn has_struct_field_dup
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
requires has_struct_field r field r'
ensures has_struct_field r field r' ** has_struct_field r field r'
{
  unfold (has_struct_field r field r');
  unreachable ()
}

ghost
fn has_struct_field_inj
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t1: Type0)
  (#td1: typedef t1)
  (r1: ref td1)
  (#t2: Type0)
  (#td2: typedef t2)
  (r2: ref td2)
requires has_struct_field r field r1 ** has_struct_field r field r2
returns _: squash (t1 == t2 /\ td1 == td2)
ensures has_struct_field r field r1 ** has_struct_field r field r2 ** ref_equiv r1 (coerce_eq () r2)
{
  unfold (has_struct_field r field r1);
  unreachable ()
}

ghost
fn has_struct_field_equiv_from
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r1: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
  (r2: ref (struct0 tn n fields))
requires ref_equiv r1 r2 ** has_struct_field r1 field r'
ensures ref_equiv r1 r2 ** has_struct_field r2 field r'
{
  unfold (has_struct_field r1 field r');
  unreachable ()
}

ghost
fn has_struct_field_equiv_to
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r1' r2': ref td')
requires ref_equiv r1' r2' ** has_struct_field r field r1'
ensures ref_equiv r1' r2' ** has_struct_field r field r2'
{
  unfold (has_struct_field r field r1');
  unreachable ()
}

ghost
fn ghost_struct_field_focus
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
requires has_struct_field r field r' ** pts_to r v
returns _: squash (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
  )
ensures has_struct_field r field r' ** pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (Ghost.hide (coerce_eq () (struct_get_field v field)))
{
  unfold (has_struct_field r field r');
  unreachable ()
}

ghost
fn ghost_struct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
requires pts_to r v
returns r': Ghost.erased (ref (fields.fd_typedef field))
ensures pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (struct_get_field v field) ** has_struct_field r field r'
{
  unfold (pts_to r v);
  unreachable ()
}

fn struct_field0
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
requires pts_to r v
returns r': ref td'
ensures pts_to r (struct_set_field field (unknown (fields.fd_typedef field)) v) ** pts_to r' (Ghost.hide (coerce_eq () (struct_get_field v field))) ** has_struct_field r field r'
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn unstruct_field
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (#v: Ghost.erased (struct_t0 tn n fields))
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (#v': Ghost.erased t')
  (r': ref td')
requires has_struct_field r field r' ** pts_to r v ** pts_to r' v' ** pure (
      struct_get_field v field == unknown (fields.fd_typedef field)
    )
returns res: Ghost.erased (struct_t0 tn n fields)
ensures has_struct_field r field r' ** pts_to r res ** pure (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field /\
      Ghost.reveal res == struct_set_field field (coerce_eq () (Ghost.reveal v')) v
    )
{
  unfold (pts_to r v);
  unreachable ()
}

let fractionable_struct s = ()

let mk_fraction_struct s p field = ()

let full_struct s = ()
