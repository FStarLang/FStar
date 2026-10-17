module Pulse.C.Types.UserStruct
#lang-pulse

(* Model implementation of Pulse.C.Types.UserStruct: verified, but never extracted.
   All typedef operations are defined pointwise through the user-provided
   constructor and destructors. *)

open Pulse.Lib.Pervasives
friend Pulse.C.Types.Base
open Pulse.C.Types.Base
open Pulse.C.Types.Struct.Aux

let us_fractionable (#t: Type0) (sd: struct_def t) (x: t) : prop =
  forall (f: field_t sd.fields) . (sd.field_desc.fd_typedef f).td_fractionable (sd.get x f)

let us_full (#t: Type0) (sd: struct_def t) (x: t) : prop =
  forall (f: field_t sd.fields) . (sd.field_desc.fd_typedef f).td_full (sd.get x f)

let us_frac_phi (#t: Type0) (sd: struct_def t) (x: t) (p: perm)
: Pure ((f: field_t sd.fields) -> Tot (sd.field_desc.fd_type f))
  (requires (us_fractionable sd x))
  (ensures (fun _ -> True))
= fun f -> (sd.field_desc.fd_typedef f).td_mk_fraction (sd.get x f) p

let us_get_mk (#t: Type0) (sd: struct_def t) (phi: (f: field_t sd.fields) -> Tot (sd.field_desc.fd_type f))
: Lemma (forall (f: field_t sd.fields) . sd.get (sd.mk phi) f == phi f)
= Classical.forall_intro (sd.get_mk phi)

let us_mk_fraction (#t: Type0) (sd: struct_def t) (x: t) (p: perm)
: Pure t
  (requires (us_fractionable sd x))
  (ensures (fun y -> p <=. 1.0R ==> us_fractionable sd y))
= let phi = us_frac_phi sd x p in
  us_get_mk sd phi;
  sd.mk phi

let us_get_mk_fraction (#t: Type0) (sd: struct_def t) (x: t) (p: perm)
: Lemma
  (requires (us_fractionable sd x))
  (ensures (forall (f: field_t sd.fields) . sd.get (us_mk_fraction sd x p) f == (sd.field_desc.fd_typedef f).td_mk_fraction (sd.get x f) p))
= us_get_mk sd (us_frac_phi sd x p)

let us_ext (#t: Type0) (sd: struct_def t) (x1 x2: t)
: Lemma
  (requires (forall (f: field_t sd.fields) . sd.get x1 f == sd.get x2 f))
  (ensures (x1 == x2))
= sd.extensionality x1 x2 (fun _ -> ())

let us_uninit_phi (#t: Type0) (sd: struct_def t) (f: field_t sd.fields) : Tot (sd.field_desc.fd_type f) =
  (sd.field_desc.fd_typedef f).td_uninitialized

let us_unknown_phi (#t: Type0) (sd: struct_def t) (f: field_t sd.fields) : Tot (sd.field_desc.fd_type f) =
  (sd.field_desc.fd_typedef f).td_unknown

let us_uninitialized (#t: Type0) (sd: struct_def t)
: Tot (y: t { us_full sd y /\ us_fractionable sd y /\
    (forall (f: field_t sd.fields) . sd.get y f == (sd.field_desc.fd_typedef f).td_uninitialized) })
= us_get_mk sd (us_uninit_phi sd);
  sd.mk (us_uninit_phi sd)

let us_unknown (#t: Type0) (sd: struct_def t)
: Tot (y: t { us_fractionable sd y /\
    (forall (f: field_t sd.fields) . sd.get y f == (sd.field_desc.fd_typedef f).td_unknown) })
= us_get_mk sd (us_unknown_phi sd);
  sd.mk (us_unknown_phi sd)

let us_mk_fraction_full (#t: Type0) (sd: struct_def t) (x: t)
: Lemma
  (requires (us_fractionable sd x))
  (ensures (us_mk_fraction sd x 1.0R == x))
= us_get_mk_fraction sd x 1.0R;
  let aux (f: field_t sd.fields) : Lemma (sd.get (us_mk_fraction sd x 1.0R) f == sd.get x f) =
    (sd.field_desc.fd_typedef f).td_mk_fraction_full (sd.get x f)
  in
  Classical.forall_intro aux;
  us_ext sd (us_mk_fraction sd x 1.0R) x

let us_mk_fraction_compose (#t: Type0) (sd: struct_def t) (x: t) (p1 p2: perm)
: Lemma
  (requires (us_fractionable sd x /\ p1 <=. 1.0R /\ p2 <=. 1.0R))
  (ensures (us_mk_fraction sd (us_mk_fraction sd x p1) p2 == us_mk_fraction sd x (p1 `prod_perm` p2)))
= us_get_mk_fraction sd x p1;
  us_get_mk_fraction sd (us_mk_fraction sd x p1) p2;
  us_get_mk_fraction sd x (p1 `prod_perm` p2);
  let aux (f: field_t sd.fields) : Lemma
    (sd.get (us_mk_fraction sd (us_mk_fraction sd x p1) p2) f == sd.get (us_mk_fraction sd x (p1 `prod_perm` p2)) f)
  = (sd.field_desc.fd_typedef f).td_mk_fraction_compose (sd.get x f) p1 p2
  in
  Classical.forall_intro aux;
  us_ext sd (us_mk_fraction sd (us_mk_fraction sd x p1) p2) (us_mk_fraction sd x (p1 `prod_perm` p2))

let us_full_not_unknown (#t: Type0) (sd: struct_def t) (v: t)
: Lemma
  (requires (us_full sd v))
  (ensures (~ (v == us_unknown sd)))
= let _ : squash (exists (f: field_t sd.fields) . True) = sd.field_desc.fd_nonempty in
  eliminate exists (f: field_t sd.fields) . True
  with (sd.field_desc.fd_typedef f).td_full_not_unknown (sd.get v f)

let us_mk_fraction_unknown (#t: Type0) (sd: struct_def t) (p: perm)
: Lemma (us_mk_fraction sd (us_unknown sd) p == us_unknown sd)
= us_get_mk_fraction sd (us_unknown sd) p;
  let aux (f: field_t sd.fields) : Lemma
    (sd.get (us_mk_fraction sd (us_unknown sd) p) f == sd.get (us_unknown sd) f)
  = (sd.field_desc.fd_typedef f).td_mk_fraction_unknown p
  in
  Classical.forall_intro aux;
  us_ext sd (us_mk_fraction sd (us_unknown sd) p) (us_unknown sd)

let us_mk_fraction_eq_unknown (#t: Type0) (sd: struct_def t) (v: t) (p: perm)
: Lemma
  (requires (us_fractionable sd v /\ us_mk_fraction sd v p == us_unknown sd))
  (ensures (v == us_unknown sd))
= us_get_mk_fraction sd v p;
  let aux (f: field_t sd.fields) : Lemma (sd.get v f == sd.get (us_unknown sd) f) =
    assert (sd.get (us_mk_fraction sd v p) f == sd.get (us_unknown sd) f);
    (sd.field_desc.fd_typedef f).td_mk_fraction_eq_unknown (sd.get v f) p
  in
  Classical.forall_intro aux;
  us_ext sd v (us_unknown sd)

let struct_typedef #t sd = {
  td_fractionable = us_fractionable sd;
  td_mk_fraction = us_mk_fraction sd;
  td_mk_fraction_full = us_mk_fraction_full sd;
  td_mk_fraction_compose = us_mk_fraction_compose sd;
  td_full = us_full sd;
  td_uninitialized = us_uninitialized sd;
  td_unknown = us_unknown sd;
  td_full_not_unknown = us_full_not_unknown sd;
  td_mk_fraction_unknown = us_mk_fraction_unknown sd;
  td_mk_fraction_eq_unknown = us_mk_fraction_eq_unknown sd;
}

let has_struct_field _ _ _ = pure False

ghost
fn has_struct_field_dup
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
requires has_struct_field r field r'
ensures has_struct_field r field r' ** has_struct_field r field r'
{
  unfold (has_struct_field r field r');
  unreachable ()
}

ghost
fn has_struct_field_inj
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r1 r2: ref (sd.field_desc.fd_typedef field))
requires has_struct_field r field r1 ** has_struct_field r field r2
ensures has_struct_field r field r1 ** has_struct_field r field r2 ** ref_equiv r1 r2
{
  unfold (has_struct_field r field r1);
  unreachable ()
}

ghost
fn has_struct_field_equiv_from
  (#t: Type)
  (#sd: struct_def t)
  (r1: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
  (r2: ref (struct_typedef sd))
requires ref_equiv r1 r2 ** has_struct_field r1 field r'
ensures ref_equiv r1 r2 ** has_struct_field r2 field r'
{
  unfold (has_struct_field r1 field r');
  unreachable ()
}

ghost
fn has_struct_field_equiv_to
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r1' r2': ref (sd.field_desc.fd_typedef field))
requires ref_equiv r1' r2' ** has_struct_field r field r1'
ensures ref_equiv r1' r2' ** has_struct_field r field r2'
{
  unfold (has_struct_field r field r1');
  unreachable ()
}

ghost
fn ghost_struct_field_focus
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
requires has_struct_field r field r' ** pts_to r v
ensures has_struct_field r field r' ** pts_to r (set sd v field (unknown (sd.field_desc.fd_typedef field))) ** pts_to r' (sd.get v field)
{
  unfold (has_struct_field r field r');
  unreachable ()
}

ghost
fn ghost_struct_field
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
requires pts_to r v
returns r': Ghost.erased (ref (sd.field_desc.fd_typedef field))
ensures has_struct_field r field r' ** pts_to r (set sd v field (unknown (sd.field_desc.fd_typedef field))) ** pts_to r' (sd.get v field)
{
  unfold (pts_to r v);
  unreachable ()
}

fn struct_field0
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
requires pts_to r v
returns r': ref td'
ensures has_struct_field r field (coerce_eq () r') ** pts_to r (set sd (Ghost.reveal v) field (unknown (sd.field_desc.fd_typedef field))) ** pts_to #_ #(sd.field_desc.fd_typedef field) (coerce_eq () r') (sd.get (Ghost.reveal v) field)
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn unstruct_field
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (#v': Ghost.erased (sd.field_desc.fd_type field))
  (r': ref (sd.field_desc.fd_typedef field))
requires has_struct_field r field r' ** pts_to r v ** pts_to r' v' ** pure (
      sd.get v field == unknown (sd.field_desc.fd_typedef field)
    )
ensures has_struct_field r field r' ** pts_to r (set sd v field v')
{
  unfold (pts_to r v);
  unreachable ()
}

let fractionable_struct sd s = ()

let mk_fraction_struct sd s p field = us_get_mk_fraction sd s p

let full_struct sd s = ()
