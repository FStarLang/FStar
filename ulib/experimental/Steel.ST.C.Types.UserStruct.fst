module Steel.ST.C.Types.UserStruct
open Steel.ST.GenElim
open Steel.ST.C.Types.Base
module RW = Steel.ST.C.Types.Rewrite
module MRW = Steel.ST.C.Model.Rewrite
module S = Steel.ST.C.Types.Struct.Aux
module FX = FStar.FunctionalExtensionality
module Conn = Steel.C.Model.Connection
module MS = Steel.ST.C.Model.Struct

friend Steel.ST.C.Types.Base
friend Steel.ST.C.Types.Struct.Aux
friend Steel.ST.C.Types.Rewrite

[@@noextract_to "krml"]
let rewrite_from_struct
  (#t: Type)
  (sd: struct_def t)
  (f: S.struct_t1 sd.field_desc)
: Tot t
= sd.mk f

[@@noextract_to "krml"]
let rewrite_to_struct
  (#t: Type)
  (sd: struct_def t)
  (f: t)
: Tot (S.struct_t1 sd.field_desc)
= FX.on_dom (field_t sd.fields) (sd.get f)

let rewrite_forall_struct
  (#t: Type)
  (sd: struct_def t)
: Lemma
  (MRW.rewrite_forall_from (rewrite_from_struct sd) (rewrite_to_struct sd))
= MRW.rewrite_forall_from_intro (rewrite_from_struct sd) (rewrite_to_struct sd) (fun (x: S.struct_t1 sd.field_desc) ->
    Classical.forall_intro (sd.get_mk x);
    assert (x `FX.feq` rewrite_to_struct sd (sd.mk x))
  )

let rewrite_forall_t
  (#t: Type)
  (sd: struct_def t)
: Lemma
  (MRW.rewrite_forall_to (rewrite_from_struct sd) (rewrite_to_struct sd))
= MRW.rewrite_forall_to_intro (rewrite_from_struct sd) (rewrite_to_struct sd) (fun (x: t) ->
    sd.extensionality (rewrite_from_struct sd (rewrite_to_struct sd x)) x (fun (f: field_t sd.fields) ->
      sd.get_mk (rewrite_to_struct sd x) f
    )
  )

[@@noextract_to "krml"]
let rewrite_struct
  (#t: Type)
  (sd: struct_def t)
: Tot (MRW.rewrite_elts (S.struct_t1 sd.field_desc) t)
= {
    rewrite_from_to = rewrite_from_struct sd;
    rewrite_to_from = rewrite_to_struct sd;
    rewrite_equiv = begin
      rewrite_forall_struct sd;
      rewrite_forall_t sd;
      ()
    end;
  }

let struct_typedef sd =
  S.struct1 sd.field_desc `RW.rewrite_typedef` rewrite_struct sd

let iso_to_struct
  (#t: Type)
  (sd: struct_def t)
: Tot (Conn.isomorphism (struct_typedef sd).pcm (S.struct1 sd.field_desc).pcm)
= coerce_eq () (Conn.isomorphism_inverse (MRW.rewrite_iso (S.struct_pcm sd.field_desc) (rewrite_struct sd))) // without the coercion, F* blows up memory

let conn_to_struct
  (#t: Type)
  (sd: struct_def t)
: Tot (Conn.connection (struct_typedef sd).pcm (S.struct1 sd.field_desc).pcm)
= Conn.connection_of_isomorphism (iso_to_struct sd)

let conn_struct_field
  (#t: Type)
  (sd: struct_def t)
  (field: field_t sd.fields)
: Tot (Conn.connection (S.struct1 sd.field_desc).pcm (sd.field_desc.fd_typedef field).pcm)
= MS.struct_field (struct_field_pcm sd.field_desc) field

[@@__reduce__]
let has_struct_field0
  (#t: Type)
  (#sd: struct_def t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
  (r': ref (sd.field_desc.fd_typedef field))
: Tot vprop
= has_focus_ref r (conn_to_struct sd `Conn.connection_compose` conn_struct_field sd field) r'

let has_struct_field
  r field r'
= has_struct_field0 r field r'

let has_struct_field_dup
  r field r'
= rewrite (has_struct_field r field r') (has_struct_field0 r field r');
  has_focus_ref_dup r _ r';
  rewrite (has_struct_field0 r field r') (has_struct_field r field r');
  rewrite (has_struct_field0 r field r') (has_struct_field r field r')

let has_struct_field_inj
  r field r1 r2
= rewrite (has_struct_field r field r1) (has_struct_field0 r field r1);
  rewrite (has_struct_field r field r2) (has_struct_field0 r field r2);
  has_focus_ref_inj r _ r1 r2;
  rewrite (has_struct_field0 r field r1) (has_struct_field r field r1);
  rewrite (has_struct_field0 r field r2) (has_struct_field r field r2)

let has_struct_field_equiv_from
  r1 field r' r2
= rewrite (has_struct_field r1 field r') (has_struct_field0 r1 field r');
  has_focus_ref_equiv_from r1 _ r' r2;
  rewrite (has_struct_field0 r2 field r') (has_struct_field r2 field r')

let has_struct_field_equiv_to
  r field r1' r2'
= rewrite (has_struct_field r field r1') (has_struct_field0 r field r1');
  has_focus_ref_equiv_to r _ r1' r2';
  rewrite (has_struct_field0 r field r2') (has_struct_field r field r2')

#push-options "--z3rlimit 16"
#restart-solver

let ghost_struct_field_focus
  #_ #_ #sd #v r field r'
= rewrite (has_struct_field r field r') (has_struct_field0 r field r');
  let r1 = ghost_focus_ref r (struct1 sd.field_desc) (conn_to_struct sd) in
  has_focus_ref_compose_12_13 r _ r1 _ r';
  let v1 = focus_ref_iso r r1 _ in
  S.ghost_struct_field_focus' r1 field r';
  drop (has_focus_ref r1 _ _);
  let v' = unfocus_ref r r1 _ in
  drop (has_focus_ref _ _ r1);
  rewrite (has_struct_field0 r field r') (has_struct_field r field r');
  sd.extensionality v' (set sd v field (unknown (sd.field_desc.fd_typedef field))) (fun f' -> sd.get_mk v1 f');
  noop ();
  rewrite (pts_to r _) (pts_to r _);
  rewrite (pts_to r' _) (pts_to r' _)

#pop-options

let ghost_struct_field
  #_ #_ #sd r field
= let r' = ghost_focus_ref r (sd.field_desc.fd_typedef field) (conn_to_struct sd `Conn.connection_compose` conn_struct_field sd field) in
  rewrite (has_struct_field0 r field r') (has_struct_field r field r');
  ghost_struct_field_focus r field r';
  r'

let struct_field_1
  (#t: Type)
  (#sd: struct_def t)
  (#v: Ghost.erased t)
  (r: ref (struct_typedef sd))
  (field: field_t sd.fields)
: STT (ref (sd.field_desc.fd_typedef field))
    (pts_to r v)
    (fun r' -> has_struct_field r field r' `star` pts_to r (set sd v field (unknown (sd.field_desc.fd_typedef field))) `star` pts_to r' (sd.get v field))
= let r' = focus_ref r (sd.field_desc.fd_typedef field) (conn_to_struct sd `Conn.connection_compose` conn_struct_field sd field) in
  rewrite (has_struct_field0 r field r') (has_struct_field r field r');
  ghost_struct_field_focus r field r';
  return r'

let struct_field0
  #t _ #sd #v r field td'
= let r1' = struct_field_1 #t #sd #v r field in
  let r' : ref td' = coerce_eq () r1' in
  rewrite (pts_to r1' _) (pts_to #_ #(sd.field_desc.fd_typedef field) (coerce_eq () r') (sd.get (Ghost.reveal v) field));
  rewrite (has_struct_field _ _ _) (has_struct_field r field (coerce_eq () r'));
  return r'

#push-options "--z3rlimit 16"
#restart-solver

let unstruct_field
  #_ #_ #sd #v r field #v' r'
= rewrite (has_struct_field r field r') (has_struct_field0 r field r');
  let r1 = ghost_focus_ref r (struct1 sd.field_desc) (conn_to_struct sd) in
  has_focus_ref_compose_12_13 r _ r1 _ r';
  let v1 = focus_ref_iso r r1 _ in
  S.unstruct_field' r1 field r';
  drop (has_focus_ref r1 _ _);
  let vf = unfocus_ref r r1 _ in
  drop (has_focus_ref _ _ r1);
  rewrite (has_struct_field0 r field r') (has_struct_field r field r');
  sd.extensionality vf (set sd v field v') (fun f' -> sd.get_mk v1 f');
  noop ();
  rewrite (pts_to r _) (pts_to r _)

#pop-options

let fractionable_struct sd s = ()

let mk_fraction_struct sd s p field = ()

let full_struct sd s = ()
