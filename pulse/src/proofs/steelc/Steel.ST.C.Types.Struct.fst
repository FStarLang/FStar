module Steel.ST.C.Types.Struct
open Steel.ST.GenElim1
friend Steel.ST.C.Types.Base
friend Steel.ST.C.Types.Struct.Aux
open Steel.ST.C.Types.Struct.Aux

module FX = FStar.FunctionalExtensionality

let define_struct0 _ _ _ = unit

let nonempty_field_description_nonempty
  (#tf: Type)
  (fd: nonempty_field_description_t tf)
: Lemma
  (exists (f: field_t fd) . True)
= if StrongExcludedMiddle.strong_excluded_middle (exists (f: field_t fd) . True)
  then ()
  else begin
    let prf
      (f: string)
    : Lemma
      (fd.fd_def f == false)
    = if fd.fd_def f
      then Classical.exists_intro (fun (f: field_t fd) -> True) f
      else ()
    in
    Classical.forall_intro prf
  end

[@@noextract_to "krml"]
let fd_gen_of_nonempty_fd (#tf: Type0) (fd: nonempty_field_description_t tf) : Tot (field_description_gen_t (field_t fd)) = {
  fd_nonempty = nonempty_field_description_nonempty fd;
  fd_type = fd.fd_type;
  fd_typedef = (fun (s: field_t fd) -> fd.fd_typedef s);
}

let struct_t0 _ n fields =
  struct_t1 (fd_gen_of_nonempty_fd fields)

let struct_set_field
  f v s
= t_struct_set_field f v s

let struct_get_field
  s field
= t_struct_get_field s field

let struct_eq
  s1 s2
= s1 `FX.feq` s2

let struct_get_field_same
  s field v
= ()

let struct_get_field_other
  s field v field'
= ()

let struct0 _ _ _ = struct1 _

let struct_get_field_unknown
  tn n fields field
= ()

let struct_get_field_uninitialized
  tn n fields field
= ()

let has_struct_field_spec
  (#tf: Type0)
  (fields: nonempty_field_description_t tf)
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
  (r1: ref ((fd_gen_of_nonempty_fd fields).fd_typedef field))
: Tot prop
= t' == fields.fd_type field /\
  td' == fields.fd_typedef field /\
  r' == coerce_eq () r1

[@@__reduce__]
let has_struct_field9
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
= exists_ (fun (r1: ref ((fd_gen_of_nonempty_fd fields).fd_typedef field)) ->
    has_struct_field1 r field r1 `star`
    pure (has_struct_field_spec fields field r' r1)
  )

let has_struct_field
  r field r'
= has_struct_field9 r field r'

let intro_has_struct_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
  (r1: ref ((fd_gen_of_nonempty_fd fields).fd_typedef field))
: STGhost unit opened
    (has_struct_field1 r field r1)
    (fun _ -> has_struct_field r field r')
    (has_struct_field_spec fields field r' r1)
    (fun _ -> True)
= noop ();
  rewrite (has_struct_field9 r field r') (has_struct_field r field r')

let elim_has_struct_field
  (#opened: _)
  (#tn: Type0)
  (#tf: Type0)
  (#n: string)
  (#fields: nonempty_field_description_t tf)
  (r: ref (struct0 tn n fields))
  (field: field_t fields)
  (#t': Type0)
  (#td': typedef t')
  (r': ref td')
: STGhost (Ghost.erased (ref ((fd_gen_of_nonempty_fd fields).fd_typedef field))) opened
    (has_struct_field r field r')
    (fun r1 -> has_struct_field1 r field r1)
    True
    (fun r1 -> has_struct_field_spec fields field r' r1)
= rewrite (has_struct_field r field r') (has_struct_field9 r field r');
  let _ = gen_elim () in
  vpattern_replace_erased (has_struct_field1 r field)

let has_struct_field_prop
  r field r'
= let r1 = elim_has_struct_field r field r' in
  intro_has_struct_field r field r' r1

let has_struct_field_dup
  #opened #tn #tf #n #fields r field r'
= let r'2 = elim_has_struct_field r field r' in
  has_struct_field_dup' r field r'2;
  intro_has_struct_field r field r' r'2;
  intro_has_struct_field r field r' r'2

let has_struct_field_inj
  #_ #tn #tf #n #fields r field r1 r2
= let r1' = elim_has_struct_field r field r1 in
  let r2' = elim_has_struct_field r field r2 in
  has_struct_field_inj' r field r1' r2';
  intro_has_struct_field r field r1 r1';
  intro_has_struct_field r field r2 r2';
  rewrite (ref_equiv r1' r2') (ref_equiv r1 r2)

let has_struct_field_equiv_from
  #_ #tn #tf #n #fields r1 field r' r2
= let r'_ = elim_has_struct_field r1 field r' in
  has_struct_field_equiv_from' r1 field r'_ r2;
  intro_has_struct_field r2 field r' r'_

let has_struct_field_equiv_to
  #_ #tn #tf #n #fields r field r1 r2
= let r1' = elim_has_struct_field r field r1 in
  let r2' : ref ((fd_gen_of_nonempty_fd fields).fd_typedef field) = coerce_eq () r2 in
  rewrite (ref_equiv r1 r2) (ref_equiv r1' r2');
  has_struct_field_equiv_to' r field r1' r2';
  rewrite (ref_equiv r1' r2') (ref_equiv r1 r2);
  intro_has_struct_field r field r2 r2'

let ghost_struct_field_focus
  #_ #tn #tf #n #fields #v r field #t' #td' r'
= let r'_ = elim_has_struct_field r field r' in
  let sq : squash (
      t' == fields.fd_type field /\
      td' == fields.fd_typedef field
  ) = () in
  ghost_struct_field_focus' r field r'_;
  rewrite (pts_to r'_ _) (pts_to r' (Ghost.hide (coerce_eq () (struct_get_field v field))));
  intro_has_struct_field r field r' r'_;
  sq

let ghost_struct_field
  #_ #tn #tf #n #fields #v r field
= let r' = ghost_struct_field' r field in
  let r'2 : Ghost.erased (ref (fields.fd_typedef field)) = coerce_eq () r' in
  rewrite (pts_to r' _) (pts_to r'2 (struct_get_field v field));
  intro_has_struct_field r field r'2 r';
  r'2

let struct_field0
  t' #_ #_ #v r field td'
= let r1' = struct_field' r field in
  let r' : ref td' = coerce_eq () r1' in
  rewrite (pts_to r1' _) (pts_to r' (struct_get_field v field));
  intro_has_struct_field r field r' r1';
  return r'

let unstruct_field
  #_ #tn #tf #n #fields #v r field #_ #_ #v' r'
= let r'_ = elim_has_struct_field r field r' in
  let v'_ : Ghost.erased ((fd_gen_of_nonempty_fd fields).fd_type field) = coerce_eq () v' in
  rewrite (pts_to r' v') (pts_to r'_ v'_);
  unstruct_field' r field r'_;
  intro_has_struct_field r field r' r'_;
  _

let fractionable_struct _ = ()
let mk_fraction_struct _ _ _ = ()

let full_struct s = full_struct_gen s
