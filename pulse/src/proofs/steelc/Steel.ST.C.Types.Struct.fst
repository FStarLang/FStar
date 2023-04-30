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

let has_struct_field
  r field r'
= has_struct_field1 r field r'

let has_struct_field_dup
  r field r'
= has_struct_field_dup' r field r'

let has_struct_field_inj
  r field r1 r2
= has_struct_field_inj' r field r1 r2

let has_struct_field_equiv_from
  r1 field r' r2
= has_struct_field_equiv_from' r1 field r' r2

let has_struct_field_equiv_to
  r field r1 r2
= has_struct_field_equiv_to' r field r1 r2
  
let ghost_struct_field_focus
  r field r'
= noop (); // FIXME: WHY WHY WHY? without this noop, z3 fails to prove precondition of field_description_t.fd_typedef . But also works if I put noop () after the function call
  ghost_struct_field_focus' r field r'

let ghost_struct_field
  r field
= noop (); // FIXME: WHY WHY WHY? (same as ghost_struct_field_focus above)
  ghost_struct_field' r field

let struct_field0
  t' #_ #_ #v r field td'
= let r1' = struct_field' r field in
  let r' : ref td' = r1' in
  rewrite (pts_to r1' _) (pts_to r' (struct_get_field v field));
  rewrite (has_struct_field1 _ _ _) (has_struct_field r field r');
  return r'

let unstruct_field
  r field r'
= unstruct_field' r field r'

let fractionable_struct _ = ()
let mk_fraction_struct _ _ _ = ()

let full_struct s = full_struct_gen s
