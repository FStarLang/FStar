module Steel.ST.C.Types.Struct.Aux
include Steel.ST.C.Types.Base

// This module is `friend`ed by Steel.ST.C.Types.Struct and Steel.ST.C.Types.Array

[@@noextract_to "krml"; norm_field_attr]
inline_for_extraction
noeq
type field_description_gen_t (field_t: eqtype) : Type u#1 = {
  fd_nonempty: squash (exists (f: field_t) . True);
  fd_type: (field_t -> Type0);
  fd_typedef: ((s: field_t) -> Tot (typedef (fd_type s)));
}
