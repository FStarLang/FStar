module Pulse.C.Types.Struct.Aux
include Pulse.C.Types.Base

// This module is `friend`ed by Pulse.C.Types.Struct and Pulse.C.Types.Array

[@@noextract_to "krml"; norm_field_attr]
inline_for_extraction
noeq
type field_description_gen_t (field_t: eqtype) : Type u#1 = {
  fd_nonempty: squash (exists (f: field_t) . True);
  fd_type: (field_t -> Type0);
  fd_typedef: ((s: field_t) -> Tot (typedef (fd_type s)));
}
