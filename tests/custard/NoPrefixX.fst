module NoPrefixX

open FStar.All
open FStar.Attributes
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* Section 102.2.  --custard_c_no_prefix and an [assume val].

   An external's name is the symbol the linker goes looking for, so it is part
   of this unit's interface in the only sense the option cares about -- more
   so than a definition's, since nothing here defines it and the whole file is
   a demand on the outside.  It was not renamed, so a program whose
   realization is called [ticket] had to write [@@custard_extern "ticket"] on
   the declaration; that attribute exists only on this branch, so the source
   stopped typechecking with a released F*, which is not a choice a portable
   library should have to make.

   Both halves are here.  [ticket] carries no attribute and takes its name
   from the option.  [fixed] carries one, and the option must leave it alone:
   the attribute is the target's own spelling, taken verbatim, and an option
   about *prefixes* has nothing to say about a name that was never prefixed. *)

assume val ticket (n:U32.t) : ML U32.t

[@@custard_extern "noprefixx_fixed"]
assume val fixed (n:U32.t) : ML U32.t

let bump (n:U32.t) : ML U32.t = U32.add_mod (ticket n) (fixed n)

let main () : ML I32.t =
  if U32.eq (bump 3ul) 13ul then 0l else 1l
