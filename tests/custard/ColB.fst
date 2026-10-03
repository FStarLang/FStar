module ColB

(* Section 32.4.  Two public definitions asking for one unqualified name.
   Custard refuses rather than picking a suffix: the whole point of
   --custard_c_no_prefix is that the caller writes the name, so producing one
   the caller did not ask for is worse than refusing. *)

module U32 = FStar.UInt32

let f (x: U32.t) : U32.t = U32.add_mod x 2ul

let main () : U32.t = U32.add_mod (ColA.f 1ul) (f 1ul)
