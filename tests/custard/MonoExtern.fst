module MonoExtern

(* Section 32.5.  A [Mono] *value* binder on an external.  Specialization
   substitutes the argument into a body; an external has none, so the argument
   is substituted into nothing.  What used to come out of this was
   [extern uint32_t kpr_launch;] and a call [kpr_launch(k)] against it -- and,
   with a closed argument, [return kpr_launch;], which compiles and never
   launches anything. *)

open FStar.Attributes

noeq type desc = { nblk : UInt32.t; f : UInt32.t -> UInt32.t }

[@@custard_extern "kpr_launch"]
assume val launch ([@@@monomorphize] d : desc) : UInt32.t

let go (k : UInt32.t) : UInt32.t =
  launch ({ nblk = 1ul; f = (fun tid -> UInt32.add_mod tid k) })

let main () : UInt32.t = go 3ul
