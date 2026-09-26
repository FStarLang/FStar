module NoUnfold
module U8 = FStar.UInt8
open FStar.All

(* Section 77.5.  [--custard_no_unfold] keeps an abbreviation of an applied
   type, so that the monomorphic instance carries the name the program gave
   it rather than the monomorphizer's generated one.  [byte_pair] is the
   abbreviation the flag names and must survive; [flag_pair] is the control,
   the same shape and not named to the flag, and unfolds as every
   abbreviation does by default.

   Not backend specific, and the OCaml backend is where that is checked:
   naming a monomorphic instance is as meaningful here as on the karamel
   path, and the emitted module is a text the greps can read. *)

noeq type pair (a:Type) = { fst : a; snd : a }

type byte_pair = pair U8.t
type flag_pair = pair bool

let swap (p:byte_pair) : byte_pair = { fst = p.snd; snd = p.fst }
let swapf (p:flag_pair) : flag_pair = { fst = p.snd; snd = p.fst }

let main () : ML unit =
  let p = swap ({ fst = 1uy; snd = 2uy }) in
  let q = swapf ({ fst = true; snd = false }) in
  FStar.IO.print_string (U8.to_string p.fst ^ "\n");
  FStar.IO.print_string ((if q.fst then "true" else "false") ^ "\n")
