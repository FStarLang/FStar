module TailLinkApp
(* #4771.  A wrapper whose body is a call to a linked function, with the
   wrapper's own parameters passed straight through.  [eta_reduce] shortens
   [add2 a b = add a b] to [add2 a = add a]; [eta_expand] has to give the
   [b] back, and can only do that if it knows the arity of [add] -- which,
   [add] being linked rather than compiled, is in the imported declarations
   and not in the program.  Before the fix the wrapper was rejected as a
   partial application. *)
module U32 = FStar.UInt32

let add2 (a b: U32.t) : U32.t = TailLinkLib.add a b

let in_range (lo x hi: U32.t) : bool = TailLinkLib.between lo x hi

let main () : U32.t =
  if add2 20ul 22ul <> 42ul then 1ul
  else if not (in_range 1ul 2ul 3ul) then 2ul
  else if in_range 1ul 4ul 3ul then 3ul
  else 0ul
