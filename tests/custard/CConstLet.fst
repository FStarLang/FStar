module CConstLet
module U32 = FStar.UInt32
open FStar.All

(* Issue 4612: a [let] whose definiens is a constant is propagated, so a rule
   matching [EConst] sees the literal rather than the name it was bound to. *)

assume val sink : U32.t -> ML unit

(* A single read. *)
let once (x : U32.t) : ML unit =
  let n = 64ul in
  sink (U32.add_mod x n)

(* Read more than once. *)
let twice (x : U32.t) : ML unit =
  let n = 65ul in
  sink (U32.add_mod x n);
  sink n

(* The definiens only becomes a literal after constant folding. *)
let folded (x : U32.t) : ML unit =
  let n = U32.mul (U32.div 128ul 64ul) 33ul in
  sink (U32.add_mod x n);
  sink n

let main () : ML unit =
  once 0ul;
  twice 1ul;
  folded 2ul
