module CoreRelMatchBinders
open FStar.Tactics.V2

type t =
  | A of FStar.Seq.lseq int 2
  | B of (l:list int{List.Tot.length l == 4})

let f (x:t) : int = match x with | A y -> FStar.Seq.length y | B l -> List.Tot.length l
let g (x:t) : int = match x with | A z -> FStar.Seq.length z | B m -> List.Tot.length m

(* After unfolding, the two matches differ only in the names of their
   pattern variables, whose sorts are refinements. Core used to re-check
   these sorts, producing a guard that trefl (which allows none) rejected. *)
let test (x:t) =
  assert (f x == g x) by (norm [delta; iota; zeta; primops; unascribe; nbe]; trefl ())
