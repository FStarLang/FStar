module CherryErasedClosure

(* Issue 4783.  [fallback: nat -> a] specialized at [a := unit] is an
   erasable [nat -> unit], but the parameter is classified on the declared
   type and every call passes the closure.  The parameter has to keep its
   function type, or Cherry counts a closure it sees as a [unit]. *)
noeq
type tree (a:Type0) =
  | Leaf : a -> tree a
  | Node : tree a -> tree a

let rec build (#a:Type0) (fallback:nat -> a) (fuel:nat)
  : Tot (tree a) (decreases fuel) =
  if fuel = 0 then Leaf (fallback 0)
  else Node (build fallback (fuel - 1))

let run (fuel:nat) : bool =
  match build (fun _ -> ()) fuel with
  | Node (Leaf _) -> true
  | _ -> false

let main () : FStar.UInt32.t =
  if run 1 then 0ul else 1ul
