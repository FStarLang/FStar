module BugTypeParamProjector

type st : Type u#1 = 
  | MkST: f:int -> st

noeq
type f (s:st) : (unit -> int) -> Type u#0 =
  | MkF : f s (fun _ -> MkST?.f s)

let test #s #g (x:f s g) = assert (MkF? x)
