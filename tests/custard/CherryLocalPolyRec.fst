module CherryLocalPolyRec
module U32 = FStar.UInt32
open FStar.All

(* A local [let rec] that binds a type of its own is lifted once per
   instantiation (custard.md, section 5.10a).  Lifted once, at a type
   variable, its body read a [list goal] as a [list] of boxed values. *)
noeq type goal = { n : int; s : string }

let keep (l : list goal) (k : list int) : ML (list goal & list int) =
  let rec filter' (f : 'a -> list 'a -> ML bool) (xs : list 'a) : ML (list 'a) =
    match xs with
    | [] -> []
    | x :: xs -> if f x xs then x :: filter' f xs else filter' f xs
  in
  filter' (fun g _ -> g.n > 1) l, filter' (fun x _ -> x > 1) k

(* Mutually recursive, and used at one type only. *)
let alternate (l : list goal) : ML (list goal) =
  let rec evens (xs : list 'a) : ML (list 'a) =
    match xs with [] -> [] | x :: xs -> x :: odds xs
  and odds (xs : list 'a) : ML (list 'a) =
    match xs with [] -> [] | _ :: xs -> evens xs
  in
  evens l

let main () : ML U32.t =
  match keep [{n=1;s="a"}; {n=2;s="b"}] [1; 2; 3], alternate [{n=1;s="a"}; {n=2;s="b"}; {n=3;s="c"}] with
  | ([g], [2; 3]), [g1; g3] ->
    if g.n = 2 && g.s = "b" && g1.n = 1 && g3.s = "c" then 0ul else 1ul
  | _ -> 1ul
