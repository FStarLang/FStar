module Bug1055b

open FStar.ST

(* this is accepted *)
let write (#a:Type) (r:ref a) = r := 42

(* this fails without --lax *)
// let append_to1 (#a:Type) (xs:list a) = 2 :: xs

(* this works again *)
let append_to2 (#a:Type) (xs:list a) = ignore(alloc 5); 2 :: xs

(* again only lax typable, causes segfault if called *)
val main : unit -> St unit
let main() = let r = alloc "some string" in write r; ignore(!r ^ !r)

(* again only lax typable, causes segfault if called *)
let foo (#a:Type) (x:a) : Tot (option a) = x
let bar = Some?.v (foo 1)
