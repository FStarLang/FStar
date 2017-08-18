open FStar.DM4F.Heap.ST
open FStar.Erase.Heap.ST


let memo (#a:eqtype) (#b:Type) (f:a -> Tot b) () : ST (a -> ST b) =
  let r = alloc #(list (a * b)) [] in
  let g (x:a) : ST b =
    match L.assoc x !r with
    | None -> let y = f x in r := (x,y) :: !r ; y
    | Some y -> y
  in g
