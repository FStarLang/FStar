
(*--build-config
options:--admit_fsi FStar.Set;
other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst
--*)
module MyList
open FStar.List

type nlist (a:Type) (n:nat) = l:list a { length l = n }

val mapT: #n:nat -> ('a -> Tot 'b) -> nlist 'a #n -> Tot (list 'b #n)
let rec mapT f x = match x with
  | [] -> []
  | a::tl -> f a::mapT f tl

val fold_left2T: #a:Type -> #b:Type -> #acc:Type -> #n:nat
            -> f:(acc -> a -> b -> Tot acc)
            -> acc
            -> l1:nlist a n
            -> l2:nlist b n
            -> Tot acc (decreases n)
let rec fold_left2 (#a:Type) (#b:Type) (#acc:Type) (#n:nat) f acc l1 l2 = match l1, l2 with
    | [], [] -> acc
    | hd1::tl1, hd2::tl2 -> fold_left2 # # #_ #(n - 1) f (f acc hd1 hd2) tl1 tl2
