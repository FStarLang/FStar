(*--build-config
options:--admit_fsi FStar.Set;
other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.List.fst
--*)
module MyList
open FStar.List

type nlist (a:Type) (n:nat) = l:list a { length l = n }

val empty_nl: #a:Type -> Tot (nlist a 0)
let empty_nl (#a:Type) = []

val cons_nl: #a:Type -> #n:nat -> hd:a -> tl:(nlist a n) -> Tot (nlist a (n+1))
let cons_nl (#a:Type) (#n:nat) hd tl = hd::tl

val mapT: #a:Type -> #b:Type -> #n:nat -> (a -> Tot b) -> nlist a n -> Tot (nlist b n)
let rec mapT (#a:Type) (#b:Type) (#n:nat) f x = match x with
  | [] -> []
  | a::tl -> (f a)::(mapT #_ #_ #(n - 1) f tl)

val append: #a:Type -> #n1:nat -> #n2:nat -> nlist a n1 -> nlist a n2 -> Tot (nlist a (n1+n2))
let rec append (#a:Type) (#n1:nat) (#n2:nat) l1 l2 =
  match l1 with
  | [] -> l2
  | hd::tl -> hd::(append #_ #(n1-1) #n2 tl l2)

val rev_acc: #a:Type -> #n1:nat -> #n2:nat -> nlist a n1 -> nlist a n2 -> Tot (nlist a (n1+n2))
let rec rev_acc (#a:Type) (#n1:nat) (#n2:nat) l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc #_ #(n1-1) #(n2+1) tl (hd::acc)

val revT: #a:Type -> #n:nat -> nlist a n -> Tot (nlist a n)
let revT (#a:Type) (#n:nat) l = rev_acc #_ #n #(0) l []

val snoc: #n:nat -> l:(nlist 'a n) -> h:'a -> Tot (nlist 'a (n+1))
let snoc #n l h =
  MyList.append #_ #n #(1) l [h]

val rev_snoc: nl:nat -> tl:(nlist 'a nl) -> hd:'a ->
      Lemma (requires True)
            (ensures (MyList.revT #_ #(nl+1) (hd::tl)) ==
                      (snoc #_ #nl (MyList.revT #_ #nl tl) hd))
let rec rev_snoc nl tl hd = admit() (* TODO! *)

val map2T: #a:Type -> #b:Type -> #c:Type -> #n:nat
            -> f:(a -> b -> Tot c)
            -> l1:nlist a n
            -> l2:nlist b n
            -> Tot (nlist c n) (decreases n)
let rec map2T (#a:Type) (#b:Type) (#acc:Type) (#n:nat) f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::map2T #_ #_ #_ #(n - 1) f tl1 tl2

(*
val fold_left2T: #a:Type -> #b:Type -> #acc:Type -> #n:nat
            -> (acc -> a -> b -> Tot acc)
            -> acc
            -> l1:nlist a n
            -> l2:nlist b n
            -> Tot acc (decreases n)
let rec fold_left2T (#a:Type) (#b:Type) (#acc:Type) (#n:nat) f acc l1 l2 = match l1, l2 with
    | [], [] -> acc
    | hd1::tl1, hd2::tl2 -> fold_left2T #_ #_ #_ #(n - 1) f (f acc hd1 hd2) tl1 tl2
*)

val fold_left2T: #a:Type -> #b:Type -> #acc:(nat -> Type) -> #n:nat
            -> f:(m:nat -> acc m -> a -> b -> Tot (acc (m + 1)))
            -> init:nat
            -> acc init
            -> l1:nlist a n
            -> l2:nlist b n
            -> Tot (acc (init + n)) (decreases n)

let rec fold_left2T (#a:Type) (#b:Type) (#acc:nat -> Type) (#n:nat) f init acc l1 l2 = match l1, l2 with
    | [], [] -> acc
    | hd1::tl1, hd2::tl2 -> fold_left2T #_ #_ #_ #(n - 1) f (init + 1) (f init acc hd1 hd2) tl1 tl2
