module Ex05a
//reverse-ok

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse : list 'a -> Tot (list 'a)
let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]

val rev : l1:list 'a -> l2:list 'a -> Tot (list 'a) (decreases l2)
let rec rev l1 l2 =
  match l2 with
  | []     -> l1
  | hd::tl -> rev (hd::l1) tl

val append_assoc : #t:eqtype -> xs:list t -> ys:list t -> zs:list t -> Lemma
      (ensures (append (append xs ys) zs = append xs (append ys zs)))
let rec append_assoc #t xs ys zs =
  match xs with
  | [] -> ()
  | x::xs' -> append_assoc xs' ys zs

val rev_is_ok : #t:eqtype -> l:list t -> Lemma (rev [] l = reverse l)
