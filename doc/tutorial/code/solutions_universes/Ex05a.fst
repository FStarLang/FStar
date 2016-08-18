module Ex05a

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

val rev_is_ok_aux : #t:eqtype -> l1:list t -> l2:list t -> Lemma
      (ensures (rev l1 l2 = append (reverse l2) l1)) (decreases l2)
let rec rev_is_ok_aux #t l1 l2 =
  match l2 with
  | [] -> ()
  | hd::tl  -> rev_is_ok_aux (hd::l1) tl; append_assoc (reverse tl) [hd] l1

val append_nil : #t:eqtype -> xs:list t -> Lemma
      (ensures (append xs [] = xs))
let rec append_nil #t xs =
  match xs with
  | [] -> ()
  | _::tl  -> append_nil tl

val rev_is_ok : #t:eqtype -> l:list t -> Lemma (rev [] l = reverse l)
let rev_is_ok #t l = rev_is_ok_aux [] l; append_nil (reverse l)
