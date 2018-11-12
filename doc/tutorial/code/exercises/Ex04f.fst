module Ex04f
//fold-left

assume val fold_left: f:('b -> 'a -> Tot 'a) -> l:list 'b -> 'a -> Tot 'a
//implement fold_left

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function 
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

val fold_left_cons_is_reverse: l:list 'a -> l':list 'a ->
                             Lemma (fold_left Cons l l' == append (reverse l) l')
let rec fold_left_cons_is_reverse l l' = admit() //and replace admit() by a proof
