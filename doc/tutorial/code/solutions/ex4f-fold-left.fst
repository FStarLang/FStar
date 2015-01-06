module FoldLeft

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function 
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

val fold_left: f:('b -> 'a -> Tot 'a) -> l:list 'b -> 'a -> Tot 'a
let rec fold_left f l a = match l with
  | Nil -> a
  | Cons hd tl -> fold_left f tl (f hd a)

val append_cons: l:list 'a -> hd:'a -> tl:list 'a ->
                 Lemma (append l (Cons hd tl) = append (append l (Cons hd Nil)) (tl))
let rec append_cons l hd tl = match l with
  | Nil -> ()
  | Cons hd' tl' ->
    let ih = append_cons tl' hd tl in
    ()

val snoc_append: l:list 'a -> h:'a -> Lemma (snoc l h = append l (Cons h Nil))
let rec snoc_append l h = match l with
  | Nil -> ()
  | Cons hd tl ->
    let _ = snoc_append tl h in
    ()

val reverse_append: tl:list 'a -> hd:'a ->
                  Lemma (reverse (Cons hd tl) = append (reverse tl) (Cons hd Nil))
let reverse_append tl hd = snoc_append (reverse tl) hd

val fold_left_cons_is_reverse: l:list 'a -> l':list 'a ->
                             Lemma (fold_left Cons l l' = append (reverse l) l')
let rec fold_left_cons_is_reverse l l' = match l with
  | Nil -> ()
  | Cons hd tl ->
    let _ = fold_left_cons_is_reverse tl (Cons hd l') in
    let _ = append_cons (reverse tl) hd l' in
    let _ = reverse_append tl hd in
    ()
