module Ex04f
//fold-left

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function 
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

// BEGIN: FoldLeftInteresting
val fold_left: f:('b -> 'a -> Tot 'a) -> l:list 'b -> 'a -> Tot 'a
let rec fold_left f l a = match l with
  | Nil -> a
  | Cons hd tl -> fold_left f tl (f hd a)

val append_assoc : #a:Type -> l1:list a -> l2:list a -> l3: list a ->
  Lemma (append l1 (append l2 l3) == append (append l1 l2) l3)
let rec append_assoc #a l1 l2 l3 =
  match l1 with
  | [] -> ()
  | h1 :: t1 -> append_assoc t1 l2 l3

let rec fold_left_Cons_is_rev #a (l1 l2: list a) :
  Lemma (fold_left Cons l1 l2 == append (reverse l1) l2) =
  match l1 with
  | [] -> ()
  | h1 :: t1 ->
    // (1) [append (append (reverse t1) [h1]) l2
    //      == append (reverse t1) (append [h1] l2)]
    append_assoc (reverse t1) [h1] l2;
    // (2) [fold_left Cons t1 (h1 :: l2) = append (reverse t1) (h1 :: l2)]
    fold_left_Cons_is_rev t1 (h1 :: l2)
    // append (reverse l1) l2
    // =def= append (append (reverse t1) [h1]) l2
    // =(1)= append (reverse t1) (append [h1] l2)
    // =def= append (reverse t1) (h1 :: l2)
    // =(2)= fold_left Cons t1 (h1 :: l2)
    // =def= fold_left Cons l1 l2
// END: FoldLeftInteresting
