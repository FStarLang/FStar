module Test

val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y


val append_eq_singl: l1:list 'a -> l2:list 'a -> x:'a ->
  Lemma (requires (append l1 l2 = [x]))
        (ensures ((l1 = [x] /\ l2 = []) \/ (l1 = [] /\ l2 = [x])))
#reset-options
let append_eq_singl l1 l2 x = ()
