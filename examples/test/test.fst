(*--build-config
  --*)
module Test
val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y

val append_cons_l: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures ((append (hd::tl) l) = (hd::(append tl l))))
#reset-options
let append_cons_l hd tl l = ()
