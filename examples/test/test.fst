(*--build-config
    options:--logQueries;
  --*)
module Test
#set-options "--max_ifuel 1 --initial_ifuel 1 --initial_fuel 0 --max_fuel 0"
type ref : Type -> Type
type aref =
  | Ref : #a:Type -> r:ref a -> aref
    
// val append: list 'a -> list 'a -> Tot (list 'a)
// let rec append x y = match x with
//   | [] -> y
//   | a::tl -> a::append tl y

// val append_cons_l: hd:'a -> tl:list 'a -> l:list 'a ->
//   Lemma (requires True)
//         (ensures ((append (hd::tl) l) = (hd::(append tl l))))
// #reset-options
// let append_cons_l hd tl l = ()
