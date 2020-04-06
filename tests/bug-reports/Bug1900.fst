module Bug1900

#set-options "--print_universes --ugly"
type t = #a:Type u#a -> x:a -> Tot unit

let foo : t = fun #_ x -> ()

let test1 () = foo 0

assume val t1 : Type u#1
assume val x_t1 : t1

let test2 () = foo x_t1

