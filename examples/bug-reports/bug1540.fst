module Bug1540

class deq a = {
  eq : a -> a -> bool;
}

instance eq_string : deq string = magic ()
instance eq_list (_ : deq 'a) : deq (list 'a) =
  magic ()

let f1 #a #d = eq #a #d

let id1 (#x:int) = x
let id2 (#[()]x:int) = x

#set-options "--debug Bug1540 --debug_level High --print_implicits"
let t1 = id1

let t2 = id2


// Bug.f1 :
//     _:
//     list (list (list (list (list (list (list (list (list (list (list (list (list (list (list string)))
//                                               ))))))))))) ->
//     _:
//     list (list (list (list (list (list (list (list (list (list (list (list (list (list (list string)))
//                                               ))))))))))) ->
//     Prims.Tot bool

instance eq_pair (_ : deq 'a) (_ : deq 'b) : deq ('a * 'b) =
  Mkdeq (fun (a,b) (c,d) -> eq a c && eq b d)

let f2 = eq
