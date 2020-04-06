module Bug1540

class deq a = {
  eq : a -> a -> bool;
}

instance eq_string : deq string = magic ()
instance eq_list (_ : deq 'a) : deq (list 'a) =
  magic ()

[@(expect_failure [228])]
let b1 = eq

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

[@(expect_failure [228])]
let b2 = eq

val f2 : string -> string -> bool
let f2 = eq

val f3 : list string -> list string -> bool
let f3 = eq

val f4 : list (list string) -> list (list string) -> bool
let f4 = eq

val f5 : list (list (list string)) -> list (list (list string)) -> bool
let f5 = eq
