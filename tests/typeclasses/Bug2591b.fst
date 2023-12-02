module Bug2591b

class tc1 (a:Type) = {
  tc1_method: a -> a;
}

type box (a:Type) {| tc1 a |} =
 | Box : v:a -> box a

let test0 #a {| tc1 a |} (x : a) : box a = Box x

let test1 #a {| tc1 a |} (b : box a) : a = Box?.v b

let test2 #a {| tc1 a |} (b : box a) : bool = Box? b
