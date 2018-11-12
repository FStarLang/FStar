module Bug138


val foo : l:list int -> Tot int (decreases %[l;0])
val bar : l:list int -> Tot int (decreases %[l;1])
let rec foo l = match l with
    | [] -> 0
    | x::xs -> bar xs
and bar l = foo l


type arg =
  | Foo : arg
  | Bar : arg

val arg_precede : arg -> Tot nat
let arg_precede a =
  match a with
    | Foo -> 0
    | Bar -> 1

val foo_bar : a:arg -> l:list int -> Tot int (decreases %[l;arg_precede a])
let rec foo_bar a l =
  match a with
    | Foo ->
       (match l with
          | [] -> 0
          | x::xs -> foo_bar Bar xs)
    | Bar -> foo_bar Foo l
