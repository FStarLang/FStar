module Pipes

open FStar.List.Tot

assume val concat : string -> list string -> string

let test (ls : list string) (s1 s2 : string) : string =
  concat s1 <| ls @ [s2]

let cat = (^)

let testl (f : int -> int) (g : int -> bool) (h : bool -> string) : Tot string =
  h <| g <| f 123

let testl_dv (f : int -> Dv int) (g : int -> Dv bool) (h : bool -> Dv string) : Dv string =
  h <| g <| f 123

let testl2 (f : int -> int) (g : int -> bool) (h : int -> bool -> string) : Tot string =
  h 42 <| g <| f 123

let testl2_dv (f : int -> Dv int) (g : int -> Dv bool) (h : int -> bool -> Dv string) : Dv string =
  h 42 <| g <| f 123

let test1 (f g h i : _) = assert ((f <| g <| h <| i) == (f (g (h i))))
let test2 (f g h i : _) = assert ((i |> h |> g |> f) == (f (g (h i))))

let testr (f : int -> int) (g : int -> bool) (h : bool -> string) : Tot string =
  f 123 |> g |> h

let testr_dv (f : int -> Dv int) (g : int -> Dv bool) (h : bool -> Dv string) : Dv string =
  f 123 |> g |> h

let mktup2 x y : string & int =
    let xx = string_of_int x |> id #string in
    (xx, y)

let mktup2_b x y : string & int =
    id #string <| string_of_int x, y

let mktup2_c x y : string & int =
    (id #string <| string_of_int x), y

let mktup2_d x y : string & int =
    id #(string & int) <| (string_of_int x, y)

let assoc1 #a #b #c (x:a) (y : b -> a -> c) (z : b) : c =
  x |> y <| z

let assoc1' #a #b #c (x:a) (y : b -> a -> c) (z : b) : c =
  x |> (y <| z)

let assoc1'' #a #b #c (x:a) (y : a -> b -> c) (z : b) : c =
  (x |> y) <| z

let assoc2 #a #b #c (x:a -> b) (y : a) (z : b -> c) : c =
  x <| y |> z

let assoc2' #a #b #c (x:a -> b) (y : a) (z : b -> c) : c =
  (x <| y) |> z

let assoc2'' #a #b #c (x:b -> c) (y : a) (z : a -> b) : c =
  x <| (y |> z)
