module Bug1750

let t_f = bool -> Tot bool
let t_g = bool -> GTot bool
[@(expect_failure [19])]
let test (b:bool) (f:'a{'a == t_f}) (g:'b{'b == t_g}) =
  if b then f else g


type eff_tag =
  | G
  | T

let eff (t:eff_tag) (b:Type) =
  match t with
  | T -> unit -> Tot b
  | G -> unit -> GTot b

let eff_to_tot (x:eff T 'a) : Tot 'a = x ()

let gtot_to_eff #a #b (f:(x:a -> GTot (b x))) : x:a -> eff G (b x) = fun x () -> f x

assume val t : Type0

[@(expect_failure [19])]
let foo (#e:eff_tag) (x:Ghost.erased t) : eff e t = (gtot_to_eff #(Ghost.erased t) #(fun _ -> t) Ghost.reveal) x


val bug : #t:Type0 -> (x:Ghost.erased t) -> Tot (y:t{y == Ghost.reveal x})

[@(expect_failure [19])]
let bug #t x =
  let foo #e (x:Ghost.erased t) : eff e t = (gtot_to_eff Ghost.reveal) x in
  eff_to_tot (foo x)
