module TcFundepInstArg

(* An argument of an instance that only occurs in the output (here [#p]) is
   determined by the actual output type, so resolution must not fix the
   output before it is known. *)

[@@FStar.Tactics.Typeclasses.fundeps [1]]
class approx (c m : Type) = { rel : c -> m -> prop }

instance approx_int : approx int int = { rel = fun x y -> x == y }

instance approx_fun (d1 d2 c1 c2 : Type) (#p : d2 -> prop)
  {| approx d1 d2, approx c1 c2 |}
  : approx (d1 -> c1) (x:d2{p x} -> c2) = { rel = fun f g -> True }

let t_refined (f : int -> int) (g : (x:int{x > 0}) -> int) : prop = rel f g

let t_unrefined (f : int -> int) (g : int -> int) : prop = rel f g

let t_var (p : int -> prop) (f : int -> int) (g : (x:int{p x}) -> int) : prop = rel f g

let t_poly (#a #ar #b #br : Type) {| approx a ar, approx b br |} (#p : ar -> prop)
  (f : a -> b) (g : (r:ar{p r}) -> br) : prop = rel f g
