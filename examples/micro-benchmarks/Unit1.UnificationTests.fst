module Unit1.UnificationTests
assume type t : int -> Type
assume val f: int -> Tot int
assume val g: #x:int -> t (f x) -> Tot unit
let h1 (x: t (f 0)) = g x
let h2 (x: t ((fun x -> f (x - 1)) 1)) = g x

(****** test for unfolding of delta equational symbols begin ******)

type some_enum =
  | X
  | Y

let t_indexed (x:some_enum) =
  match x with
  | X -> nat
  | Y -> int

let t_inst_index = t_indexed X

assume val f_with_implicit (#x:some_enum) (u:t_indexed x) (v:t_indexed x) :t_indexed x

let g_calls_f (u v:t_inst_index) = f_with_implicit u v  //the implicit here is inferred by unfolding t_inst_index, which is delta_equational with some depth (2, i think)

(****** test for unfolding of delta equational symbols end ******)

////////////////////////////////////////////////////////////////////////////////
//Test unfoldings
////////////////////////////////////////////////////////////////////////////////

type width =
  | W1
  | Winfinite
let tt w =
  match w with
  | W1 -> bool
  | Winfinite -> int
let join w1 w2 =
  match w1, w2 with
  | _, Winfinite
  | Winfinite, _ -> Winfinite
  | _ -> w1
let join_types #w1 (_:tt w1) #w2 (_:tt w2) = tt (join w1 w2)
assume val op : #w1:width -> #w2:width -> x:tt w1 -> y:tt w2 -> norm [iota; primops; delta_only [%`join; %`join_types]] (join_types x y)
let unfold_test1(x:tt W1) (y:tt W1) = x `op` (y `op` y)

unfold
let norm_join (#a:Type) (x:a) = norm [iota; primops; delta_only [%`join; %`join_types]] x
assume val op2 : #w1:width -> #w2:width -> x:tt w1 -> y:tt w2 -> norm_join (join_types x y)
let unfold_test2 (x:tt W1) (y:tt W1) = x `op2` (y `op2` y)
