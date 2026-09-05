module Bug2169

open FStar.Tactics.V2
open FStar.List.Tot

(* The nondeterminism monad, without the WP index. *)
let repr (a:Type u#a) : Type u#a = list a

let return (a:Type) (x:a) : repr a = [x]

let bind (a b:Type) (l:repr a) (f:a -> repr b) : repr b = concatMap f l

total
reifiable
reflectable
effect {
  ND with { repr; return; bind }
}

let lift_pure_nd (a:Type) (f:unit -> a) : repr a = [f ()]

sub_effect Tot ~> ND = lift_pure_nd

let g (x:int) : option int = Some x

let wrap (f:int -> ND unit) (x':int) : ND unit =
  match g x' with
  | Some x -> f x
  | None -> f 4

assume val f : int -> ND unit

let rewrite_inside_reify (x y:int) (_:squash (x == y)) =
  assert (reify (f x) == reify (f y))
    by (rewrite_eqs_from_context ())
