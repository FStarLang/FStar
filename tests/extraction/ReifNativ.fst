module ReifNativ

#set-options "--warn_error -272" // top-level effect

let repr (a:Type) : Type0 = int -> Dv a

let return (a:Type) (x:a) : Tot (repr a) =
  fun _ -> x

let bind a b (x:repr a) (f:a -> Tot (repr b)) : Tot (repr b) =
  fun _ ->
    let v = x 0 in
    f v 0

[@@ top_level_effect; primitive_extraction]
total
reifiable
effect {
  EE (a:Type)
  with { repr; return; bind; }
}

let lift (a:Type) (w : pure_wp a) (f : unit -> PURE a w) : repr a =
  fun _ -> admit(); f ()

sub_effect PURE ~> EE = lift

let test () : EE bool =
  true

let test2 () : EE bool =
  let b1 = test () in
  let b2 = test () in
  b1 && b2

let top : int =
  if test2 () then
    1
  else
    0

(* Reifying is ghost *)
[@@expect_failure [34]]
let top2 () : Tot (repr bool) = reify (test2 ())

let top3 () : GTot (repr bool) = reify (test2 ())
