module CommuteMatch

open FStar.Tactics

type t = | X | Y

assume val x : t
assume val f : int -> int
assume val g : int -> int

let test1 () =
  assert ((match x with | X -> f | Y -> g) 42 == (match x with | X -> f 42 | Y -> g 42)) by begin
    dump "1";
    t_commute_applied_match ();
    dump "2"
  end

let rwtac () : Tac unit =
  pointwise (fun () ->
    try t_commute_applied_match ()
    with | _ -> trefl ());
  trefl ()

[@@postprocess_with rwtac]
let rw_test () =
  (match x with | X -> f | _ -> g) 42
