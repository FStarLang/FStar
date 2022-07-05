module CommuteMatch

open FStar.Tactics

type t = | X | Y

assume val x : t
assume val f : int -> int -> int
assume val g : int -> int -> int

let test1 () =
  assert ((match x with | X -> f | Y -> g) 42 12 == (match x with | X -> f 42 12 | Y -> g 42 12)) by begin
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
  (match x with | X -> f | _ -> g) 42 12

[@@postprocess_with rwtac]
let rw_test2 (b:bool) =
  (if b then f else g) 100 200

open FStar.All

assume val ff : int -> int -> int
assume val gg : int -> int -> int

//#set-options "--debug CommuteMatch --debug_level Extreme,Rel,TacUnify,TacVerbose,2365,2635 --print_implicits --print_full_names --ugly"

[@@postprocess_with rwtac]
let rw_test3 () : int =
  (match x with | X -> ff | _ -> gg) 42 12

[@@postprocess_with rwtac]
let rw_test4 (b:bool) :  ML int =
  f (999 + (((match b with
   | true -> ff
   | false -> gg
   ) <: int -> int -> ML int) 100 200)) 123
