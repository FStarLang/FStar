module CallSubtac

open FStar.Tactics.V2

class cc (a:Type) = {
  dummy : a -> a;
}

instance cc_int : cc int = {
  dummy = (fun x -> x);
}

instance cc_bool : cc bool = {
  dummy = (fun x -> x);
}

instance cc_list (a:Type) (_ : cc a) : cc (list a) = {
  dummy = (fun x -> x);
}

let must #a (r : ret_t a) : Tac a =
  match r with
  | Some x, _ -> x
  | None, issues ->
    // log_issues issues;
    fail "must failed"

let test1 () = assert True by (
  let g = cur_env () in
  let goal = `(cc (list (list int))) in
  let goal, _ = must <| tc_term g goal in
  let u = must <| universe_of g goal in
  let w = must <| call_subtac g FStar.Tactics.Typeclasses.tcresolve u goal in
  dump ("witness = " ^ term_to_string w)
)

(* This is the same example, but it starts from the *term* for tcresolve,
unembeds it into an actual Tac function, and calls it. *)
let test2 () = assert True by (
  let g = cur_env () in
  let goal = `(cc (list (list int))) in
  let goal, _ = must <| tc_term g goal in
  let u = must <| universe_of g goal in
  let tac_tm = `FStar.Tactics.Typeclasses.tcresolve in
  let tac_f : unit -> Tac unit = unquote tac_tm in
  let w = must <| call_subtac g tac_f u goal in
  dump ("witness = " ^ term_to_string w)
)

let test3 () = assert True by (
  let g = cur_env () in
  let goal = `(cc (list (list int))) in
  let goal, _ = must <| tc_term g goal in
  let u = must <| universe_of g goal in
  let tac_tm = `FStar.Tactics.Typeclasses.tcresolve in
  let w = must <| call_subtac_tm g tac_tm u goal in
  dump ("witness = " ^ term_to_string w)
)
