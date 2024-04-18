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
  | _ -> fail "must failed"

let test1 () = assert True by (
  let g = cur_env () in
  let goal = `(cc (list (list int))) in
  let goal, _ = must <| tc_term g goal in
  let u = must <| universe_of g goal in
  let w = must <| call_subtac g FStar.Tactics.Typeclasses.tcresolve u goal in
  dump ("witness = " ^ term_to_string w)
)
