module Bug3224a

open FStar.Tactics.V2

noeq
type vcode = {
    t : Type u#2;
    up : t -> int;
}

let x = true
let tt : term = `(Mkvcode?.up)

let _ = assert True by (
  let g = cur_env () in
  set_guard_policy SMTSync;
  // ^ for some reason this is needed for this example to
  // work, but the important bit is that it does not overflow
  // the stack and crash.
  let u = check_equiv g tt (`(match x with | true -> Mkvcode?.up)) in
  match u with
  | Some u, _ ->
    dump "ok"
  | _, [] ->
    dump "fail and no issue?"
  | _, i::is ->
    dump (FStar.Issue.render_issue i)
)
