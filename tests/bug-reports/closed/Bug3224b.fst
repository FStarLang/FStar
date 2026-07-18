module Bug3224b

open FStar.Tactics.V2

noeq
type vcode = {
    t : Type u#2;
    up : t -> int;
}

let _ = assert True by (
  let g = cur_env () in
  let u = tc_term g (`(fun projectee -> match projectee as proj_ret returns Mkvcode?.t proj_ret -> int with | Mkvcode t up -> up)) in
  match u with
  | Some u, _ ->
    dump "ok"
  | _, [] ->
    dump "fail and no issue?"
  | _, i::is ->
    dump (FStar.Issue.render_issue i)
)
