module PulseBug100

open FStar.Tactics.V2

let _ = assert True by begin
  let g = top_env () in
  match t_check_equiv false true g (`nat) (`int) with
  | None, _ -> ()
  | Some _, _ ->
    fail "no! nat is not int!"
end

let _ = assert True by begin
  let g = top_env () in
  match t_check_equiv false true g (`int) (`nat) with
  | None, _ -> ()
  | Some _, _ ->
    fail "no! nat is not int!"
end