module Bug2535

open FStar.Tactics

assume val some_f : unit -> int

let lem (s: list int) : bool =
  _ by (
    let t0 = quote (some_f () = 0) in
    let t1 = norm_term_env (cur_env ()) [nbe] t0 in
    exact t1
  )
