module Bug2515

open FStar.Tactics

let match_term (t: term) : Tac term =
    match t with
    | Tv_App fn' arg -> t
    | _ -> t

let go  (t: term) : Tac unit =
  let t' = norm_term_env (cur_env ()) [delta] t in
  ignore (visit_tm match_term t')

assume
val h : int

let lem1 (x: int)
  : Lemma (ensures True)
    by (go (quote (x == h)))
  = ()
