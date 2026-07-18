module Bug3236

#set-options "--defensive error"

open FStar.Tactics.V2

val fa_cong : unit -> unit
let fa_cong (u1:unit) =
  let do1 (u2:unit) : Tac unit =
    let t = (`()) in
    let l = Cons #term t Nil in
    ()
  in
  ()

val ex_cong : unit -> unit
let ex_cong () =
  let t () : Tac unit =
    admit();
    let [ex] = l_intros () in
    ()
  in
  ()

val is_true : term -> Tac bool
let is_true t =
    begin match term_as_formula' t with
    | True_ -> true
    | x1 -> begin match inspect t with
           | Tv_App l r -> true
           | x2 -> false
           end
    end
