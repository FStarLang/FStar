module Change

open FStar.Tactics

let id #a (x:a) : a = x

// [@plugin]
// let tau1 = fun () -> dump "0";
//                        change_sq (`(eq2 #int (id #int 5) 5));
//                        dump "1"
// let _ = assert_by_tactic (id 5 == 5) tau1

let rec is_five (x: nat) =
  match x with
  | 5 -> fst ((snd (false, true), false))
  | _ -> is_five (x - 1)

[@plugin]
let tau2 = fun () -> dump "0";
                       change_sq (`(id 5 == (match (is_five 5) with | true -> 5 | false -> 4)));
                       dump "1"
let _ = assert_by_tactic (id 5 == 5) tau2

// [@plugin]
// let tau3 = fun () -> dump "0";
//                        change_sq (`(5 == 5));
//                        dump "1"
// let _ = assert_by_tactic (id 5 == 5) tau3
