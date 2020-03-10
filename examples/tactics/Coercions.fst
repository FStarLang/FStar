module Coercions

open FStar.Tactics


let tm () : Tac term = Tv_App (Tv_App (`op_Addition) (`1, Q_Explicit)) (`2, Q_Explicit)

let basic () : Tac int =
  match tm () with
  | Tv_App l _ -> 1
  | _ -> 2

let one () : Tac term =
  match tm () with
  | Tv_App l _ -> begin match l with
                  | Tv_App _ (x, _) -> x
                  | _ -> fail ""
                  end
  | _ -> fail ""

let two () : Tac term =
  match tm () with
  | Tv_App _ (x, _) -> x
  | _ -> fail ""

let _ = assert True by
        (print ("tm = "  ^ term_to_string (tm ()));
         print ("one = " ^ term_to_string (one ()));
         print ("two = " ^ term_to_string (two ()));
         ())

let test_binder_to_term (b : binder) : Tac term = b

//Nested patterns!
(* let test (tm:term_view) : option term = *)
(*   match tm with *)
(*   | Tv_App (Tv_App _ (x, _)) _ -> Some x *)
(*   | _ -> None *)

(* let test2 (tm:term) : option term = *)
(*   match tm with *)
(*   | Tv_App (Tv_App _ (x, _)) _ -> Some x *)
(*   | _ -> None *)
