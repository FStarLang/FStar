module Pulse.Typing.Printer
module T = FStar.Tactics
open Pulse.Syntax.Printer
open Pulse.Typing


#push-options "--query_stats --ifuel 1 --z3rlimit_factor 4 --split_queries no"
let rec print_st_typing #g #t #c (d:st_typing g t c)
  : T.Tac string 
  = match d with
    | T_Abs g x q b u body c tt body_typing ->
      Printf.sprintf "(T_Abs ... %s)" (print_st_typing body_typing)
    
    | T_STApp _ _ _ _ _ _ _ _ ->
      "T_STApp"
    
    | T_Return _ _ _ _ _ _ _ _ _ _ _ ->
      "T_Return"

    | T_Lift _ _ _ _ d _ ->
      Printf.sprintf "(T_Lift %s)" (print_st_typing d)

    | T_Bind g e1 e2 c1 c2 b x c d1 _ d2 _ ->
      Printf.sprintf "(T_Bind %s %s)" (print_st_typing d1) (print_st_typing d2)

    | T_TotBind g e1 e2 t1 c2 b x _ d ->
      Printf.sprintf "(T_TotBind %s)" (print_st_typing d)

    | T_Frame g e c frame _ body ->
      Printf.sprintf "(T_Frame %s %s)" (Pulse.Syntax.Printer.term_to_string frame) (print_st_typing body)

    | T_If _ _ _ _ _ _ _ _ _ _ _ ->
      "T_If"

    | T_Match _ _ _ _ _ _ _ _ _ _ ->
      "T_Match"

    | T_Equiv g e c c' d eq ->
      Printf.sprintf "(T_Equiv %s)"
         (print_st_typing d)
    //   Printf.sprintf "(T_Equiv \n\t{%s}\n\t{%s}\n\t %s)"
    //      (Pulse.Syntax.Printer.comp_to_string c)
    //      (Pulse.Syntax.Printer.comp_to_string c')
    //      (print_st_typing d)
        
    | T_IntroPure _ _ _ _ ->
      "T_IntroPure"

    | T_Rewrite _ _ _ _ _ ->
      "T_Rewrite"
      
    | _ -> "<UNK>"