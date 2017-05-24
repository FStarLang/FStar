module Syntax

open FStar.Tactics


let test1 = assert_by_tactic (pack (Tv_Const (C_Int ((10 + 8) + (3 + 9))));;
                              return ()) True

let test2 = assert_by_tactic (x <-- quote test1;
                              v <-- inspect x;
                              match v with
                              | Tv_FVar fv -> print ("FV: " ^ flatten_name (inspect_fv fv))
                              | _ -> fail "wat") True


let blah' (ff : term -> tactic term) (t : term) =
    tv <-- inspect t;
    tv <-- (match tv with
           | Tv_Var b -> //print ("BVar = " ^ inspect_bv b);;
                         return (Tv_Var b)
           | Tv_FVar f -> //print ("FVar = " ^ flatten_name (inspect_fv f));;
                          return (Tv_FVar f)
           | Tv_App l r -> l <-- ff l;
                           r <-- ff r;
                           return (Tv_App l r)
           | Tv_Abs b t -> t <-- ff t;
                           return (Tv_Abs b t)
           | Tv_Arrow b t -> t <-- ff t;
                             return (Tv_Arrow b t)
           | Tv_Refine b t -> t <-- ff t;
                              return (Tv_Refine b t)
           | Tv_Type u -> return (Tv_Type ())
           | Tv_Const c -> return (Tv_Const c));
     pack tv

let blah : term -> tactic term =
    fix1 blah'

let _ = assert_by_tactic (t <-- quote (1+1);
                          s <-- term_to_string t; print ("t = " ^ s);;
                          t <-- blah t;
                          s <-- term_to_string t; print ("t = " ^ s);;
                          return ()
                          ) True

let _ = assert_by_tactic (t <-- quote blah;
                          tv <-- inspect t;
                          (match tv with
                          | Tv_FVar fv ->
                              print (flatten_name (inspect_fv fv));;
                              return ()
                          | _ ->
                              fail "wat")) True

let _ = assert_by_tactic (print "GGG 1";;
                          t <-- quote (fun (x y x : int) -> y + x);
                          print "GGG 2";;
                          blah t;;
                          print "GGG 3";;
                          return ()) True
