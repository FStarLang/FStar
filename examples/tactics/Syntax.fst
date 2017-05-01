module Syntax

open FStar.Tactics

let blah : term -> tactic term = fix1 (fun ff t ->
    tv <-- inspect t;
    tv <-- (match tv with
           | Tv_Var b -> return (Tv_Var b)
           | Tv_FVar f -> return (Tv_FVar f)
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
    pack tv)

let _ = assert_by_tactic (t <-- quote (1+1);
                          s <-- term_to_string t; print ("t = " ^ s);;
                          t <-- blah t;
                          s <-- term_to_string t; print ("t = " ^ s);;
                          return ()
                          ) (True)
