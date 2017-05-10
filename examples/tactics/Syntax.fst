module Syntax

open FStar.Tactics

let quote_sanity_check =
    assert_by_tactic (t <-- quote (1+1);
                      match inspect t with
                      | Tv_App _ _ -> return ()
                      | _ -> fail ("oops!: " ^ term_to_string t)) True

// should reduce to 30
let test1 = assert_by_tactic (let _ = pack (Tv_Const (C_Int ((10 + 8) + (3 + 9)))) in
                              return ()) True

let test2 = assert_by_tactic (x <-- quote test1;
                              print ("quote test1 returned = " ^ term_to_string x);;
                              match inspect x with
                              | Tv_FVar fv -> print ("FV: " ^ flatten_name (inspect_fv fv))
                              | _ -> fail "wat") True


let blah' (ff : term -> tactic term) (t : term) =
    print ("GGG Trace: " ^ term_to_string t);;
    print ("GGG Trace2: " ^ formula_to_string (term_as_formula t));;
    tv <-- (match inspect t with
            | Tv_Var b -> print ("BVar = " ^ inspect_bv b);;
                          return (Tv_Var b)
            | Tv_FVar f -> print ("FVar = " ^ flatten_name (inspect_fv f));;
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
            | Tv_Const c -> return (Tv_Const c)
            | Tv_Unknown -> return Tv_Unknown);
     return (pack tv)

let blah : term -> tactic term =
    fix1 blah'

let _ = assert_by_tactic (t <-- quote (1+1);
                          print ("t = " ^ term_to_string t);;
                          t <-- blah t;
                          print ("t = " ^ term_to_string t);;
                          return ()
                          ) True

let _ = assert_by_tactic (t <-- quote blah;
                          (match inspect t with
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

let _ = assert_by_tactic (t <-- quote (2 + 3);
                          match term_as_formula t with
                          | Eq _ _ _ -> return ()
                          | _ -> return ();;

                          return ())
                          True

let _ = assert_by_tactic (t <-- quote ((x:int) -> x == 2 /\ False);
                          match term_as_formula t with
                          | Forall _ _ -> return ()
                          | _ -> fail ("This should be a forall: " ^ term_to_string t)) True

let _ = assert_by_tactic (t <-- quote ((y:int) -> (x:int) -> x + 2 == 5);
                          match term_as_formula t with
                          | Implies _ _ -> return ()
                          | f -> fail ("This should be an implication: " ^ formula_to_string f)) True
