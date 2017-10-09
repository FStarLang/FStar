module Syntax

open FStar.Tactics
open FStar.Reflection.Arith

let quote_sanity_check =
    assert_by_tactic True
                     (t <-- quote (1+1);
                      match inspect t with
                      | Tv_App _ _ -> return ()
                      | _ -> fail ("oops!: " ^ term_to_string t))

let goal_sanity_check =
    assert_by_tactic (True /\ True)
                     (g <-- cur_goal;
                      match term_as_formula g with
                      | And _ _ -> return ()
                      | _ -> fail ("oops!: " ^ term_to_string g))

// should reduce to 30
let test1 = assert_by_tactic True (let _ = pack (Tv_Const (C_Int ((10 + 8) + (3 + 9)))) in return ())

let test2 = assert_by_tactic True
                             (x <-- quote test1;
                              match inspect x with
                              | Tv_FVar fv -> return ()
                              | _ -> fail "wat")


let rec blah  (t : term) =
    tv <-- (match inspect t with
            | Tv_Var b -> return (Tv_Var b)
            | Tv_FVar f -> return (Tv_FVar f)
            | Tv_App l (r, q) -> l <-- blah l;
                                 r <-- blah r;
                                 return (Tv_App l (r, q))
            | Tv_Abs b t -> t <-- blah t;
                            return (Tv_Abs b t)
            | Tv_Arrow b t -> t <-- blah t;
                              return (Tv_Arrow b t)
            | Tv_Refine b t -> t <-- blah t;
                               return (Tv_Refine b t)
            | Tv_Type u -> return (Tv_Type ())
            | Tv_Const c -> return (Tv_Const c)
            | Tv_Uvar u t -> return (Tv_Uvar u t)
            | Tv_Let b t1 t2 -> return (Tv_Let b t1 t2)
            | Tv_Match t brs -> return (Tv_Match t brs)
            | Tv_Unknown -> return Tv_Unknown);
     return (pack tv)

let _ = assert_by_tactic True
                         (t <-- quote (1+1);
                          t' <-- blah t;
                          if term_eq t t'
                          then return ()
                          else fail "blah not an identity?"
                          )

let _ = assert_by_tactic True
                         (t <-- quote blah;
                          (match inspect t with
                          | Tv_FVar fv ->
                              return ()
                          | _ ->
                              fail "Free variable did not return an FV"))

let _ = assert_by_tactic True
                         (t <-- quote (5 == 2 + 3);
                          match term_as_formula' t with
                          | Comp Eq _ _ _ -> return ()
                          | _ -> fail "term_as_formula did not recognize an equality"
                          )

let _ = assert_by_tactic True
                         (t <-- quote ((fun (x:int) -> x) 5);
                          match inspect t with
                          | Tv_App _ _ -> return ()
                          | Tv_Const (C_Int 5) -> fail "Quoted term got reduced!"
                          | _ -> fail "What?"
                          )

let _ = assert_by_tactic True
                         (t <-- quote ((x:int) -> x == 2 /\ False);
                          match term_as_formula' t with
                          | Forall _ _ -> return ()
                          | _ -> fail ("This should be a forall: " ^ term_to_string t))

// The implicit type argument for eq2 (==) mentions x and y, so this is not seen as an implication...
// In detail, initially the type is `?u y x` for some unification variable `?u`, and unification
// then resolves it to `(fun _ _ -> int) y x`, so `y` and `x` are still free.
//
// Tweaking inference to do some normalization could get rid of this, I think..
let _ = assert_by_tactic True
                         (t <-- quote ((y:int) -> (x:int) -> x + 2 == 5);
                          match term_as_formula t with
                          | Implies _ _ -> fail "" // make it fail for now, but this is the wanted result, I think
                          | f -> print ("This should be an implication: " ^ formula_to_string f);;
                                 print "But that's a known issue...";;
                                 return ()
                         )

let arith_test1 =
    let bind = FStar.Tactics.bind in
    let fail = FStar.Tactics.fail in
    assert_by_tactic True
                    (t <-- quote (1 + 2);
                             match run_tm (is_arith_expr t) with
                             | Inr (Plus (Lit 1) (Lit 2)) -> print "alright!"
                             | Inr _ -> fail "different thing"
                             | Inl s -> fail ("oops: " ^ s))

let arith_test2 (x : int) =
    let bind = FStar.Tactics.bind in
    let fail = FStar.Tactics.fail in
    assert_by_tactic True
                    (t <-- quote (x + x);
                             match run_tm (is_arith_expr t) with
                             | Inr (Plus (Atom 0 _) (Atom 0 _)) -> print "alright!"
                             | Inr _ -> fail "different thing"
                             | Inl s -> fail ("oops: " ^ s))

let _ = assert_by_tactic True
            (t <-- quote (let x = 2 in x + 6);
             match inspect t with
             | Tv_Let b t1 t2 -> (
                print ("b = " ^ binder_to_string b);;
                print ("t1 = " ^ term_to_string t1);;
                print ("t2 = " ^ term_to_string t2)
                )
             | _ -> fail "wat?"
             )
