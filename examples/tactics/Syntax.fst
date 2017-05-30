module Syntax

open FStar.Tactics
open FStar.Reflection.Arith

let quote_sanity_check =
    assert_by_tactic (t <-- quote (1+1);
                      match inspect t with
                      | Tv_App _ _ -> return ()
                      | _ -> fail ("oops!: " ^ term_to_string t)) True

// should reduce to 30
let test1 = assert_by_tactic (let _ = pack (Tv_Const (C_Int ((10 + 8) + (3 + 9)))) in
                              return ()) True

let test2 = assert_by_tactic (x <-- quote test1;
                              match inspect x with
                              | Tv_FVar fv -> return ()
                              | _ -> fail "wat") True


let blah' (ff : term -> tactic term) (t : term) =
    tv <-- (match inspect t with
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
            | Tv_Const c -> return (Tv_Const c)
            | Tv_Unknown -> return Tv_Unknown);
     return (pack tv)

let blah : term -> tactic term =
    fix1 blah'

let _ = assert_by_tactic (t <-- quote (1+1);
                          t' <-- blah t;
                          if term_eq t t'
                          then return ()
                          else fail "blah not an identity?"
                          ) True

let _ = assert_by_tactic (t <-- quote blah;
                          (match inspect t with
                          | Tv_FVar fv ->
                              return ()
                          | _ ->
                              fail "Free variable did not return an FV")) True

let _ = assert_by_tactic (t <-- quote (5 == 2 + 3);
                          match term_as_formula' t with
                          | Comp Eq _ _ _ -> return ()
                          | _ -> fail "term_as_formula did not recognize an equality"
                          )
                          True

let _ = assert_by_tactic (t <-- quote ((fun (x:int) -> x) 5);
                          match inspect t with
                          | Tv_App _ _ -> return ()
                          | Tv_Const (C_Int 5) -> fail "Quoted term got reduced!"
                          | _ -> fail "What?"
                          ) True

let _ = assert_by_tactic (t <-- quote ((x:int) -> x == 2 /\ False);
                          match term_as_formula' t with
                          | Forall _ _ -> return ()
                          | _ -> fail ("This should be a forall: " ^ term_to_string t)) True

// The implicit type argument for eq2 (==) mentions x and y, so this is not seen as an implication...
// In detail, initially the type is `?u y x` for some unification variable `?u`, and unification
// then resolves it to `(fun _ _ -> int) y x`, so `y` and `x` are still free.
//
// Tweaking inference to do some normalization could get rid of this, I think..
let _ = assert_by_tactic (t <-- quote ((y:int) -> (x:int) -> x + 2 == 5);
                          match term_as_formula; t with
                          | Implies _ _ -> fail "" // make it fail for now, but this is the wanted result, I think
                          | f -> print ("This should be an implication: " ^ formula_to_string f);;
                                 print "But that's a known issue...";;
                                 return ()
                         ) True

let arith_test1 =
    let bind = FStar.Tactics.bind in
    let fail = FStar.Tactics.fail in
    assert_by_tactic (t <-- quote (1 + 2);
                             match run_tm (is_arith_expr t) with
                             | Inr (Plus (Lit 1) (Lit 2)) -> print "alright!"
                             | Inr _ -> fail "different thing"
                             | Inl s -> fail ("oops: " ^ s))
                            True

let arith_test2 (x : int) =
    let bind = FStar.Tactics.bind in
    let fail = FStar.Tactics.fail in
    assert_by_tactic (t <-- quote (x + x);
                             match run_tm (is_arith_expr t) with
                             | Inr (Plus (Atom 0 _) (Atom 0 _)) -> print "alright!"
                             | Inr _ -> fail "different thing"
                             | Inl s -> fail ("oops: " ^ s))
                            True
