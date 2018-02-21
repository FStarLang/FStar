module Bug1346
open FStar.Tactics

assume val p1 (x:int) : Type0

let my_cut (t:tactic term) : tactic unit =
    qq <-- quote_lid ["FStar";"Tactics";"Derived";"__cut"];
    t <-- t ;
    let tt = pack (Tv_App qq (t, Q_Explicit)) in
    apply (return tt)

assume val aug : (unit -> Type0) -> Type0
let test (p:(unit -> Type0)) (q:(unit -> Type0))
   = assert_by_tactic
            (p == q ==>
             aug p ==>
             aug q)
             ( eq <-- implies_intro ;
               h <-- implies_intro ;
               dump "A" ;;
               my_cut (return (type_of_binder h)) ;;
               dump "B" ;;
               rewrite eq;;
               norm [] ;;
               dump "C" ;;
               hh <-- intro ;
               apply (quote FStar.Squash.return_squash) ;;
               dump "D" ;;               
               exact (return (pack (Tv_Var hh))) ;; //USED TO FAIL
               exact (return (pack (Tv_Var h))))

let t1 : tactic unit =
  x <-- forall_intro;
  px <-- implies_intro;
  y <-- forall_intro;
  eq_yx <-- implies_intro;
  dump "Before";;
  rewrite eq_yx;;
  dump "***************After rewrite";;
  squash_intro;; 
  dump "***************After squash" ;;
  exact (return (pack (Tv_Var px)));;
  dump "End"

let foo1 () =
    assert_by_tactic
      (
          (forall (x:int). p1 2 ==> (forall (y:int). y == 1 ==> p1 2)) // SUCCEEDS
          ) t1;
    ()

let foo2 () =
    assert_by_tactic
      (
          (forall (x:int). p1 x ==> (forall (y:int). y == 1 ==> p1 x)) // USED TO FAIL
          ) t1;
    ()
