module GRewrite
open FStar.Tactics

(* Tests for the grewrite function *)

let test_grewrite (a b c : int) (l : b == c) =
    assert_by_tactic (liftM2' grewrite (quote b) (quote c);;
                      ql <-- quote l;
                      exact ql;;
                      trivial;;
                      return ()) (a + b == a + c)

let test_grewrite2 (w x y z:int) =
    assert_by_tactic (liftM2' grewrite (quote (z + y)) (quote (y + z));;
                      liftM2' grewrite (quote (x + (y + z))) (quote ((y + z) + x));;
                      liftM2' grewrite (quote (w + ((y + z) + x))) (quote (((y + z) + x) + w)))
                     (w + (x + (z + y)) == (y + z) + (x + w))

let test_grewrite3 (w x y z : int) =
    assert_by_tactic (liftM2' grewrite (quote (1 + 2)) (quote 3);;
                      liftM2' grewrite (quote (3, 3+4)) (quote (3,7)))
                     ((1+2, 3+4) == (5-2, 7+0))

// Rewrites all at once
let test_grewrite4 (f : int -> int -> int) (w : int) =
    assert_by_tactic (implies_intro;;
                      seq (liftM2' grewrite (quote (f w w)) (quote w))
                          revert)
                     (f w w == w ==> f (f w w) (f w w) == w)

let test_grewrite5 (n m : int) (p1 : n == m)
                               (p2 : (fun x -> x + n) == (fun x -> m + x)) =
    assert_by_tactic (liftM2' grewrite (quote n) (quote m);;
                      liftM1' exact (quote p1);;
                      trivial)
                     ((fun x -> x + n) == (fun x -> m + x))

let guard (b:bool) : tactic unit =
    if b then return ()
         else fail "failed guard"

// Sanity checks for term_eq
let test_term_eq (m n o : int) =
    assert_by_tactic (liftM1' guard (liftM2' term_eq (quote n) (quote n))) True;
    assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (n+m)) (quote (n+m)))) True;

    // These fail because of uvars present in types (of the arguments)
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun x -> n)) (quote (fun x -> n)))) True;
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun n -> n)) (quote (fun n -> n)))) True;
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun m -> m)) (quote (fun n -> n)))) True;
    // This fails because of the annotated return types turn out different in each side. Should fix
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun m -> m + o)) (quote (fun n -> n + o)))) True;
    ()
