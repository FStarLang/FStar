module GRewrite
open FStar.Tactics

(* Tests for the grewrite function *)

let test_grewrite (a b c : int) (l : squash (b == c)) =
    assert_by_tactic (a + b == a + c)
                     (liftM2' grewrite (quote b) (quote c);;
                      trivial;;
                      exact (quote l);;
                      return ())

let test_grewrite2 (w x y z:int) =
    assert_by_tactic (w + (x + (z + y)) == (y + z) + (x + w))
                     (liftM2' grewrite (quote (z + y)) (quote (y + z));;
                      liftM2' grewrite (quote (x + (y + z))) (quote ((y + z) + x));;
                      liftM2' grewrite (quote (w + ((y + z) + x))) (quote (((y + z) + x) + w)))

let test_grewrite3 (w x y z : int) =
    assert_by_tactic ((1+2, 3+4) == (5-2, 7+0))
                     (liftM2' grewrite (quote (1 + 2)) (quote 3);;
                      liftM2' grewrite (quote (3, 3+4)) (quote (3,7)))

// Rewrites all at once
let test_grewrite4 (f : int -> int -> int) (w : int) =
    assert_by_tactic (f w w == w ==> f (f w w) (f w w) == w)
                     (implies_intro;;
                      seq (liftM2' grewrite (quote (f w w)) (quote w))
                          l_revert)

let test_grewrite5 (n m : int) (p1 : squash (n == m))
                               (p2 : (fun x -> x + n) == (fun x -> m + x)) =
    assert_by_tactic ((fun x -> x + n) == (fun x -> m + x))
                     (liftM2' grewrite (quote n) (quote m);;
                      flip;; exact (quote p1))

let guard (b:bool) : tactic unit =
    if b then return ()
         else fail "failed guard"

// Sanity checks for term_eq
let test_term_eq (m n o : int) =
    assert_by_tactic True (liftM1' guard (liftM2 term_eq (quote n) (quote n)));
    assert_by_tactic True (liftM1' guard (liftM2 term_eq (quote (n+m)) (quote (n+m))));

    // These fail because of uvars present in types (of the arguments)
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun x -> n)) (quote (fun x -> n)))) True;
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun n -> n)) (quote (fun n -> n)))) True;
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun m -> m)) (quote (fun n -> n)))) True;
    // This fails because of the annotated return types turn out different in each side. Should fix
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun m -> m + o)) (quote (fun n -> n + o)))) True;
    ()
