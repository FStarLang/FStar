module GRewrite
open FStar.Tactics

(* Tests for the grewrite function *)

let test_grewrite (a b c : int) =
    let l : (b == c) = magic() in
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

// Should rewrite all at once, and does, but we get a weird hard query
let test_grewrite4 (f : int -> int -> int) (w : int) =
    assert_by_tactic (implies_intro;;
                      seq (liftM2' grewrite (quote (f w w)) (quote w))
                          revert)
                     (f w w == w ==> f (f w w) (f w w) == w)
