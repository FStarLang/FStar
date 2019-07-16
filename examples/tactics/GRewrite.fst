(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module GRewrite
open FStar.Tactics

(* Tests for the grewrite function *)

let test_grewrite (a b c : int) (l : squash (b == c)) =
    assert (a + b == a + c)
        by (grewrite (quote b) (quote c);
            trivial ();
            exact (quote l))

let test_grewrite2 (w x y z:int) =
    assert (w + (x + (z + y)) == (y + z) + (x + w))
        by (grewrite (quote (z + y)) (quote (y + z));
            grewrite (quote (x + (y + z))) (quote ((y + z) + x));
            grewrite (quote (w + ((y + z) + x))) (quote (((y + z) + x) + w)))

let test_grewrite3 (w x y z : int) =
    assert ((1+2, 3+4) == (5-2, 7+0))
        by (grewrite (quote (1 + 2)) (quote 3);
            grewrite (quote (3, 3+4)) (quote (3,7)))

// Rewrites all at once
let test_grewrite4 (f : int -> int -> int) (w : int) =
    assert (f w w == w ==> f (f w w) (f w w) == w)
        by (let _ = implies_intro () in
            seq (fun () -> grewrite (quote (f w w)) (quote w))
                l_revert)

let test_grewrite5 (n m : int) (p1 : squash (n == m))
                               (p2 : (fun x -> x + n) == (fun x -> m + x)) =
    assert ((fun x -> x + n) == (fun x -> m + x))
        by (grewrite (quote n) (quote m);
            flip ();
            exact (quote p1))

let guard (b:bool) : Tac unit =
    if b then ()
         else fail "failed guard"

// Sanity checks for term_eq
let test_term_eq (m n o : int) =
    assert True by (guard (term_eq (quote n) (quote n)));
    assert True by (guard (term_eq (quote (n+m)) (quote (n+m))));

    // These fail because of uvars present in types (of the arguments)
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun x -> n)) (quote (fun x -> n)))) True;
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun n -> n)) (quote (fun n -> n)))) True;
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun m -> m)) (quote (fun n -> n)))) True;
    // This fails because of the annotated return types turn out different in each side. Should fix
    //assert_by_tactic (liftM1' guard (liftM2' term_eq (quote (fun m -> m + o)) (quote (fun n -> n + o)))) True;
    ()
