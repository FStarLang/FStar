module Calc

open FStar.Mul
open FStar.Calc
open FStar.Tactics

let eta (f:'a->'b->bool) x y : Type0 = f x y

(* bad chain *)
[@(expect_failure [19])]
let test_gt_lt_elab () =
  calc_finish (eta (>=))
   (fun () ->
   calc_step (eta (<=)) 11 (fun () ->
    calc_step (eta (>=)) 9 (fun () -> calc_init 10)
        (fun () -> ()))
        (fun () -> ()))

(* bad chain *)
[@(expect_failure [19])]
let test_gt_lt () =
  calc (>=) {
    10;
   >= {}
    9;
   <= {}
    11;
  }

(* bad chain, not refl *)
[@(expect_failure [19])]
let test_singl () =
  calc (<) {
    10;
  }

(* bad chain *)
[@(expect_failure [19])]
let test (x:int) : Lemma True =
  calc (>) {
    x;
    == { }
    x;
  }


[@(expect_failure [19])]
let fail1 () =
  calc (==) {
    1;
   == {}
    2;
   == { admit ()}
    3;
   == { admit () }
    4;
  }

[@(expect_failure [19])]
let fail2 () =
  calc (==) {
    1;
   == { admit () }
    2;
   == {}
    3;
   == { admit () }
    4;
  }

[@(expect_failure [19])]
let fail3 () =
  calc (==) {
    1;
   == { admit () }
    2;
   == { admit () }
    3;
   == {}
    4;
  }

assume val p : prop
assume val q : prop
assume val lem : unit -> Lemma (requires p) (ensures q)

(* checking that the impl intro trick doesn't mess up error messages *)
[@(expect_failure [19])]
let test_impl_elab () =
  calc_finish (==>) (fun () ->
    calc_step (==>) q
      (fun () -> calc_init p)
      (fun () -> calc_push_impl (fun _ -> ()))
  )

[@(expect_failure [19])]
let test_impl () =
  calc (==>) {
    p;
    ==> { () }
    q;
  }

assume val my_lemma (x:int) : Lemma
  (requires false)
  (ensures  true)

[@(expect_failure [19])]
let test_1763_elab (x:int) : Lemma (True) =
  calc_finish (fun x y -> x == y) (fun () ->
    calc_step (fun x y -> x == y) x (fun () ->
     calc_step (fun x y -> x == y) x (fun () ->
      calc_init x)
      (fun () -> my_lemma x))
      (fun () -> ()))

[@(expect_failure [19])]
let test_1763 (x:int) : Lemma (True) =
  calc (==) {
    x;
    == { my_lemma x }
    x;
    == {}
    x;
  }
