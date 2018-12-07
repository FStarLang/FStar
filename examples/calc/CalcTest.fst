module CalcTest

open FStar.Mul
open FStar.Calc

let calc0 (a : pos) : Lemma (a + a > a) =
  calc (>) {
    a + a;
    == { () }
    2 * a;
    > { () }
    a;
  }

(* The lemma above, desugared. F* eta-expands and ascribes <: Type in
 * order to treat boolean operators such as (>) as `relation`s. *)
let calc0_desugared (a : pos) : Lemma (a + a > a) =
  calc_finish (fun x y -> (>) x y <: Type) (fun () ->
    calc_step (fun x y -> (>) x y <: Type) a (fun () ->
      calc_step (fun x y -> (==) x y <: Type) (2 * a) (fun () ->
        calc_init (a + a)
      ) (fun () -> ())
    ) (fun () -> ())
  )

let check a = assert_norm (calc0 a == calc0_desugared a)
  
let calc1 (a b c d e : int)
          (h1 : unit -> Lemma (a * (c + 1) = 24))
          (h2 : unit -> Lemma (b + d == 25))
       : Lemma (a + b + a * c + d - (e - e) > 30) =
  calc (>) {
    a + b + a * c + d - (e - e);
   == { (* reorder, e-e = 0 *) }
    a + a * c + b + d;
   == { (* distributivity *) }
    a * (c + 1) + b + d;
   == { h1 () }
    24 + b + d;
   == { h2 () }
    24 + 25;
   == { }
    49;
   > { }
    30;
  }

let test_ge () =
  calc (>=) {
    10;
   >= {}
    9;
   >= {}
    8;
   == {}
    4+4;
   >= {}
    0;
  }

let test_erase () =
  let x = 1 in
  calc (>=) {
    10;
   >= {}
    9;
   >= {}
    8;
   == {}
    4+4;
   >= {}
    0;
  };
  let y = 41 in
  x + y

let test_gt () =
  calc (>) {
    10;
   >= {}
    9;
   > { () }
    8;
   == {}
    4+4;
   >= {}
    0;
  }

[@(expect_failure [19])]
let test_gt_lt () =
  calc (>=) {
    10;
   >= {}
    9;
   <= {}
    11;
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
