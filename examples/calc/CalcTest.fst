module CalcTest

open FStar.Mul
open FStar.Calc
open FStar.Preorder

let calc1 (a b c d e : int)
          (h1 : unit -> Lemma (a * (c + 1) = 24))
          (h2 : unit -> Lemma (b + d == 25))
       : Lemma (a + b + a * c + d - (e - e) >= 49) =
  calc (==) {
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
