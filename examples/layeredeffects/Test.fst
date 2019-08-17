module Test

#set-options "--max_fuel 0 --max_ifuel 0"

open HoareST

assume val f (x:int) : HoareST int (fun _ -> x > 2)  (fun h0 r h1 -> h0 == h1 /\ r == 2)
assume val g (x:int) : HoareST int (fun _ -> x == 2) (fun h0 r h1 -> h0 == h1 /\ r == 3)

let test ()
: HoareST int
  (fun _ -> True)
  (fun h0 r h1 -> r > 2 /\ h0 == h1)
= 3

let test2 ()
: HoareST int
  (fun _ -> True)
  (fun h0 r h1 -> r >= 3 /\ h0 == h1)
= let u = () in
  let x = test u in
  let y = f x in
  g y


assume val f_fail (x:int) : HoareST int (fun _ -> True)  (fun h0 r h1 -> True)

[@expect_failure]
let test_fail ()
: HoareST int
  (fun _ -> True)
  (fun h0 r h1 -> True)
= let y = f 3 in
  y


open HoareST2

assume val f2 (x:int) : HoareST2 int (fun _ -> x > 2) (fun r _ -> r == 2)

// [@expect_failure]
// let test3 ()
// : HoareST2 int
//   (fun _ -> True)
//   (fun _ r -> True)
// = let y = f2 3 in
//   y
