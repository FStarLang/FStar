module LayeredEffects

#set-options "--max_fuel 0 --max_ifuel 0"

open LowStar.STExn

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

