module FStar.InteractiveHelpers.Tutorial.Definitions

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module B = LowStar.Buffer

open FStar.List
open FStar.Tactics
open FStar.Mul

/// Some dummy functions used for the tutorial for the FStar.FStar.InteractiveHelpers functions

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"

let f1 (n : int) (m : nat) : Pure nat (requires (n > 3)) (ensures (fun _ -> True)) =
  m % (n - 3)

let f2 (x y : nat) :
  Pure (z:nat{z >= 8}) (requires True) (ensures (fun z -> z % 2 = 0)) =
  2 * (x + y) + 8

let f3 (x : nat) : nat =
  2 * x

let f4 (n : int{n % 2 = 0}) : Tot (n':int{n' % 2 = 0}) =
  n + 2

assume val sf1 (r : B.buffer int) :
  ST.Stack int
  (requires (fun _ -> True))
  (ensures (fun h0 n h1 ->
    B.live h0 r /\ B.as_seq h0 r == B.as_seq h1 r /\
    n = List.Tot.fold_left (fun x y -> x + y) 0 (Seq.seq_to_list (B.as_seq h0 r))))

assume val sf2 (l : list int) :
  ST.ST (B.buffer int)
  (requires (fun _ -> True))
  (ensures (fun h0 r h1 ->
    B.live h0 r /\
    B.as_seq h1 r == Seq.seq_of_list l))

assume val sf3 : b:B.buffer nat ->
                    ST.Stack unit (requires (fun h0 -> B.live h0 b))
                                  (ensures (fun h0 r h1 -> B.live h1 b))

let pred1 (x y z : nat) = True
let pred2 (x y z : nat) = True
let pred3 (x y z : nat) = True
let pred4 (x y z : nat) = True
let pred5 (x y z : nat) = True
let pred6 (x y z : nat) = True

let lpred1 (l1 l2 : Seq.seq int) = True
let lpred2 (l1 l2 : Seq.seq int) = True
let lpred3 (l1 l2 : Seq.seq int) = True

let spred1 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
let spred2 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
let spred3 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
let spred4 (h : HS.mem) (r1 r2 r3 : B.buffer int) = True
