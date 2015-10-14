(*--build-config
    options:--admit_fsi Set --z3timeout 10;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst  stack.fst listset.fst
    ghost.fst located.fst lref.fst stackAndHeap.fst sst.fst rstWhile.fst seq.fsi seq.fst word.fst
  --*)

(*Why is MD5 so? Why did its designer(s) think
  it was a good way to convolute bits?
  Is there a principle behind its design? or just random convolutery?
  *)
module MD5Common
open FStar.Regions.RSTWhile
open StackAndHeap  open FStar.Regions.Heap  open FStar.Regions.Located
open FStar.Regions.RST
open MVector
open Heap
open Set
open MachineWord

(*http://rosettacode.org/wiki/MD5/Implementation#Haskell
 While the version in Haskell and other higher order languages
is elegant, they do not seem to be memory efficient.
For example, mapping 64-way in parallel is unnceccesary and we need
only 4 accumulators at any given time
*)

val funF : word -> word -> word -> Tot word
let funF x y z = bitwiseOr (bitwiseAnd x y) (bitwiseAnd (complement x)  z)

(*should these functions also implemented in imperative style?*)
val funG : word -> word -> word -> Tot word
let funG x y z = bitwiseOr (bitwiseAnd x z) (bitwiseAnd (complement z)  y)

val funH : word -> word -> word -> Tot word
let funH x y z =  bitwiseXOR (bitwiseXOR x y) z

val funI : word -> word -> word -> Tot word
let funI x y z =  bitwiseXOR y (bitwiseAnd (complement z) x)


val idxF  : n:nat{n<64} -> Tot (n:nat{n<16})
let idxF x = x % 16

val idxG  : n:nat{n<64} -> Tot (n:nat{n<16})
let idxG i = (5 * i + 1) % 16

val idxH  : n:nat{n<64} -> Tot (n:nat{n<16})
let idxH i = (3 * i + 5) % 16

val idxI  : n:nat{n<64} -> Tot (n:nat{n<16})
let idxI i = (7 * i) % 16


val  funFGHI : n:nat{n<64} -> word -> word -> word -> Tot word
let funFGHI n =
  match (n / 16) with
  | 0 -> (assert (n<16)); funF
  | 1 -> (assert (16<=n/\n<32)); funG
  | 2 -> (assert (32<=n/\n<48)); funH
  | 3 -> (assert (48<=n/\n<64)); funI


val  idx : n:nat{n<64} -> n:nat{n<64} -> Tot (n:nat{n<16})
let idx n =
  match (n / 16) with
  | 0 -> (assert (n<16)); idxF
  | 1 -> (assert (16<=n/\n<32)); idxG
  | 2 -> (assert (32<=n/\n<48)); idxH
  | 3 -> (assert (48<=n/\n<64)); idxI



let rotValues : l:(list (n:nat{n<32}))
(*{List.length l=16} BUG?*)
 =

[7; 12; 17; 22;     5; 9; 14; 20;    4; 11; 16; 23;    6; 10; 15; 21]

(*#set-options "--initial_fuel 0 --max_fuel 1000 --initial_ifuel 0 --max_ifuel 1000"*)


val lenthRotValue : unit ->
  Lemma
      (requires True)
      (ensures (List.length rotValues = 16))
[SMTPat rotValues]
let lenthRotValue u = (admit ())


val nthT : #a:Type -> l:(list a) -> n:nat{n<List.length l} -> Tot a
let rec nthT l n = match l with
h::tl -> if n=0 then h else (nthT tl (n-1))

val rots: n:nat{n<64} -> Tot (n:nat{n<32})
let rots n =
  let row:(n:nat{n<4}) = n/16 in
  let col:(n:nat{n<4}) = n%4 in
  let index:(n:nat{n<16}) = row*4+col in
  nthT rotValues index

(**
floor(abs(sin(i + 1)) × (2 pow 32))
*)
assume val consts: n:nat{n<64} -> Tot word


(*A chunk of 512 bits, or 16 32 bit words.
  MD5 processes messages as these chunk *)


(*How can we make these private to this file
  and not corrupt the global namespace?*)
let iA:(n:nat{n<4})=0
let iB:(n:nat{n<4})=1
let iC:(n:nat{n<4})=2
let iD:(n:nat{n<4})=3

opaque type divides  (divisor :nat) (n:nat) =
exists (k:nat). k*divisor=n


val leastMultipleGeq : n:nat -> div:pos -> Tot (m:nat{divides div m /\ m < n+ div /\ n<=m})
let leastMultipleGeq n div =
let m = (if (n%div = 0) then n else ((div - (n % div)) + n)) in
let ad = (admitP (divides div m /\ m < n+ div /\ n<=m)) in m

(*(div - (n % div)) + n*)
(*(ceil (n/div))*div*)


(*size of the messsage after padding. this function will be used to preallocate
  an array of the right size*)
val psize : n:nat -> Tot (m:nat{divides 16 m /\ (m < n+ 32) /\ (n<=m)})
let psize n =
  let lm = leastMultipleGeq n 16 in
  if ((lm+1) % 16 < 12) then lm else lm+16

open Seq

assume val initAcc : s:(seq word){length s =4}

(*we can tradeoff space for time by not copying the whole thing,
  but allocate only a new array for padding. Perhaps it can also include
  the leftofer from the last complete chunk.
   The MD5 main loop will have to be modified to handle this dichotomy
  of data/chunk location*)
(*pads the input*)
