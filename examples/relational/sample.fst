(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/st2.fst $LIB/bytes.fst 
  --*)

module Sample
open Comp
open Heap
open Bytes

(* Example for Nik's proposal of sequencing (Email from 04/29/2015) *)

let c0_pfx a = a := 0
let c1_pfx b = b := 1
let equiv_pfx a b = compose2 c0_pfx c1_pfx a b

type injection (#a:Type) (f:a -> Tot a) = (forall x y. f x = f y ==> x = y)
type surjection (#a:Type) (f:a -> Tot a) = (forall y. (exists x. f x = y))
type bijection (#a:Type) (f:a -> Tot a) = injection f /\ surjection f

(* sample two random values into c and d such that they are related by a
  bijection f *)
assume val sample : #a:Type
                    -> f:(a -> Tot a){bijection f}
                    -> ST2 (a * a)
                       (requires (fun _ -> True))
                       (ensures (fun h2' p  h2 -> h2' = h2 /\ fst p = f (snd p)))


let c0_sfx (a, c) = a := !a + c
let c1_sfx (b, d) = b := !b + d
let equiv_sfx a b c d = compose2 c0_sfx c1_sfx (a, c) (b, d)

(* relate the programs
  c0_pfx ; sample ; c0_sfx  and
  c1_pfx ; sample ; c1_sfx  *)
val equiv_seq: a:ref int
               -> b:ref int
               -> ST2 (unit * unit)
                  (requires (fun _ -> True))
                  (ensures (fun _ _ h2 -> sel (fst h2) a = sel (snd h2) b))
let equiv_seq a b = let _ = equiv_pfx a b in
                    let c, d = sample (fun x -> x + 1) in
                    equiv_sfx a b c d


(* Encryption with xor (Example from RF* paper) *)

assume val blocksize : int
type block = b:bytes{length b = blocksize}  
assume val xor : block -> block -> Tot block

let xor_sym = assume(forall a b. xor a b = xor b a) 
let xor_inv = assume(forall a b. xor (xor a b) a = b)
let xor_ass = assume(forall a b c. xor (xor a b) c = xor a (xor b c))
val xor_inj : a:block -> b:block -> c:block 
              -> Lemma 
              (requires (xor a b = xor a c))
              (ensures (b = c))
              [SMTPat (xor a b = xor a c)]
let xor_inj a b c = cut (b2t (xor (xor a b) a = xor (xor a c) a))

let encrypt p k = xor p k 
let decrypt c k = xor c k 

(* keeping this assertion here explicilty because of #284 *)
let test a b  = assert (bijection (fun x -> xor (xor a b) x)) 

val cpa : block 
       -> block
       -> ST2 (block * block) 
            (requires (fun _ -> True))
            (ensures (fun _ p _ -> fst p = snd p))
let cpa a b = let k1, k2 = sample (fun x -> xor (xor a b) x) in 
              compose2 (fun k -> encrypt a k) (fun k -> encrypt b k) k1 k2 
              (* This does not work with eta reduced versions of the function *)
