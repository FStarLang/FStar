(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/st2.fst $LIB/bytes.fst 
  --*)

module Bijection

type injection (#a:Type) (#b:Type) (f:a -> Tot b) = (forall x y. f x = f y ==> x = y)
type surjection (#a:Type)(#b:Type) (f:a -> Tot b) = (forall y. (exists x. f x = y))
type bijection (#a:Type) (#b:Type) (f:a -> Tot b) = injection f /\ surjection f
type bij (#a:Type) (#b:Type) = f:(a -> Tot b){bijection f}
opaque type inverses (#a:Type) (#b:Type) (f:a -> Tot b) (g:b -> Tot a) =
   (forall y. f (g y) = y) /\
   (forall x. g (f x) = x)
val lemma_inverses_bij: a:Type -> b:Type -> f:(a -> Tot b) -> g:(b -> Tot a) ->
  Lemma (requires (inverses f g))
        (ensures (bijection f))
let lemma_inverses_bij f g = ()

module Sample
open Bijection

(* sample two random values such that they are related by a bijection f *)
assume val sample : #a:Type -> #b:Type
                    -> f:(a -> Tot b){bijection f}
                    -> Tot (r:(a * b) {snd r = f (fst r)})


(* Simple example for Nik's proposal of sequencing (Email from 04/29/2015) *)
module Example1
open Heap
open Comp
open Sample
open Bijection

let c0_pfx a = a := 0
let c1_pfx b = b := 1
let equiv_pfx a b = compose2 c0_pfx c1_pfx a b

let c0_sfx (a, c) = a := !a + c
let c1_sfx (b, d) = b := !b + d
let equiv_sfx a b c d = compose2 c0_sfx c1_sfx (a, c) (b, d)

let dec x = x - 1
let inc x = x + 1

(* relate the programs
  c0_pfx ; sample ; c0_sfx  and
  c1_pfx ; sample ; c1_sfx  *)
val equiv_seq: a:ref int
               -> b:ref int
               -> ST2 (unit * unit)
                  (requires (fun _ -> True))
                  (ensures (fun _ _ h2 -> sel (fst h2) a = sel (snd h2) b))
let equiv_seq a b = let _ = equiv_pfx a b in
                    cut (inverses dec inc);
                    let c, d = sample (fun x -> dec x) in
                    equiv_sfx a b c d


module Xor
open Bytes
assume val blocksize : int
type block = b:bytes{length b = blocksize}  
assume val xor : block -> block -> Tot block

assume Xor_sym : (forall a b.{:pattern (xor a b)} xor a b = xor b a) 
assume Xor_inv : (forall a b.{:pattern (xor a b)}xor (xor a b) a = b)
assume Xor_ass : (forall a b c.{:pattern (xor (xor a b) c); (xor a (xor b c))} xor (xor a b) c = xor a (xor b c))
val xor_inj : a:block -> b:block -> c:block 
              -> Lemma 
              (requires (xor a b = xor a c))
              (ensures (b = c))
              [SMTPat (xor a b = xor a c)]
let xor_inj a b c = cut (b2t (xor (xor a b) a = xor (xor a c) a))


(* Encryption with xor (Example from RF* paper) *)
module Example2
open Heap
open Comp
open Sample
open Bijection
open Xor

let encrypt p k = xor p k 
let decrypt c k = xor c k 

val cpa : block 
       -> block
       -> ST2 (block * block) 
            (requires (fun _ -> True))
            (ensures (fun _ p _ -> fst p = snd p))
let cpa a b = let sample_fun = (fun x -> xor (xor a b) x) in 
              cut (inverses #block #block sample_fun sample_fun);
              let k1, k2 = sample sample_fun in 
              compose2 (fun k -> encrypt a k) (fun k -> encrypt b k) k1 k2 
              (* This does not work with eta reduced versions of the function *)

(* As this example does not use state, we actually don't need the ST2 monad *)
val cpa' : block 
        -> block
        -> Tot (r:(block * block){fst r = snd r})
let cpa' a b = let sample_fun = (fun x -> xor (xor a b) x) in 
              cut (inverses #block #block sample_fun sample_fun);
              let k1, k2 = sample sample_fun in 
              encrypt a k1, encrypt b k2
              (* This does not work with eta reduced versions of the function *)
