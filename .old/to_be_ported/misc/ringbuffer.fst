(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#monadic(DST, returnTX, bindNoExnTX)
module Array
type seq :: * => *
logic val Index   : seq 'a -> nat -> 'a
logic val Update  : seq 'a -> nat -> 'a -> seq 'a
logic val Const   : nat -> 'a -> seq 'a
logic val Length  : seq 'a -> nat
logic val Slice   : seq 'a -> nat -> nat -> seq 'a
logic val Append  : seq 'a -> seq 'a -> seq 'a
type Equal :: 'a::* => seq 'a => seq 'a => E

assume LengthConst:  forall n v.{:pattern (Length (Const n v))} Length (Const n v) = n 
assume IndexConst:   forall (n:nat) (v:'a) (i:nat). {:pattern (Index (Const n v) i)} (i < n) ==> (Index (Const n v) i = v)
assume LengthUpdate: forall s (i:nat) v. {:pattern (Length (Update s i v))} (i < Length s) ==> Length (Update s i v) = Length s
assume IndexUpdate:  forall s i v (n:nat). {:pattern (Index (Update s i v) n)} (n <= Length s) 
                                      ==>  (if (Eq i n) then (Eq (Index (Update s i v) n) v) else (Eq (Index (Update s i v) n) (Index s n)))
assume LengthSlice:  forall s (i:nat) (j:nat). {:pattern (Length (Slice s i j))} ((i <= j) && (j <= Length s)) ==> ((Sub j i) = (Length (Slice s i j)))
assume IndexSlice:   forall s i j (k:nat). {:pattern (Index (Slice s i j) k)} (k <= Length (Slice s i j)) ==> (Index (Slice s i j) k = Index s (Add i k))
assume LengthAppend: forall s t. {:pattern (Length (Append s t))} Length (Append s t) = (Add (Length s) (Length t))
assume IndexAppend:  forall s t (i:nat). {:pattern (Index (Append s t) i)} 
                                         (if (i < Length s) 
                                          then (Eq (Index (Append s t) i) (Index s i))
                                          else (Eq (Index (Append s t) i) (Index t (Sub i (Length s)))))
assume SeqEquals:    forall s0 s1.{:pattern (Equal s0 s1)} ((Equal s0 s1) 
                                                            <==> ((Length s0 = Length s1)
                                                                  && (forall (i:nat).{:pattern (Index s0 i); (Index s1 i)} (i < Length s0) ==> (Eq (Index s0 i) (Index s1 i)))))
assume Extensional:  forall s t.{:pattern (Equal s t)} Equal s t ==> (s = t)

type array 'a = ref (seq 'a)

val alloc:  n:nat 
         -> v:'a 
         -> Writer (array 'a) 
               TrivialPre
              (Ensures _ (fun h a h' => 
                   (Not (InHeap h a) && h'=UpdHeap h a (Const n v))))
              (Modifies EmptySet)

val index:  a:array 'a 
         -> i:nat
         -> Reader 'a
              (Requires (fun h => (i <= Length (SelHeap h a))))
              (Provides _ (fun h v => (v=(Index (SelHeap h a) i))))
                  
val update: a:array 'a 
         -> i:nat
         -> v:'a 
         -> Writer unit 
              (Requires (fun h => (i < Length (SelHeap h a))))
              (Ensures _ (fun h u h' => (h' = UpdHeap h a (Update (SelHeap h a) i v))))
              (Modifies (Singleton a))
end

module RingBuffer
open Array

type pos = n:nat{n > 0}
type t0 'a = {ghostdata: seq (option 'a);
              data: seq (option 'a);
              size: pos;
              start: nat;
              len: nat}

type Invariant :: _ = fun ('a::*) (x:t0 'a) => 
    ((Length x.data = x.size)
     && (x.start < x.size)
     && (x.len <= x.size)
     && (forall (i:nat). (i < Length x.ghostdata) ==> (Some_is (Index x.ghostdata i)))
     && (if (LTE (Add x.start x.len) x.size)
         then (Equal _ x.ghostdata (Slice x.data x.start (Add x.start x.len)))
         else (Equal _ x.ghostdata (Append (Slice x.data x.start x.size)
                                      (Slice x.data 0 (Sub (Add x.start x.len) x.size))))))
    
type t 'a = x:t0 'a{Invariant _ x}
type T 'a = ref (t 'a)
type Empty :: _ = fun ('a::*) (h:heap) (r:T 'a) => (Equal _ ((SelHeap h r).ghostdata) (Const 0 None))
type Full :: _ = fun ('a::*) (h:heap) (r:T 'a) => (Eq (Length ((SelHeap h r).ghostdata)) ((SelHeap h r).size))
logic val Get : seq (option 'a) -> i:nat -> 'a
define Get_def:forall s i. Get s i = (Some_proj_1 (Index s i))

val create: 'a::* 
         -> n:pos
         -> Writer (T 'a) TrivialPre
              (Ensures _ (fun h (v:T 'a) h' => 
                   (Not(InHeap h v)
                    && Eq ((SelHeap h' v).ghostdata) (Const 0 None)
                    && Eq ((SelHeap h' v).size) n)))
              (Modifies EmptySet)
let create ('a::*) (n:pos) =
  let r:t 'a = {ghostdata=Const 0 None;
                data=Const n None;
                size=n;
                start=0;
                len=0} in
  ref r

val clear: 'a::*
        -> r:T 'a 
        -> Writer unit 
               TrivialPre
               (Ensures _ (fun h u h' => 
                  (Eq ((SelHeap h' r).ghostdata) (Const 0 None)
                   && Eq ((SelHeap h' r).size) ((SelHeap h r).size))))
               (Modifies (Singleton r))
let clear ('a::*) (r:T 'a) =
  let s = !r in 
    r := ({s with len=0; ghostdata=Const 0 None})

val isEmpty: 'a::* 
           -> r:T 'a
           -> Reader bool TrivialPre
               (Provides _ (fun h b => (b=true <==> Empty h r)))
let isEmpty ('a::*) (r:T 'a) = 
  let s = !r in s.len = 0

val head: 'a::*
       -> r:T 'a
       -> Reader 'a
            (Requires (fun h => Not (Empty h r)))
            (Provides _ (fun h a => (a=(Get ((SelHeap h r).ghostdata) 0))))
let head ('a::*) (r:T 'a) =
  let t = !r in
  match Index t.data t.start with
    | Some v -> v
    | None -> unreachable ()

val enqueue: 'a::* 
         -> r:T 'a
         -> v:'a
         -> Writer unit
               (Requires (fun h => (Not(Full h r))))
               (Ensures _ (fun h u h' => 
                    (Equal _ ((SelHeap h' r).ghostdata) (Append ((SelHeap h r).ghostdata) (Const 1 (Some v)))
                     && (Eq ((SelHeap h' r).size) ((SelHeap h r).size)))))
               (Modifies (Singleton r))
let enqueue ('a::*) (r:T 'a) (v:'a) =
  let t = !r in
  let nextEmpty = 
    if (t.start + t.len) < t.size 
    then t.start + t.len 
    else  t.start + t.len - t.size in
    r := ({t with
             ghostdata=(Append t.ghostdata (Const 1 (Some v)));
             data=(Update t.data nextEmpty (Some v));
             len=(t.len + 1)})
    
val dequeue: 'a::*
       -> r:T 'a
       -> Writer 'a
              (Requires (fun h => Not(Empty h r)))
              (Ensures _ (fun h v h' => 
                  ((v = (Get ((SelHeap h r).ghostdata) 0))
                   && (Eq ((SelHeap h' r).size) ((SelHeap h r).size))
                   && (Equal ((SelHeap h' r).ghostdata)
                         (Slice ((SelHeap h r).ghostdata) 1 (Length ((SelHeap h r).ghostdata)))))))
              (Modifies (Singleton r))
let dequeue('a::*) (r:T 'a) =
  let t = !r in
    match Index t.data t.start with
      | None -> unreachable()
      | Some v -> 
          let _ =  r := ({t with
                            ghostdata=(Slice t.ghostdata 1 (Length t.ghostdata));
                            start=(if (t.start + 1) = t.size then 0 else t.start + 1);
                            len=(t.len - 1)}) in 
            v
end

module Test    
open Array
open RingBuffer

(*
    e1 e2 : DST int P  ~> bind ['a=_, 'b=_, 'Tx1=_ ...] e1 (\f. bind e2 (\x. f x)) : DST t WP <: DST int P
*)
val testHarness: x:int -> y:int -> z:int -> Writer unit TrivialPre (TrivialPost _) (Modifies EmptySet)
let testHarness (x:int) (y:int) (z:int) =
  let b = RingBuffer.create 2 in
  let _ = RingBuffer.enqueue b x in
  let _ = RingBuffer.enqueue b y in
  let h = RingBuffer.dequeue b in
  let _ = assert_lemma<Eq h x> () in
    RingBuffer.enqueue b z;
    let h = RingBuffer.dequeue b in
    let _ = assert_lemma<Eq h y> () in 
    let h = RingBuffer.dequeue b in
    let _ = assert_lemma<Eq h z> () in 
      ()
      

  
