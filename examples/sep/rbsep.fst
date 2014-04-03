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
#monadic(DST.DST, DST.returnTX, DST.bindNoExnTX)
module RingBuffer
open DST
open Array
open RefSet

type clear_t ('a::*) ('Inv::heap => E) (fp:refset) (ghostdata:array (option 'a)) (size:pos) = 
    u:unit -> Writer unit (Requires (On fp 'Inv))
                          (Ensures _ (fun h u h' => 
                               (On fp 'Inv h'
                                && Length (SelHeap h' ghostdata) = 0)))
                          (Modifies fp)

type head_t ('a::*) ('Inv::heap => E) (fp:refset) (ghostdata:array (option 'a)) (size:pos) = 
    u:unit -> Reader 'a (Requires (fun h => (On fp 'Inv h && (GT (Length (SelHeap h ghostdata)) 0))))
                        (Provides _ (fun h a => (a=(Some_proj_1 (Index (SelHeap h ghostdata) 0)))))

type enqueue_t ('a::*) ('Inv::heap => E) (fp:refset) (ghostdata:array (option 'a)) (size:pos) = 
    v:'a -> Writer unit (Requires (fun h => (On fp 'Inv h && LT (Length (SelHeap h ghostdata)) size)))
                        (Ensures _ (fun h u h' =>
                             (On fp 'Inv h'
                              && Equal _ (SelHeap h' ghostdata) (Append (SelHeap h ghostdata) (Const 1 (Some v))))))
                        (Modifies fp)

type dequeue_t ('a::*) ('Inv::heap => E) (fp:refset) (ghostdata:array (option 'a)) (size:pos) = 
    u:unit -> Writer 'a (Requires (fun h => (On fp 'Inv h && GT (Length (SelHeap h ghostdata)) 0)))
                        (Ensures _ (fun h v h' =>
                             (On fp 'Inv h'
                              && (v = (Some_proj_1 (Index (SelHeap h ghostdata) 0)))
                              && (Equal _
                                    (SelHeap h' ghostdata)
                                    (Slice (SelHeap h ghostdata) 1 (Length (SelHeap h ghostdata)))))))
                        (Modifies fp)

type record ('a::*) ('Inv::heap => E) (fp:refset) (ghostdata:array (option 'a)) (size:pos) = 
    { 
      clear:   clear_t 'a 'Inv fp ghostdata size;
      head:    head_t 'a 'Inv fp ghostdata size;
      enqueue: enqueue_t 'a 'Inv fp ghostdata size;
      dequeue: dequeue_t 'a 'Inv fp ghostdata size
    }

logic data type t 'a =
  | RB : 'Inv::heap => E 
    -> ghostfp:refset              (* ghost *)
    -> ghostdata:array (option 'a) (* ghost *)
    -> size:pos 
    -> record 'a 'Inv ghostfp ghostdata size
    -> t 'a

type Invariant :: 'a::* => array (option 'a) => ref nat => ref nat => array (option 'a) => pos => heap => E
assume InvariantDef: forall ('a::*) (data:array (option 'a)) (start:ref nat) (len:ref nat) (ghostdata:array (option 'a)) (size:pos) (h:heap).
                        {:pattern (Invariant 'a data start len ghostdata size h )}
                        (Invariant 'a data start len ghostdata size h 
                         <==> 
                         (Perm data h && Perm start h && Perm len h && Perm ghostdata h && (start <> len) && (ghostdata <> data)
                          && (Length (SelHeap h data) = size)
                          && (SelHeap h start < size)
                          && (SelHeap h len <= size)
                          && (forall (i:nat). (i < Length (SelHeap h  ghostdata)) ==> (Some_is (Index (SelHeap h ghostdata) i)))
                          && (if (LTE (Add (SelHeap h start) (SelHeap h len)) size)
                              then (Array.Equal _ (SelHeap h ghostdata) (Slice (SelHeap h data) (SelHeap h start) (Add (SelHeap h start) (SelHeap h len))))
                              else (Array.Equal _ (SelHeap h ghostdata) (Append (Slice (SelHeap h data) (SelHeap h start) size)
                                                                                     (Slice (SelHeap h data) 0 (Sub (Add (SelHeap h start) (SelHeap h len)) size)))))))

val create: 'a::* 
         -> size:pos
         -> Writer (t 'a) (TrivialPre)
                          (Ensures _ (fun h v h' => 
                               (On (RB_proj_2 v) (RB_proj_1 v) h' 
                                && Fresh h (RB_proj_2 v)
                                && Eq 0 (Length (SelHeap h' (RB_proj_3 v)))
                                && (RB_proj_4 v = size))))
                          (Modifies EmptySet)
let create ('a::*) (size:pos) =
  let data = ref (Array.Const<option 'a> size None) in 
  let start = ref (0:nat) in 
  let len = ref (0:nat) in   
  let ghostdata = ref (Array.Const<option 'a> 0 None) in
  let ghostfp = Union  (Singleton data) (Union (Singleton ghostdata) (Union (Singleton start) (Singleton len))) in 

  let clear : clear_t 'a (Invariant 'a data start len ghostdata size) ghostfp ghostdata size =
    fun (u:unit) -> 
      (len := 0);
      (ghostdata := Array.Emp) in 

  let head : head_t 'a (Invariant 'a data start len ghostdata size) ghostfp ghostdata size = 
    fun (u:unit) -> 
      match Index (!data) (!start) with
        | None -> unreachable ()
        | Some v -> v in

  let enqueue : enqueue_t 'a (Invariant 'a data start len ghostdata size) ghostfp ghostdata size = 
    fun (v:'a) -> 
      let s = !start in 
      let l = !len in 
      let nextEmpty = 
        if (s + l) < size
        then s + l
        else s + l - size in 
      let g = !ghostdata in 
      let d = !data in 
      let _ = len := (l + 1) in 
      let _ = ghostdata := (Append g (Const 1 (Some v))) in 
      let _ = data := (Update d nextEmpty (Some v)) in 
        () in

  let dequeue : dequeue_t 'a (Invariant 'a data start len ghostdata size) ghostfp ghostdata size = 
    fun (u:unit) ->
      match Index (!data) (!start) with
        | None -> unreachable()
        | Some v -> 
            let g = !ghostdata in 
            let s = !start in 
            let _ = ghostdata := (Slice g 1 (Length g)) in
            let _ = start := (if (s + 1) = size then 0 else s + 1) in 
            let _ = len := (!len - 1) in 
              v in 
    
    (RB<'a,(Invariant 'a data start len ghostdata size)>
       ghostfp
       ghostdata 
       size
       ({clear=clear;
         head=head;
         enqueue=enqueue;
         dequeue=dequeue}))
      
end

module Test    
open RefSet
open Array
open RingBuffer
open DST

val testHarness: x:int -> y:int -> z:int -> Writer unit TrivialPre (TrivialPost _) (Modifies EmptySet)
let testHarness (x:int) (y:int) (z:int) =
  let h = get () in 
  let r = RingBuffer.create<int> 2 in
    match r with 
      | RB '_ 'Inv fp gd sz rb -> 
          let _ = rb.enqueue x in
          let _ = rb.enqueue y in
          let w = rb.dequeue () in
          let _ = assert_lemma<Eq w x> () in
            rb.enqueue z;
            let w = rb.dequeue () in
            let _ = assert_lemma<Eq w y> () in
            let w = rb.dequeue () in
            let _ = assert_lemma<Eq w z> () in
              ()
      

  
