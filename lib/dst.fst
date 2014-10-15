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
(* -------------------------------------------------------------------------------- *)
(* The Dijkstra state monad *)
(* -------------------------------------------------------------------------------- *)
module DST

(* The primitive heap of references is modeled using a Select/Update theory *)
logic array(SelHeap, UpdHeap, EmpHeap, InHeap) type heap (* = list (loc * obj) *)
logic val SelHeap : 'a:S -> heap -> ref 'a -> 'a
logic val UpdHeap : 'a:S -> heap -> ref 'a -> 'a -> heap
logic val EmpHeap : heap
type InHeap : 'a:S => heap => ref 'a => E
type ST : _ = fun ('Pre:heap => E) ('a:S) ('Post:result 'a => heap => E) =>
    h:heap{'Pre h} -> (x:'a * h':heap{'Post (V x) h'})

type DST : _ = fun ('a:S) ('Tx:(result 'a => heap => E) => heap => E) =>
    'Post:(result 'a => heap => E) -> ST ('Tx 'Post) 'a 'Post

type D : _ = fun ('a:S) => DST 'a (fun ('Post:result 'a => heap => E) h => forall x h'. 'Post (V x) h')

type Requires : _ = fun ('a:S) ('R:heap => E) =>
    DST 'a (fun ('Post:result 'a => heap => E) h => 'R h /\ (forall x h'. 'Post (V x) h'))

type Ensures : _ = fun ('a:S) ('E:heap => 'a => heap => E) =>
    DST 'a (fun ('Post:result 'a => heap => E) h => forall x h'. 'E h x h' ==> 'Post (V x) h')

type Modifies : _ = fun ('a:S) (x:ref 'a) (h:heap) (h':heap) =>
    forall ('b:S) (y:ref 'b). x<>y ==> SelHeap h y = SelHeap h' y /\ (InHeap h y ==> InHeap h' y)

type ReqEns : _ = fun ('a:S) ('R:heap => E) ('E:heap => 'a => heap => E) =>
    DST 'a (fun ('Post:result 'a => heap => E) (h:heap) =>
         'R h /\ (forall x h'. 'E h x h' ==> 'Post (V x) h'))

type returnTX : _ =
    fun ('a:S) (x:'a) ('Post:result 'a => heap => E) => 'Post (V x)

type bindNoExnTX : _ =
    fun ('a:S) ('b:S)
      ('Tx1:(result 'a => heap => E) => heap => E)
      ('Tx2:'a => (result 'b => heap => E) => heap => E)
      ('Post:result 'b => heap => E) =>
      ('Tx1 (fun (x:result 'a) (h:heap) =>
          forall (v:'a). x=V v ==> 'Tx2 v 'Post h))  (* Tx1 returns normally *)

type bindTX : _ =
    fun ('a:S) ('b:S)
      ('Tx1:(result 'a => heap => E) => heap => E)
      ('Tx2:'a => (result 'b => heap => E) => heap => E)
      ('Post:result 'b => heap => E) =>
      ('Tx1 (fun (x:result 'a) (h:heap) =>
           (forall (e:exn). x=E e ==> 'Post (E e) h) /\ (* Tx1 raises an exceptions *)
           (x=Err ==> 'Post Err h) /\                   (* Tx1 has a fatal error *)
           (forall (v:'a). x=V v ==> 'Tx2 v 'Post h)))  (* Tx1 returns normally *)

type Tx2E : 'a:S => ((result 'a => heap => E) => heap => E) => E
type HeapInv : heap => E
type DeltaHeap : heap => heap => E
assume DeltaHeap_trans: forall h1 h2 h3. DeltaHeap h1 h2 /\ DeltaHeap h2 h3 ==> DeltaHeap h1 h3
type WithInv : _ = fun ('a:S) ('Tx:(result 'a => heap => E) => heap => E) ('Post:result 'a => heap => E) (hin:heap) =>
    HeapInv hin /\ 'Tx (fun (r:result 'a) (hout:heap) => HeapInv hout /\ DeltaHeap hin hout ==> 'Post r hout) hin
type iDST : _ = fun ('a:S) ('Tx:(result 'a => heap => E) => heap => E) =>
    DST 'a (WithInv 'a 'Tx)
    
type Witness : heap => E
val get: unit
  -> DST heap (fun ('Post:result heap => heap => E) h => 'Post (V h) h)
val witness:
     unit
  -> iDST heap (fun ('Post:result heap => heap => E) h =>
      (Witness h ==> 'Post (V h) h))
val recall:
     unit
  -> iDST unit (fun ('Post:result unit => heap => E) h =>
      (forall (hold:heap). Witness hold ==> DeltaHeap hold h)
      ==> 'Post (V ()) h)
type ResultIs : _ = fun ('a:S) (r:result 'a) ('T:'a => E) =>
    (forall (x:'a). r=(V x) ==> 'T x)
val ref:
     'a:S
  ->  v:'a
  -> DST (ref 'a) (fun ('Post:result (ref 'a) => heap => E) h =>
      (forall (x:ref 'a). not (InHeap h x)
       ==> 'Post (V x) (UpdHeap h x v)))

val read: 'a:S
  -> r:ref 'a
  -> DST 'a (fun ('Post:result 'a => heap => E) h =>
      'Post (V (SelHeap h r)) h)

val write: 'a:S
  -> r:ref 'a
  -> v:'a
  -> DST unit (fun ('Post:result unit => heap => E) h =>
      'Post (V ()) (UpdHeap h r v))

val fatal_error: unit -> DST 'a (fun ('Post:result 'a => heap => E) h =>
    'Post Err h)

val raise : e:exn -> DST 'a (fun ('Post:result 'a => heap => E) h =>
    'Post (E e) h)

type WithFinally : _ = (fun ('a:S)
                           ('Tx2:(result unit => heap => E) => heap => E)
                           ('Post:result 'a => heap => E)
                           (r1:result 'a) (hpre2:heap) =>
    ((r1=Err ==> 'Post r1 hpre2)
     /\ (r1<>Err ==> ('Tx2 (fun (r2:result unit) (hfinal:heap) =>
                                ((r2=V() ==> 'Post r1 hfinal)
                                 /\ (forall e. (r2=E e ==> 'Post (E e) hfinal))
                                 /\ (r2=Err ==> 'Post Err hfinal)))
                              hpre2))))

type TryFinally : _ = (fun ('a:S)
                          ('Tx1:(result 'a => heap => E) => heap => E)
                          ('Tx2:(result unit => heap => E) => heap => E)
                          ('Post:result 'a => heap => E)
                          (hinit:heap) =>
    ('Tx1 (WithFinally 'a 'Tx2 'Post) hinit))
    
val try_finally: 'a:S
  -> 'Tx1:(unit => (result 'a => heap => E) => heap => E)
  -> 'Tx2:(unit => (result unit => heap => E) => heap => E)
  -> (x:unit -> DST 'a ('Tx1 x))
  -> (y:unit -> DST unit ('Tx2 y))
  -> iDST 'a (TryFinally 'a ('Tx1 ()) ('Tx2 ()))
  
val assert_lemma: 'T:E
  -> unit
  -> DST unit (fun ('Post:result unit => heap => E) h =>
      ('T /\ ('T ==> 'Post (V ()) h)))

val assume_lemma: 'T:E
  -> unit
  -> DST unit (fun ('Post:result unit => heap => E) h =>
      ('T ==> 'Post (V ()) h))

val annot_refinement: 'a:S
  -> 'T:('a => E)
  -> x:'a
  -> DST (x:'a{'T x}) (fun ('Post:result (x:'a{'T x}) => heap => E) h =>
      'T x /\ (forall (y:'a{'T y}). x=y ==> 'Post (V y) h))
