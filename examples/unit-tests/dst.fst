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
module DST
open RefSet

(* ******************************************************************************** *)
(* Logical definition of heaps *)
(* ******************************************************************************** *)
logic array(SELHEAP, UPDHEAP, EmpHeap, INHEAP) type heap (* Interpreted as a (Array (ref 'a) (option 'a)) *)
logic val SELHEAP : 'a:S -> heap -> ref 'a -> 'a
logic val UPDHEAP : 'a:S -> heap -> ref 'a -> 'a -> heap    
logic val EmpHeap : heap
type INHEAP :  'a:S => heap => ref 'a => E
logic val SelHeap: 'a:S -> heap -> ref 'a -> 'a
logic val UpdHeap : 'a:S -> heap -> ref 'a -> 'a -> heap    
type InHeap :  'a:S => heap => ref 'a => E
logic val Restrict : heap -> refset -> heap
type HeapEqual : heap => heap => E

assume SelHeap_def: forall ('a:S) (h:heap) (r:ref 'a). SelHeap h r = SELHEAP h r
assume UpdHeap_def: forall ('a:S) (h:heap) (r:ref 'a) (v:'a). UpdHeap h r v = UPDHEAP h r v
assume InHeap_def: forall ('a:S) (h:heap) (r:ref 'a). InHeap 'a h r <==> INHEAP 'a h r
assume RestrictSel_def: forall (r:refset) (h:heap) ('a:S) (a:ref 'a). {:pattern (SelHeap (Restrict h r) a)}
        (InSet r a) ==> (SELHEAP (Restrict h r) a = SELHEAP h a)
assume RestrictIn_def: forall (r:refset) (h:heap) ('a:S) (a:ref 'a). {:pattern (InHeap (Restrict h r) a)}
        (if (InSet r a) 
         then (INHEAP (Restrict h r) a <==> (INHEAP h a))
         else (not(INHEAP (Restrict h r) a)))
assume HeapEqual_def: forall h1 h2.{:pattern (HeapEqual h1 h2)} 
         (HeapEqual h1 h2 <==> (forall ('a:S) (a:ref 'a).{:pattern (SelHeap h1 a); (SelHeap h2 a)}
                                  (SELHEAP h1 a = SELHEAP h2 a)))
assume HeapEqual_ext: forall h1 h2.{:pattern (HeapEqual h1 h2)} HeapEqual h1 h2 ==> h1=h2
assume RestrictEqual: forall h1 h2 r.{:pattern (Restrict h1 r); (Restrict h2 r)} 
         ((forall ('a:S) (a:ref 'a). {:pattern (InSet r a)} InSet r a ==> (SELHEAP h1 a = SELHEAP h2 a))
                       ==> (Restrict h1 r = Restrict h2 r))

(* ******************************************************************************** *)
(* Core definition of a Dijkstra-style state monad *)
(* ******************************************************************************** *)
type ST : _ = fun ('Pre:heap => E) ('a:S) ('Post:result 'a => heap => E) => 
    (h:heap{'Pre h} -> (x:'a * (h':heap{'Post (V x) h'})))
type DST : _ = fun ('a:S) ('Tx:(result 'a => heap => E) => heap => E) => 
    ('Post:(result 'a => heap => E)
     -> (ST ('Tx 'Post) 'a 'Post))
type returnTX : _ = 
    fun ('a:S) (x:'a) ('Post:result 'a => heap => E) (h:heap) => (forall (y:'a). y=x ==> 'Post (V y) h)
type bindTX : _ = 
    fun ('a:S) ('b:S) 
      ('Tx1:(result 'a => heap => E) => heap => E)
      ('Tx2:'a => (result 'b => heap => E) => heap => E)
      ('Post:result 'b => heap => E) => 
      ('Tx1 (fun (x:result 'a) (h:heap) =>
           (forall (e:exn). (x=E e) ==> 'Post (E e) h) /\ (* Tx1 raises an exceptions *)
           ((x=Err) ==> 'Post Err h) /\                   (* Tx1 has a fatal error *)
           (forall (v:'a). (x=V v) ==> 'Tx2 v 'Post h)))  (* Tx1 returns normally *)
type bindNoExnTX : _ = 
    fun ('a:S) ('b:S) 
      ('Tx1:(result 'a => heap => E) => heap => E)
      ('Tx2:'a => (result 'b => heap => E) => heap => E)
      ('Post:result 'b => heap => E) => 
      ('Tx1 (fun (x:result 'a) (h:heap) =>
           (forall (v:'a). (x=V v) ==> 'Tx2 v 'Post h)))  (* Tx1 returns normally *)

(* ******************************************************************************** *)
(* Connectives and predicates related to permissions and separation *)
(* ******************************************************************************** *)
type Star : _ = fun ('P:heap => E) ('Q:heap => E) (h:heap) => (* affine interpretation *)
    (exists r1 r2.{:pattern (Disjoint r1 r2)} Disjoint r1 r2 /\ 'P (Restrict h r1) /\ 'Q (Restrict h r2))

type StarH : _ = fun (r1:refset) (r2:refset) ('P:heap => E) ('Q:heap => E) (h:heap) =>
    (Disjoint r1 r2 /\ 'P (Restrict h r1) /\ 'Q (Restrict h r2))

type Fresh : _ = fun (h:heap) (r:refset) => 
    (forall ('a:S) (a:ref 'a).{:pattern (InSet r a)} (InSet r a ==> Not(INHEAP h a)))

type RefsInHeap : _ = fun (h:heap) (r:refset) => 
    (forall a.{:pattern (InHeap h a)} InSet r a ==> INHEAP h a)
    
type Perm : 'a:S => ref 'a => heap => E

type On : _ = fun (r:refset) ('P:heap => E) (h:heap) => ('P (Restrict h r))

type Lift : (heap => E) => E

type Permission : _ = fun ('a:S) (r:ref 'a) (h:heap) => (Perm r h /\ InHeap h r)

assume PermEq: forall (h1:heap) (h2:heap) ('a:S) (r:ref 'a). {:pattern (Perm r h1); (Perm r h2)}
           (Perm r h1 /\ (SELHEAP h1 r = SELHEAP h2 r)) ==> Perm r h2

assume RestrictPerm1: forall (h:heap) (s:refset) ('a:S) (r:ref 'a). {:pattern (Perm r (Restrict h s))}
           (Perm r (Restrict h s) /\ InSet s r) ==> Perm r h

assume RestrictPerm2: forall (h:heap) (s:refset) ('a:S) (r:ref 'a). {:pattern (Perm r (Restrict h s))}
           (Perm r h /\ InSet s r) ==> (Perm r (Restrict h s))

(* ******************************************************************************** *)
(* Commonly used special cases *)
(* ******************************************************************************** *)

(* Pure: A monad for code neither reads now writes the heap *)
type Pure : _ = fun ('a:S) ('Pre:E) ('Post:'a => E) => 
    (DST 'a (fun ('Q:result 'a => heap => E) (h:heap) => 
         ('Pre /\ (forall (x:'a). 'Post x ==> 'Q (V x) h))))

(* Reader: For code that only reads the heap *)
type Reader : _ = fun ('a:S) ('Pre:heap => E) ('Post:heap => 'a => E) => 
    (DST 'a (fun ('Q:result 'a => heap => E) (h:heap) =>
         ('Pre h /\ (forall (x:'a). 'Post h x ==> 'Q (V x) h))))

(* Writer: For code that reads, writes, or allocates *)
type Mods : _ = fun (m:refset) (h:heap) (h':heap) => 
    (forall ('b:S) (x:ref 'b).{:pattern (SelHeap h' x); (InHeap h' x)}
       (InHeap h x /\ Not(InSet m x))
     ==> (InHeap h' x /\ (SelHeap h x = SelHeap h' x)))

type Writer : _ = fun ('a:S) ('Pre:heap => E) ('Post:heap => 'a => heap => E) (mods:refset) => 
    (DST 'a (fun ('Q:result 'a => heap => E) (h:heap) =>
         ('Pre h /\ 
            (forall (x:'a) (h':heap). ('Post h x h' /\ Mods mods h h')
             ==> 'Q (V x) h'))))

(* ML: The ML monad, i.e., anything goes *)
type ML : _ = fun ('a:S) => (DST 'a (fun ('Post:result 'a => heap => E) h => (forall x h'. 'Post (V x) h')))

(* ******************************************************************************** *)
(* Some conveniences *) 
(* ******************************************************************************** *)
type Requires : _ = fun ('P:heap => E) => 'P
type Ensures : _ = fun ('a:S) ('P:heap => 'a => heap => E) => 'P
type Provides : _ = fun ('a:S) ('P:heap => 'a => E) => 'P
type TrivialPre : _ = fun (h:heap) => True
type TrivialPost : _ = fun ('a:S) (h:heap) (a:'a) (h':heap) => True
logic val Modifies : refset -> refset
define Modifies_id: forall r. Modifies r = r
type ResultIs : _ = fun ('a:S) (r:result 'a) ('T:'a => E) => 
    (forall (x:'a). r=(V x) ==> 'T x)

(* ******************************************************************************** *)
(* Primitive operations on references store *)
(* ******************************************************************************** *)
val ref:
     'a:S
  ->  v:'a
  -> DST (ref 'a) (fun ('Post:result (ref 'a) => heap => E) h => 
      (forall (x:ref 'a) (h':heap). 
         (not (InHeap h x) /\ Perm x h' /\ h'=UpdHeap h x v)
       ==> 'Post (V x)  h'))

val read: 'a:S
  -> r:ref 'a
  -> Reader 'a (Requires (Perm r))
               (Provides _ (fun h a => (a=SelHeap h r)))

val write: 'a:S
  -> r:ref 'a
  -> v:'a 
  -> Writer unit (Requires (Perm r))
                 (Ensures _ (fun h u h' => 
                      ((h'=UpdHeap h r v)
                       /\ Perm r h')))
                 (Modifies (Singleton r))

val get: unit -> Reader heap TrivialPre (fun h h' => (h=h'))

val assert_lemma: 'T:E 
  -> unit
  -> Pure unit (LBL "assert_lemma" 'T) (fun u => 'T)

val assume_lemma: 'T:E 
  -> unit
  -> Pure unit True (fun u => 'T)

