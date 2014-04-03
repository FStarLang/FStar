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
module ST

(* A very manual and tedious way of programming with the Hoare state monad. 
   See the Dijkstra monadic examples for a more practical and powerful way. 
   e.g., auth.fst and auth2.fst in this same directory. *)

type ref :: * => *
type heap
type Select :: 'a::* => heap => ref 'a => 'a => P
type Update :: 'a::* => heap => ref 'a => 'a => heap => P
type InDom :: 'a::* => ref 'a => heap => P

assume SU_1 : forall (h1:heap) (h2:heap) (x:ref 'a)  (v:'a). 
               Update h1 x v h2 => Select h2 x v

assume SU_2 : forall (h1:heap) (h2:heap) (x1:ref 'a)
                     (x2:ref 'b) (v1:'a) (v2:'b).
              ((not (Eq2 x1 x2)) && (Select h1 x1 v1) && (Update h1 x2 v2 h2)) =>
              Select h2 x1 v1

assume SU_3: forall (h:heap) (h1:heap) (h2:heap) (x:ref 'a) (v:'a).
              (Update h x v h1 && Update h x v h2) => h1=h2

assume SU_4: forall (h:heap) (x:ref 'a) (v1:'a) (v2:'a).
              (Select h x v1 && Select h x v2) => v1=v2

type ST ('Pre::(heap => E)) 
        ('a::*)  
        ('Post::(heap => heap => 'a => E)) = h1:heap{'Pre h1} -> (x:'a * h2:heap{'Post h1 h2 x})

val bindST: 'a::*
        -> 'b::*
        -> 'Pre1::(heap => P)
        -> 'Post1::(heap => heap => 'a => P)
        -> 'Pre2::('a => heap => E)
        -> 'Post2::(heap => heap => 'b => P)
        -> 'Post::(heap => heap => 'b => P)
        -> ST 'Pre1 'a 'Post1
        -> g:(x:'a -> (ST ('Pre2 x) 'b 'Post2)){(forall (h1:heap) (h2:heap) (x:'a). ('Pre1 h1 && 'Post1 h1 h2 x) => 'Pre2 x h2)}
        -> ST 'Pre1
              'b
              (fun (h1:heap) (h3:heap) (y:'b) => exists (h2:heap) (x:'a). ('Post1 h1 h2 x && 'Post2 h2 h3 y))
let bindST f g h = 
  let x, h1 = f h in 
    g x h1

val bindST2 : 'a::*
        -> 'b::*
        -> 'Pre::(heap => P)
        -> 'Post1::(heap => heap => 'a => P)
        -> 'Post::(heap => heap => 'b => P)
        -> ST 'Pre 'a 'Post1
        -> g:(h0:heap -> x:'a -> (ST (fun (h1:heap) => 'Post1 h0 h1 x) 'b (fun (h1:heap) (h2:heap) => 'Post h0 h2)))
        -> ST 'Pre
              'b
              'Post
let bindST2 f g h1 = 
  let x, h2 = f h1 in 
  let r, h3 = g h1 x h2 in 
    r, h3

val unitST: 'a::*
         -> 'Pre::(heap => P) 
         -> 'Post::(heap => heap => 'a => P)
         -> x:'a{forall (h:heap). 'Pre h => 'Post h h x}
         -> ST 'Pre 'a 'Post
let unitST x h = (x, h)

val read: r:ref 'a 
       -> ST (fun (h:heap) => InDom r h) 
             'a 
             (fun (h1:heap) (h2:heap) (v:'a) => (h1=h2) && Select h1 r v) 

val write: r:ref 'a 
        -> v:'a 
        -> ST (fun (h:heap) => InDom r h) 
              unit 
              (fun (h1:heap) (h2:heap) (x:unit) => Update h1 r v h2)

val alloc: v:'a
        -> ST (fun (h:heap) => True)
              (ref 'a)
              (fun (h1:heap) (h2:heap) (r:ref 'a) => (InDom r h2 && Update h1 r v h2))

end

module Client
open ST

val __assert: 'P::P
           -> unit
           -> ST (fun (h:heap) => 'P)
                 unit
                 (fun (h1:heap) (h2:heap) (x:unit) => (h1=h2))

(* let x = alloc 0 in *)
(* let y = read x in *)
(* let z = assert<y=0>() in  *)
(* let _ = write x 1 in *)
(* let y = read x in *)
(*  assert (y=1)     *)

let _ =
  bindST<ref int, unit, (fun (h:heap) => True),
                        (fun (h1:heap) (h2:heap) (x:ref int) => (InDom x h2 && Update h1 x 0 h2)),
                        (fun (x:ref int) (h1:heap) => (InDom x h1 && Select h1 x 0)),
                        (fun (h1:heap) (h2:heap) (r:unit) => True)>
                          
    (alloc 0) (fun (x:ref int) ->

  bindST<int, unit, (fun (h:heap) => (InDom x h && Select h x 0)),
                    (fun (h1:heap) (h2:heap) (y:int) => ((h1=h2) && (y=0))),
                    (fun (y:int) (h:heap) => (y=0)),
                    (fun (h1:heap) (h2:heap) (r:unit) => True)>

    (read x)  (fun (y:int) -> 

    (__assert<Eq y 0> () )))


let _ =
  bindST2<ref int, unit, (fun (h:heap) => True),
                         (fun (h1:heap) (h2:heap) (x:ref int) => (InDom x h2 && Update h1 x 0 h2 (* Select h2 x 0 *))),
                         (fun (h1:heap) (h2:heap) (r:unit) => True)>
                          
    (alloc 0) (fun (h0:heap) (x:ref int) ->

  bindST2<int, unit, (fun (h:heap) => (InDom x h && Select h x 0)),
                     (fun (h1:heap) (h2:heap) (y:int) => (h1=h2) && (y=0)),
                     (fun (h1:heap) (h2:heap) (r:unit) => True)>

    (read x)  (fun (h1:heap) (y:int) ->

    (__assert<Eq y 0>())))
                      
