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
module Set
type nat = i:int{GTE i 0}
type arr :: * => *

(* TODO: Why not use nat here? Problem: desugaring refinements in the logic. *)
logic function SizeOf : arr 'a -> int
logic function Emp : int -> 'a -> arr 'a
logic function ArrSel : int -> arr 'a -> 'a
logic function ArrUpd : int -> 'a -> arr 'a -> arr 'a
assume (forall (x:arr 'a) (n:nat) (v:'a). ((ArrSel n (ArrUpd n v x)) = v))
assume (forall (x:arr 'a) (n:nat) (m:nat) (v:'a). (not (m=n)) => ((ArrSel n (ArrUpd m v x)) = (ArrSel n x)))
assume (forall (x:arr 'a) (n:nat) (v:'a). ((SizeOf x) = (SizeOf (ArrUpd n v x))))
assume (forall (x:int) (y:int). (GTE x y) <=> (GT x y) || (x=y))

type setrec = {dense : arr int; 
               sparse : arr int; 
               n : int;
               maxsize: int}
type setref = ref setrec

(* Element i is in the set if  sparse[dense[i]] = i *) 
type InSet :: int => setrec => E 
assume (forall (i:int) (r:setrec). 
          InSet i r <=> 
          ((GTE (ArrSel i r.sparse) 0) && 
           (LT (ArrSel i r.sparse) r.n) &&
           (Eq (ArrSel (ArrSel i r.sparse) r.dense) i)))


(* The contents of dense in [0,n) is in the set *)
type SetInvariant :: setref => heap => E 
assume (forall (x:setref) (h:heap). 
          ((SetInvariant x h) <=> 
             (forall (di:int) (r:setrec). (r=(Select x h)) && (GTE di 0) && (LT di r.n) =>
                 (InSet (ArrSel di r.dense) r))))
type set = x:setref{SetInvariant x}


val create: 'Post::(set => heap => E)
         -> max:nat
         -> ST (fun (h:heap) => 
                      (forall (x:set) (s:setrec) (h':heap).
                          ((Fresh x h) && 
                           (h'=(Update x s h)) && 
                           (SetInvariant x h') && 
                           (s.maxsize=max) && 
                           (s.n=0)) => 'Post x h'))
                set
               'Post

val get: 'Post::(bool => heap => E)
      -> x:set
      -> i:nat
      -> ST (fun (h:heap) =>
              (forall (r:setrec). (r=(Select x h)) =>
                  ((LT i r.maxsize) &&
                   (InSet i r => 'Post true h) &&
                   ((not(InSet i r)) => 'Post false h))))
            bool
           'Post

val set: 'Post::(unit => heap => E)
      -> x:set
      -> i:nat
      -> ST (fun (h:heap) =>
              (forall (r:setrec). (r=(Select x h)) =>
                  ((LT i r.maxsize) &&
                   (InSet i r => 'Post () h) &&
                   ((not(InSet i r)) => 'Post () (Update x ({dense=(ArrUpd<int> r.n i r.dense);
                                                             sparse=(ArrUpd<int> i r.n r.sparse);
                                                             n=(Plus r.n 1);
                                                             maxsize=r.maxsize}) h)))))
            unit
            'Post

module TestHarness
open Set

val test : 'a::*
        -> 'Post :: (unit => heap => E)
        -> x:'a
        -> ST (fun (h:heap) => (forall (y:unit) (h':heap). 'Post y h')) unit 'Post
let test x = 
  (* let c = Set.create<int, _> 0 in *) (* Should fail *)
  let a = Set.create 10 in 
  let b = Set.create 20 in
  let ra = Set.get a 5 in 
(*   let rb = Set.get b 7 in  *)
  let _ = Assert<(fun (H:heap) => (ra = false)), _> () in ()


(*   let _ = Assert<(fun (H:heap) => (rb = false)), _> () in *)
(*   let _ = Set.set a 5 in *)
(*   let _ = Set.set b 7 in *)
(*   let rb = Set.get b 7 in *)
(*     Assert<(fun (H:heap) => (ra = true)), _> (); *)
(*     Assert<(fun (H:heap) => (rb = true)), _> (); *)
(*     Assert<(fun (H:heap) => *)
(*              (fun (r:setrec) => *)
(*                ((ArrSel 0 r.dense) = 5)) (Select a H)), _> (); *)
(*     Assert<(fun (H:heap) => *)
(*              (fun (r:setrec) => *)
(*                ((ArrSel 5 r.sparse) = 0)) (Select a H)), _> (); *)
(*     Assert<(fun (H:heap) => *)
(*              (fun (r:setrec) => *)
(*                (r.n = 1)) (Select a H)), _> (); *)
(*     Assert<(fun (H:heap) => *)
(*              (fun (r:setrec) => *)
(*                ((ArrSel 0 r.dense) = 7)) (Select b H)), _> (); *)
(*     Assert<(fun (H:heap) => *)
(*              (fun (r:setrec) => *)
(*                ((ArrSel 7 r.sparse) = 0)) (Select b H)), _> (); *)
(*     Assert<(fun (H:heap) => *)
(*              (fun (r:setrec) => *)
(*                (r.n = 1)) (Select b H)), _> () *)

end

