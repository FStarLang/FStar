(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.ViewLens.Tuple2

open FStar.HyperStack.ST

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.ViewLens
open LowStar.ViewLensST

noeq
type pointer_lens a = 
  | Mk_pl : l:hs_view_lens (B.pointer a) a{
              (as_loc l.fp == B.loc_buffer l.roots) /\ 
              (forall h . l.inv h ==> B.live h l.roots /\ B.as_seq h l.roots == Seq.create 1 (l.view h)) /\ 
              (forall h1 h2 . l.view h1 == l.view h2 ==> B.as_seq h1 l.roots == B.as_seq h2 l.roots)} -> 
            pl_reader:(unit -> LensST a l (fun _ -> True) (fun m1 x m2 -> m1 == x /\ x == m2)) -> 
            pl_writer:(x:a -> LensST unit l (fun _ -> True) (fun _ _ m -> m == x)) ->
            pointer_lens a

noeq
type tup2_t (a:Type) (b:Type) =
  | Mk_tl : l1:pointer_lens a ->
            l2:pointer_lens b{lens_disjoint l1.l l2.l} -> 
            tl_reader:(unit -> LensST (a & b) (l1.l <*> l2.l) (fun _ -> True) (fun m1 xy m2 -> m1 == xy /\ xy == m2)) -> 
            tl_writer:(x:a -> y:b -> LensST unit (l1.l <*> l2.l) (fun _ -> True) (fun _ _ m -> m == (x,y))) -> 
            tup2_t a b

let mk_tup2 (#a:Type) (#b:Type)
            (l1:pointer_lens a)
            (l2:pointer_lens b{lens_disjoint l1.l l2.l})
          : tup2_t a b = 
  let tl_reader () : LensST (a & b) (l1.l <*> l2.l) (fun _ -> True) (fun m1 xy m2 -> m1 == xy /\ xy == m2) = 
        (let x = lens_include (star_includes_left l1.l l2.l) #_ #(fun _ -> True) #(fun m1 x m2 -> m1 == x /\ x == m2) (fun _ -> l1.pl_reader ()) in
         let y = lens_include (star_includes_right l1.l l2.l) #_ #(fun _ -> True) #(fun m1 x m2 -> m1 == x /\ x == m2) (fun _ -> l2.pl_reader ()) in 
         admit ()) in 
  let tl_writer (x:a) (y:b) : LensST unit (l1.l <*> l2.l) (fun _ -> True) (fun _ _ m -> m == (x,y)) = 
        (lens_include (star_includes_left l1.l l2.l) #unit #(fun _ -> True) #(fun _ _ m -> m == x) (fun _ -> l1.pl_writer x);
         lens_include (star_includes_right l1.l l2.l) #unit #(fun _ -> True) #(fun _ _ m -> m == y) (fun _ -> l2.pl_writer y);
         admit ()) in 
  Mk_tl l1 l2 tl_reader tl_writer
