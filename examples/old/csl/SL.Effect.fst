(*
   Copyright 2008-2018 Microsoft Research

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
module SL.Effect

open SL.Heap

let pre = memory -> Type0
let post (a:Type) = a -> memory -> Type0
let st_wp (a:Type) = post a -> pre

(* unfold *) let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> post x m0

(* unfold *) let frame_post (#a:Type) (p:post a) (m0:memory) :post a =
  fun x m1 -> defined (m1 <*> m0) ==> p x (m1 <*> m0)  //m1 is the frame

(* unfold *) let frame_wp (#a:Type) (wp:st_wp a) (post:post a) (m:memory) =
  exists (m0 m1:memory). defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ wp (frame_post post m1) m0

(* unfold *) let bind_wp (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post m0 -> wp1 (fun x m1 -> wp2 x post m1) m0

(* unfold *) let id_wp (a:Type) (x:a) (p:post a) (m:memory) = p x emp

(* unfold *)  let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (m0:memory) =
  l_ITE p (wp_then post m0) (wp_else post m0)

(* unfold *)  let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (m0:memory) = wp p m0

(* unfold *)  let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (m:memory). wp1 p m ==> wp2 p m

(* unfold *) let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (m:memory) =
  forall (b:b). wp b p m

(* unfold *) let st_trivial (a:Type) (wp:st_wp a) =
  forall m0. wp (fun _ _ -> True) m0
      
new_effect {
  STATE : result:Type -> wp:st_wp result -> Effect
  with return_wp    = return_wp
     ; bind_wp      = bind_wp
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite_wp
     ; stronger     = st_stronger
     ; close_wp     = st_close_wp
     ; trivial      = st_trivial
}

let (<|) f x = f x

let with_fp (fp : refs) (x:'a) : 'a = x

let by_smt (x:Type0) : Type0 = x
let mem_eq (x:Type0) : Type0 = x

let with_fp_lemma fp x : Lemma (with_fp fp x == x) [SMTPat (with_fp fp x)] = ()

effect ST (a:Type) (wp:st_wp a) (fp:refs) = STATE a (frame_wp (with_fp fp wp))
