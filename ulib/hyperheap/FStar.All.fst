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
module FStar.All
open FStar.ST

let all_pre = all_pre_h HyperHeap.t
let all_post (a:Type) = all_post_h HyperHeap.t a
let all_wp (a:Type) = all_wp_h HyperHeap.t a
new_effect ALL = ALL_h HyperHeap.t

inline let lift_state_all (a:Type) (wp:st_wp a) (p:all_post a) =  wp (fun a -> p (V a))
sub_effect STATE ~> ALL = lift_state_all

inline let lift_exn_all (a:Type) (wp:ex_wp a)   (p:all_post a) (h:HyperHeap.t) = wp (fun ra -> p ra h)
sub_effect EXN   ~> ALL = lift_exn_all

effect All (a:Type) (pre:all_pre) (post: (HyperHeap.t -> Tot (all_post a))) =
       ALL a
           (fun (p:all_post a) (h:HyperHeap.t) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1)) (* WP  *)
           (fun (p:all_post a) (h:HyperHeap.t) -> forall ra h1. (pre h /\ post h ra h1) ==> p ra h1) (* WLP *)
effect ML (a:Type) =
  ALL a (all_null_wp HyperHeap.t a) (all_null_wp HyperHeap.t a)

assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val failwith: string -> All 'a (fun h -> True) (fun h a h' -> is_Err a /\ h==h')
assume val exit: int -> 'a
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a
