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

let all_pre = all_pre_h HyperStack.mem
let all_post (a:Type) = all_post_h HyperStack.mem a
let all_wp (a:Type) = all_wp_h HyperStack.mem a
new_effect ALL = ALL_h HyperStack.mem

unfold let lift_state_all (a:Type) (wp:st_wp a) (p:all_post a) =  wp (fun a -> p (V a))
sub_effect STATE ~> ALL = lift_state_all

unfold let lift_exn_all (a:Type) (wp:ex_wp a)   (p:all_post a) (h:HyperStack.mem) = wp (fun ra -> p ra h)
sub_effect EXN   ~> ALL = lift_exn_all

effect All (a:Type) (pre:all_pre) (post: (HyperStack.mem -> Tot (all_post a))) =
       ALL a
           (fun (p:all_post a) (h:HyperStack.mem) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1)) (* WP  *)
effect ML (a:Type) =
  ALL a (all_null_wp HyperStack.mem a)

assume val pipe_right: 'a -> ('a -> ML 'b) -> ML 'b
assume val pipe_left: ('a -> ML 'b) -> 'a -> ML 'b
assume val failwith: string -> All 'a (fun h -> True) (fun h a h' -> Err? a /\ h==h')
assume val exit: int -> ML 'a
assume val try_with: (unit -> ML 'a) -> (exn -> ML 'a) -> ML 'a
