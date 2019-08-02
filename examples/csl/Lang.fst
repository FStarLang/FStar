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
module Lang

(*
 * An encoding of separation logic in F*.
 * We consider a deeply embedded language of commands and write a wp transformer that computes
 * the wp in separation logic style.
 * Then we manipulate those wps using tactics for finding the frames.
 * Once the wps become "first-order" (after the existentials for heap frames have been solved),
 * they are then sent to Z3.
 *)

open FStar.SL.Heap

type t = UInt64.t
type addr = ref t

let st_wp (a:Type0) = (a -> heap -> Type0) -> heap -> Type0

noeq type command :Type0 -> Type =
  | Return: #a:Type -> v:a -> command a
  | Read  : id:addr -> command t
  | Write : id:addr -> v:t -> command unit
  | Alloc : command addr
  | Bind  : #a:Type0 -> #b:Type0 -> c1:command a -> c2:(a -> command b) -> command b

(*
 * wp computation
 * The initial heap for the commands is just the footprint of the command.
 *)
let rec wpsep_command (#a:Type0) (c:command a) :st_wp a
  = match c with
    | Return #a x ->
      fun p h0 -> (is_emp h0) /\ p x h0  //Return does not touch the heap, so we run it on emp

    | Read r ->
      //Read only needs to touch the reference r in the heap, we run it on the singleton heap
      fun p h0 -> (exists (x:t). h0 == (points_to r x)) /\ (forall (x:t). h0 == (points_to r x) ==> p x h0)

    | Write r y ->
      //Write only needs to touch the reference r in the heap, we run it on the singleton heap
      fun p h0 -> (exists (x:t). h0 == (points_to r x)) /\ (forall (h1:heap). h1 == (points_to r y) ==> p () h1)

    | Alloc ->
      //Alloc also runs on emp
      fun p h0 -> (is_emp h0) /\ (forall (r:addr) (h1:heap). (h1 == points_to r 0uL) /\ (get_next_addr h1 == get_next_addr h0 + 1) ==> p r h1)
    | Bind #a #b c1 c2 ->
      (*
       * We are running (c1; c2) on an input heap h3.
       * In the separation logic style, we will partition the heaps and run commands on the partitions.
       * The way we are going to do it is, we first partition h3 into two disjoint heaps h2' and h2'',
       * and run c1 on h2', let's say the output heap of c1 is then h1.
       * We now join h1 with h2'' (the second partition of the original heap), and partition the resulting heap
       * again into h1' and h1'', where c2 runs on h1' resulting in h2.
       * The final heap is then join of h2 and h1''.
       *)
      FStar.Classical.forall_intro (FStar.WellFounded.axiom1 #a #(command b) c2);
      fun p h3 -> exists (h2':heap) (h2'':heap). h3 == join_tot h2' h2'' /\
     (wpsep_command c1) (fun x h1 -> exists (h1':heap) (h1'':heap). (join_tot h1 h2'') == (join_tot h1' h1'') /\
     (wpsep_command (c2 x)) (fun y h2 -> p y (join_tot h2 h1'')) h1') h2'

(*
 * The wp that we compute for a command only talks about the footprint of the command.
 * So, we need to partition the global heap as well, and run the command on its partition.
 *
 * Given the input heap h0, we partition it into h0' and h0'', run the command on h0', resulting in h1',
 * and return the final heap as join h1' h0''.
 *)
let lift_wpsep (#a:Type0) (wp_sep:st_wp a) :st_wp a
  = fun p h0 -> exists (h0':heap) (h0'':heap). h0 == (join_tot h0' h0'') /\ wp_sep (fun x h1' -> p x (join_tot h1' h0'')) h0'
