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
module ReifyTest

open MRefHeap
open MRefST
open FStar.Preorder


(* The signature of reify for MRefST. *)

assume val reify_ : #a:Type ->
            #pre:st_pre ->
	    #post:(heap -> Tot (st_post a)) ->
            e:(unit -> MRefST a pre post) ->
	    h0:heap ->
	    Pure (a * heap) (pre h0) (fun xh1 -> heap_rel h0 (snd xh1) /\ post h0 (fst xh1) (snd xh1))


(* A small example program demonstrating the unsoundness of the combination of reify_ and recall. *)

val test_reify_recall : unit ->
                        MRefST unit (fun _ -> True) 
	                            (fun _ _ _ -> True)
let test_reify_recall _ = 
  let h0 = ist_get () in
  let m = alloc #nat (fun n m -> b2t (n <= m)) 0 in 

  assume (stable_on_heap m (fun h -> contains m h /\ sel h m > 0));  //temporary, until we chase down the mysterious reason why F* does not accept it

  let x = read m in
  let _ = write m (x + 1) in 
  let h1 = ist_get () in

  let f = fun (x:unit) -> witness m (fun h -> contains m h /\ sel h m > 0) in
  let v = reify_ #unit #(fun h0 -> contains m h0 /\ sel h0 m > 0) #(fun h0 _ h1 -> h0 == h1 /\ ist_witnessed (fun h -> contains m h /\ sel h m > 0)) f in

  let f' = fun (x:unit) -> witness m (fun h -> contains m h /\ sel h m > 3) in
  let v' = reify_ #unit #(fun h0 -> contains m h0 /\ sel h0 m > 3) #(fun _ _ _ -> True) f' in

  let _ = v h1 in    //accepted, as expected

  //let _ = v' h1 in    //rejected, as expected  

  let g = fun (x:unit) -> recall m (fun h -> contains m h /\ sel h m > 0) in
  let w = reify_ #unit #(fun h0 -> ist_witnessed (fun h -> contains m h /\ sel h m > 0)) #(fun h0 _ h1 -> h0 == h1 /\ contains m h1 /\ sel h1 m > 0) g in

  let h2 = ist_get () in

  let _ = w h2 in 
  assert (contains m h2 /\ sel h2 m > 0);      //accepted, as expected

  let _ = w h0 in  
  assert (contains m h0 /\ sel h0 m > 0);      //accepted, demonstrates the unsoundness of the combination of reify_ and recall for IST

  ()
