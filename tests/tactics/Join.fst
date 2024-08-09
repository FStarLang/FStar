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
module Join

open FStar.Tactics.V2

(* Basic test *)
assume val p : int -> prop
let test (x:int) (_:squash (p x)) = assert (p x /\ p x) by (
  split ();
  join()
  )

val p16 : x:int -> Lemma (x == 16 ==> pow2 x == 65536) [SMTPat (pow2 x)]
let p16 _ = assert_norm (pow2 16 == 65536)

let hard = pow2 20 == 1048576

assume val phi : Type
assume val psi : Type
assume val lem : squash hard -> Lemma phi

(* Making sure it can be proven *)
let _ = assert hard

let repeat' t = let _ = repeat t in ()
let implies_intro' () = let _ = implies_intro () in ()

let formula =
   (phi /\ (psi ==> phi) /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ (False ==> phi)
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ (phi ==> True)
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi
 /\ phi /\ phi /\ phi /\ phi /\ phi /\ phi )

let tau b =
    norm [delta];
    repeatseq (fun () -> first [split; implies_intro'; (fun () -> apply_lemma (`lem))]);
    if b then
        repeat' join; // this line makes the thing 20 times faster
    dump "Final state"

let test1 (x y z : nat) =
    assert formula by (tau false)

let test2 (x y z : nat) =
    assert formula by (tau true)
