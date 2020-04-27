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
module Bug260

type pnat =
  | O : pnat
  | S : pnat -> pnat

type validity : n:pnat -> Type =
  | VSucc : n:pnat -> Tot (validity (S n))

(* val bad : t:pnat -> Tot (validity (S (S t)))           (\* wrong type: *\) *)
val bad : t:pnat -> Tot (validity (S t)) //-- right type:
let bad t = VSucc t

(* we could have probably proved false with a variant of this *)
type validity' : n:pnat -> Type =
  | VSucc' : n:pnat -> (validity' n) -> Tot (validity' (S n))

val validity'_empty : n:pnat -> validity' n -> Lemma (requires True) (ensures (False))
let rec validity'_empty n h =
  match h with
  | VSucc' n' h' -> validity'_empty n' h'

assume val bad' : t:pnat -> Tot (validity' (S (S t)))

val ff : unit -> Lemma (requires True) (ensures (False))
let ff () = validity'_empty (S (S O)) (bad' O)
