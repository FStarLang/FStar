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
module Bug775

//"t" that satisfy p for some n
type sats_prop (t:Type) (p:(t -> nat -> Tot prop)) = 
    x:t{exists n. p x n}

val bind_sats_prop: 
    #a:Type
    -> #b:Type
    -> (prop_a:(a -> nat -> Tot prop)) // some condition over a
    -> (prop_b:(b -> nat -> Tot prop)) // some condition over b
    -> s:(sats_prop a prop_a) // a value that, for some an, satisfies prop_a
    // f takes an "a" that satisfies prop a for some an
    // and returns a "b" satisfying prop b for some bn that is greater than min(an)
    -> f:(x:a{exists xn. prop_a x xn} -> Tot (sats_prop b (fun (y:b) (yn:nat) -> forall (xn:nat). (prop_a x xn ==> prop_b y (xn+yn)))))
    -> Tot (sats_prop b prop_b)
let bind_sats_prop #a #b pa pb s f = 
    let y:b = f s in
    y
(*
Subtyping check failed; expected type (sats_prop b pb); got type
(sats_prop b
  (fun y yn -> (l_Forall (fun xn -> (l_imp (pa s xn@0) (pb y@2 (op_Addition xn@0 yn@1)))))))
*)
