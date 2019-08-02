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
module Bug351b

// copied from FStar.Constructive
type ctrue : Type =
  | I : ctrue

// copied from FStar.Constructive
noeq type cexists (#a:Type) (p:a -> Type) =
  | ExIntro : x:a -> h:p x -> cexists p


// even if the definition of P shouldn't matter below, it actually does
// (everything works if we assume P or if we define it in a simpler way)
type pt (a:Type) = (cexists (fun (x:a) -> ctrue))

// all this works fine if we change to h2':(P p -> Tot unit)
val aux : p:Type -> h:pt p -> a:(Type->Type) -> h2':(a p -> Tot unit) ->
            Pure unit (requires (a == pt)) (ensures (fun _ -> True))
let aux (p:Type) (h:pt p) (a:(Type->Type)) h2' = h2' h
// bug351b.fst(16,37-16,38): Subtyping check failed;
// expected type (a p); got type (P p)
