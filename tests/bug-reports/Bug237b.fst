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
module Bug237b

(* Can only reproduce one of the problems with k_foralle.
   The others only appear in tinyfstar-new.fst for now. *)

type knd =
  | KType : knd
  | KKArr : knd -> knd

val ktsubst_beta : knd -> Tot knd
let ktsubst_beta k = k

val tconsts : unit -> Tot knd
let tconsts () = KKArr KType

type kinding : k:knd -> Type =
| KConst : kinding (tconsts())
| KTApp : #k':knd -> hk1:kinding (KKArr k') -> kinding (ktsubst_beta k')

val k_foralle : u:unit -> Tot (kinding KType)
let k_foralle () =  KTApp (* KType *) KConst
(* Problem: without the annotation and the explicit k' in KTApp
   this causes "Unresolved implicit argument" *)
