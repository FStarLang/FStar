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
module Inverse
open FStar.Seq
type bytes = seq FStar.UInt8.byte
type lbytes (l:int) = b:bytes{length b = l}

type pinverse (#a:Type) (#b:Type) (r:(b -> b -> Type)) ($f:(a -> Tot b)) : Type = 
    (y:b -> Tot (xopt:option a{(forall (x:a). r (f x) y <==> (xopt = Some x))}))

type t = 
  | A 
  | B

val t2b : t -> Tot (lbytes 1)
let t2b = function
  | A -> Seq.create 1 1uy
  | B -> Seq.create 1 2uy

val b2t : pinverse Seq.equal t2b
let b2t b = match Seq.index b 0 with
  | 1uy -> Some A
  | 2uy -> Some B
  | _ -> None

(* type s = *)
(*   | C of t *)

(* val s2b : s -> Tot (lbytes 1) *)
(* let s2b = function *)
(*   | C A -> Seq.create 1 1uy *)
(*   | C B -> Seq.create 1 2uy *)

(* val b2s : pinverse Seq.Eq s2b *)
(* let b2s b = match Seq.index b 0 with *)
(*   | 1uy -> Some (C A) *)
(*   | 2uy -> Some (C B) *)
(*   | _ -> None *)

(* type s = *)
(*   | C : t -> t -> s *)

(* val s2b : s -> Tot (lbytes 1) *)
(* let s2b = function *)
(*   | C A A -> Seq.create 1 1uy *)
(*   | C A B -> Seq.create 1 2uy *)
(*   | C B A -> Seq.create 1 3uy *)
(*   | C B B -> Seq.create 1 4uy *)

(* val b2s : pinverse Seq.Eq s2b *)
(* let b2s b = match Seq.index b 0 with *)
(*   | 1uy -> Some (C A A) *)
(*   | 2uy -> Some (C A B) *)
(*   | 3uy -> Some (C B A) *)
(*   | 4uy -> Some (C B B) *)
(*   | _ -> None *)
  
(* type s = *)
(*   | C of (t * t) *)

(* val s2b : s -> Tot (lbytes 1) *)
(* let s2b = function *)
(*   | C (A, A) -> Seq.create 1 1uy *)
(*   | C (A, B) -> Seq.create 1 2uy *)
(*   | C (B, A) -> Seq.create 1 3uy *)
(*   | C (B, B) -> Seq.create 1 4uy *)

(* val b2s : pinverse Seq.equal s2b *)
(* let b2s b = match Seq.index b 0 with *)
(*   | 1uy -> Some (C (A, A)) *)
(*   | 2uy -> Some (C (A, B)) *)
(*   | 3uy -> Some (C (B, A)) *)
(*   | 4uy -> Some (C (B, B)) *)
(*   | _ -> None *)
  

