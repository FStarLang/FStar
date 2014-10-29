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


module Vector

type vector 'a : int => Type =
  | VNil : vector 'a 0
  | VCons : 'a -> n:int -> vector 'a n -> vector 'a (n+1)

(* type vector2 'a : nat => Type = *)
(*   | VNil2 : vector2 'a 0 *)
(*   | VCons2 : 'a -> n:nat -> vector2 'a n -> vector2 'a (n+1) *)

(* val head: n:(n:int{n > 0}) -> vector 'a n -> 'a *)
(* let head n v = *)
(*   match v with *)
(*     | VNil -> assert false; failwith "Dead code" *)
(*     | VCons x n xs -> x *)
