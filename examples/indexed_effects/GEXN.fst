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
module GEXN

(* 
   A proof-of-concept example of a Graded Dijkstra Monad---the EXN monad graded by the set of allowed exception names 
*)


open FStar.Set

let exn = string

let gex (a:Type) = unit -> M ((set exn) * either a exn)

(* If DM4F would accept it, would prefer to use the more precise spec below *)

let gex' (a:Type) = unit -> M (s:set exn & (either a (e:exn{mem e s})))

(* Monad definition *)
val return_gex : (a:Type) -> (x:a) -> gex a
let return_gex a x = fun _ -> empty , Inl x

val bind_gex : (a:Type) -> (b:Type) -> (f:gex a) -> (g:a -> gex b) -> gex b
let bind_gex a b f g = fun _ ->
  let (s,r) = f () in
  match r with
  | Inr e -> s , Inr e
  | Inl x -> g x ()

let raise0 (a:Type) (e:exn) : gex a = fun _ -> singleton e , Inr e

reifiable reflectable new_effect {
  GEXN : (a:Type) -> Effect
  with repr     = gex
     ; bind     = bind_gex
     ; return   = return_gex
     ; raise (#a:Type) = raise0 a
}


(* Syntactic sugar packaging an allowed exceptions index and EXN WP *)

let gexn_wp (a:Type) = unit -> (set exn * either a exn -> Type0) -> Type0
let exn_wp (a:Type)  = (either a exn -> Type0) -> Type0

unfold
let (><) (#a:Type) (s:set exn) (wp:exn_wp a) : gexn_wp a
  = fun _ post -> wp (fun e -> post (s,e))

let raise (#a:Type) (e:exn) : GEXN a (singleton e >< (fun p -> p (Inr e)))
  = GEXN?.raise e
