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
module FStar.Squash

(* Interface for squash types; somehow inspired by:
Quotient Types: A Modular Approach. Aleksey Nogin, TPHOLs 2002.
http://www.nuprl.org/documents/Nogin/QuotientTypes_02.pdf
*)

(* This is a monad *)
val return_squash : #a:Type -> a -> Tot (squash a)

val bind_squash : #a:Type -> #b:Type -> squash a -> (a -> GTot (squash b)) ->
  Tot (squash b)

(* With a special ``push'' operation *)
val push_squash   : #a:Type -> #b:(a -> Type) -> (x:a -> Tot (squash (b x))) -> Tot (squash (x:a -> GTot (b x)))

val get_proof : p:Type ->
  Pure (squash p) (requires p) (ensures (fun _ -> True))

val give_proof : #p:Type -> squash p ->
  Pure unit (requires True) (ensures (fun _ -> p))

val proof_irrelevance : p:Type -> x:squash p ->
                                 y:squash p -> Tot (squash (x == y))

val squash_double_arrow : #a:Type -> #p:(a -> Type) ->
  $f:(squash (x:a -> GTot (squash (p x)))) -> GTot (squash (x:a -> GTot (p x)))

val push_sum : #a:Type -> #b:(a -> Type) ->
  $p:(dtuple2 a (fun (x:a) -> squash (b x))) -> Tot (squash (dtuple2 a b))

val squash_double_sum:  #a:Type -> #b:(a -> Type) ->
  $p:(squash (dtuple2 a (fun (x:a) -> squash (b x)))) -> Tot (squash (dtuple2 a b))

val map_squash : #a:Type -> #b:Type -> squash a -> (a -> GTot b) ->
  Tot (squash b)

val join_squash : #a:Type -> squash (squash a) -> Tot (squash a)
