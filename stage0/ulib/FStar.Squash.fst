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

(* This file shows that there is another natural model for some of the
   squash things; for this one it doesn't seem to harm importing this
   file (exposing the implementation); it probably doesn't help either *)

let return_squash (#a:Type) x = ()

let bind_squash (#a:Type) (#b:Type) f g = admit()

let push_squash (#a:Type) (#b:(a->Type)) f = admit()

let get_proof (p:Type) = ()

let give_proof (#p:Type) _ = ()

let proof_irrelevance (p:Type) x y = ()

let squash_double_arrow #a #p f =
    bind_squash f push_squash

let push_sum (#a:Type) (#b:(a -> Type)) ($p : dtuple2 a (fun (x:a) -> squash (b x))) =
    match p with
    | Mkdtuple2 x y ->
        bind_squash #(b x) #(dtuple2 a b) y (fun y' ->
        return_squash (Mkdtuple2 x y'))

let squash_double_sum (#a:Type) (#b:(a -> Type)) (p : squash (dtuple2 a (fun (x:a) -> squash (b x)))) =
    bind_squash p (fun p' -> push_sum p') // Need eta...

let map_squash (#a:Type) (#b:Type) s f =
    bind_squash #a #b s (fun x -> return_squash (f x))

let join_squash (#a:Type) (x:squash (squash a)) =
    bind_squash x (fun x -> x)
