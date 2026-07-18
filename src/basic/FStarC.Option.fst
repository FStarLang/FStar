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
module FStarC.Option

open FStarC.Effect

let map f = function
  | Some x -> Some (f x)
  | None -> None

let must =
  function
  | Some x -> x
  | None -> failwith "FStarC.Option.must: called on None"

let dflt d = function
  | Some x -> x
  | None -> d

let rec find f xs =
  match xs with
  | [] -> None
  | x::xs -> if f x then Some x else find f xs

let bind o f =
  match o with
  | Some x -> f x
  | None -> None

let catch o f =
  match o with
  | Some x -> Some x
  | None -> f ()

let iter f =
  function
  | Some x -> f x
  | None -> ()
