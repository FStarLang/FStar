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
module FStar.Option
let isSome = function
  | Some _ -> true
  | None -> false
let isNone o = not (isSome o)
let map f = function
  | Some x -> Some (f x)
  | None -> None
let get = function
  | Some x -> x
  | None -> failwith "Option.get called on None"
