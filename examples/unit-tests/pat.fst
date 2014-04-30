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

module Patterns

let is_some = function 
  None -> false
  | Some _ -> true 

let get_some = function 
  | None -> failwith "got None"
  | Some x -> x

let bind_opt o f = match o with 
  | None -> None
  | Some x -> f x

let map_opt o f = match o with 
  | None -> None
  | Some x -> Some <| f x
