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
module FStar.Option

open FStar.All

inline_for_extraction
val isNone: option 'a -> Tot bool
inline_for_extraction
let isNone = function
  | None -> true
  | Some _ -> false

inline_for_extraction
val isSome: option 'a -> Tot bool
inline_for_extraction
let isSome = function
  | Some _ -> true
  | None -> false

inline_for_extraction
val map: ('a -> ML 'b) -> option 'a -> ML (option 'b)
inline_for_extraction
let map f = function
  | Some x -> Some (f x)
  | None -> None

inline_for_extraction
val mapTot: ('a -> Tot 'b) -> option 'a -> Tot (option 'b)
inline_for_extraction
let mapTot f = function
  | Some x -> Some (f x)
  | None -> None

inline_for_extraction
val get: option 'a -> ML 'a
let get = function
  | Some x -> x
  | None -> failwith "empty option"

let (let?) (x: option 'a) (f: 'a -> option 'b): option 'b
  = match x with
  | Some x -> f x
  | None   -> None

let (and?) (x: option 'a) (y: option 'b): option ('a & 'b)
  = match x, y with
  | Some x, Some y -> Some (x, y)
  | _ -> None
