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
#light "off"
// (c) Microsoft Corporation. All rights reserved

module Microsoft.FStar.Unionfind
(* Unionfind with path compression but without ranks *)

type cell<'a when 'a : not struct> = {mutable contents : contents<'a> }
and contents<'a when 'a : not struct> = 
  | Data of list<'a> * int
  | Fwd of cell<'a>
type uvar<'a when 'a : not struct> = 'a cell

exception Impos


let counter = ref 0

let fresh x = counter := !counter + 1; {contents = Data ([x], !counter) }
  
let rec rep cell = match cell.contents with 
  | Data _ -> cell
  | Fwd cell' -> rep cell'

let find x = 
    let y = rep x in 
    if not (LanguagePrimitives.PhysicalEquality x y) then x.contents <- Fwd y; //path compression
    match y.contents with
        | Data ((hd::tl), _) -> hd
        | _ -> failwith "impossible"

let uvar_id uv = match (rep uv).contents with
  | Data (_, id) -> id
  | _ -> failwith "impossible"

let union x y = 
  let cellX = rep x in
  let cellY = rep y in
    if LanguagePrimitives.PhysicalEquality cellX cellY then ()
    else match cellX.contents, cellY.contents with
            | Data (dx, ctrx), Data (dy,_) -> 
              cellX.contents <- Data ((dx@dy), ctrx);
              cellY.contents <- Fwd cellX
            | _ -> failwith "impossible"
          
let change x a = 
  let cellX = rep x in
    match cellX.contents with 
	  | Data (_, ctrX) -> 
	    cellX.contents <- Data ([a],ctrX)
      | _ -> failwith "impossible"

let equivalent x y =
  LanguagePrimitives.PhysicalEquality (rep x) (rep y)
