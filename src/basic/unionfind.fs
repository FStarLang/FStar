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

module FStar.Unionfind
(* Unionfind with path compression but without ranks *)
(* Provides transacational updates, based on a suggeestion from Francois Pottier *)

type cell<'a when 'a : not struct> = {mutable contents : contents<'a> }
and contents<'a when 'a : not struct> =
  | Data of list<'a> * int
  | Fwd of cell<'a>
type uvar<'a when 'a : not struct> = 'a cell

exception Impos

type tx = int

let log : ref<list<(tx * list<(unit -> unit)>)>> = Util.mk_ref []

let log_undo x = match !log with
    | (tx, undos)::rest -> log := (tx, x::undos)::rest
    | _ -> ()//no current transaction; nothing to log

let new_transaction =
    let tx_ctr = ref 0 in
    fun () ->
        let tx = incr tx_ctr; !tx_ctr in
        log := (tx, [])::!log ;
        tx

//apply undo logs for all transactions succeeding tx, including tx itself
let rollback tx =
    let rec aux = function
        | [] -> failwith "Transaction identifier is invalid"
        | (tx', undo)::rest ->
          undo |> List.iter (fun f -> f());
          if tx=tx'
          then log := rest
          else aux rest in
   aux !log

//discard undo logs for all transactions succeeding tx, including tx itself
let commit tx =
    let rec aux = function
        | [] -> failwith "Transaction identifier is invalid"
        | (tx', undo)::rest ->
          if tx=tx'
          then log := rest
          else aux rest in
    aux !log

let update_in_tx r v =
    let old = !r in
    let undo () = r := old in
    log_undo undo;
    r := v

let counter = ref 0

let fresh x = counter := !counter + 1; {contents = Data ([x], !counter) }

let rec rep cell = match cell.contents with
  | Data _ -> cell
  | Fwd cell' ->
    if Util.physical_equality cell cell'
    then failwith "YIKES! Cycle in unionfind graph"
    else rep cell'

let update x c =
    let cur = x.contents in
    let undo () = x.contents <- cur in
    log_undo undo;
    x.contents <- c

let find x =
    let y = rep x in
    if not (LanguagePrimitives.PhysicalEquality x y) then update x (Fwd y); //path compression
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
              update cellX (Data ((dx@dy), ctrx));
              update cellY (Fwd cellX)
            | _ -> failwith "impossible"

let change x a =
  let cellX = rep x in
    match cellX.contents with
	  | Data (_, ctrX) ->
        update cellX (Data ([a],ctrX))
      | _ -> failwith "impossible"

let equivalent x y =
  LanguagePrimitives.PhysicalEquality (rep x) (rep y)
