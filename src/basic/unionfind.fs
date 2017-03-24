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

(* Persistent union-find implementation adapted from
   https://www.lri.fr/~filliatr/puf/ *)

(* Persistent arrays *)
type pa_t<'a> = ref<data<'a>>
and data<'a> =
    | PArray of array<'a>
    | PDiff of int * 'a * pa_t<'a>

let pa_create n v = ref (PArray (Array.make n v))

let pa_init n f = ref (PArray (Array.init n f))

let rec pa_rerootk t k = match !t with
    | PArray _ -> k ()
    | PDiff (i, v, t') ->
        pa_rerootk t' (fun () -> begin match !t' with
            | PArray a ->
                let v' = a.[i] in
                a.[i] <- v;
                t := PArray a;
                t' := PDiff (i, v', t)
            | PDiff _ -> failwith "Impossible" end; k())

let pa_reroot t = pa_rerootk t (fun () -> ())

let pa_get t i = match !t with
    | PArray a -> a.[i]
    | PDiff _ ->
        pa_reroot t;
        begin match !t with
            | PArray a -> a.[i]
            | PDiff _ -> failwith "Impossible"
        end

let pa_set t i v =
    pa_reroot t;
    match !t with
        | PArray a ->
            let old = a.[i] in
            if old = v then t else
                begin
                    a.[i] <- v;
                    let res = ref (PArray a) in
                    t := PDiff (i, old, res);
                    res
                end
        | PDiff _ -> failwith "Impossible"


(* Union-find implementation based on persistent arrays *)
type puf_t<'a> = {
    mutable parent: pa_t<int>;
    ranks: pa_t<int>;
}

let puf_create n =
    { ranks = pa_create n 0;
      parent = pa_init n (fun i -> i) }

(* implements path compression, returns new array *)
let rec puf_find_aux f i =
    let fi = pa_get f i in
    if fi = i then
        f, i
    else
        let f, r = puf_find_aux f fi in
        let f = pa_set f i r in
        f, r

let puf_find h x =
    let f, rx = puf_find_aux h.parent x in
        h.parent <- f;
        rx

let puf_union h x y =
    let rx = puf_find h x in
    let ry = puf_find h y in
    if rx <> ry then begin
        let rxc = pa_get h.ranks rx in
        let ryc = pa_get h.ranks ry in
        if rxc > ryc then
            { parent = pa_set h.parent ry rx; ranks = h.ranks}
        else if rxc < ryc then
            { parent = pa_set h.parent rx ry; ranks = h.ranks}
        else
            { parent = pa_set h.parent ry rx;
              ranks = pa_set h.parent ry rx; }
        end else
            h

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
