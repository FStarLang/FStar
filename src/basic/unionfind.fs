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

open FStar.All
open FStar.Util

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
            // if old = v then t else
                begin
                    a.[i] <- v;
                    let res = ref (PArray a) in
                    t := PDiff (i, old, res);
                    res
                end
        | PDiff _ -> failwith "Impossible"

(* apply impure function from Array to a persistent array *)
let impure f t =
  pa_reroot t;
  match !t with PArray a -> f a | PDiff _ -> failwith "Impossible"

let pa_length t = impure Array.length t

(* very inefficient strategy for growing the array *)
let pa_new t x =
    pa_reroot t;
    match !t with
        | PArray a ->
            let new_el = Array.make 1 x in
            t :=  PArray (Array.append a new_el)
        | PDiff _ -> failwith "Impossible"

(* double the array whenever its bounds are reached *)
let pa_new_double t x l empty =
    pa_reroot t;
    (Util.print2 "Length and number of elems are %s %s\n" (sprintf "%i" (pa_length t)) (sprintf "%i" l));
    match !t with
        | PArray a ->
            if (pa_length t = l) then begin
                let arr_tail = Array.make l empty in
                arr_tail.[0] <- x;
                t := PArray (Array.append a arr_tail)
            end else
                a.[l] <- x
        | PDiff _ -> failwith "Impossible"


(* Union-find implementation based on persistent arrays *)
type puf_t<'a when 'a : not struct> = {
    (* array of parents of each node
       contains either path or root element *)
    mutable parent: pa_t<(either<int, 'a>)>;
    ranks: pa_t<int>;
    (* keep track of how many elements are allocated in the array *)
    count: ref<int> }
type puf<'a when 'a : not struct> = puf_t<'a>
type p_uvar<'a> = P of int

let puf_empty () =
    { parent = pa_create 2 (Inl -1) ;
      ranks = pa_create 2 0;
      count = ref 0 }

let puf_fresh (h: puf<'a>) (x: 'a) =
    let count = !(h.count) in
    pa_new_double h.parent (Inr x) count (Inl -1);
    pa_new_double h.ranks 0 count 0;
    h.count := count + 1;
    (P count): p_uvar<'a>

(* implements path compression, returns new array *)
let rec puf_find_aux f i =
    match (pa_get f i) with
        | Inl fi ->
            let f, r, id = puf_find_aux f fi in
            let f = pa_set f i r in
            f, r, id
        | Inr x -> f, Inr x, i

(* return both the rep and its id in the array *)
let puf_find_i (h: puf<'a>) (x: p_uvar<'a>) =
    let x = match x with | P a -> a in
    let f, rx, i = puf_find_aux h.parent x in
        h.parent <- f;
        match rx with
            | Inr r -> r, i
            | Inl _ -> failwith "Impossible"

(* only return the rep *)
let puf_find (h: puf<'a>) (x: p_uvar<'a>) =
    let v, _ = puf_find_i h x in
    v

let puf_union (h: puf<'a>) (x: p_uvar<'a>) (y: p_uvar<'a>) =
    let rx, ix = puf_find_i h x in
    let ry, iy = puf_find_i h y in
    if not (LanguagePrimitives.PhysicalEquality rx ry) then begin
        let rxc = pa_get h.ranks ix in
        let ryc = pa_get h.ranks iy in
        if rxc > ryc then
            { parent = pa_set h.parent iy (Inl ix);
              ranks = h.ranks;
              count = h.count}
        else if rxc < ryc then
            { parent = pa_set h.parent ix (Inl iy);
              ranks = h.ranks;
              count = h.count}
        else
            { parent = pa_set h.parent iy (Inl ix);
              ranks = pa_set h.ranks ix (rxc+1);
              count = h.count }
        end else
            h


(* Stateful interface to persistent unionfind *)
// type uf_t<'a> = ref<puf_t<'a>>
// type p_uvar<'a> = { elem: 'a; id: int; uf: uf_t<'a> }

// let p_uvar_id uv =
//     let f, rx, id = puf_find_aux (!uv.uf).parent uv.id in
//     id

// let p_fresh uf x =
//     let length = pa_length <| (!uf).parent in
//     pa_new (!uf).parent (Inr x);
//     pa_new (!uf).ranks 0;
//     { elem = x; id = length; uf = uf }

// let p_find x =
//     let f = puf_find !x.uf x.id

// let p_change uv c =
//     let f, rx, id = puf_find_aux (!uv.uf).parent uv.id in

// let p_change uv c =
//     match !(uv.uf).[id] with
//         | Inl i -> p_change

// let p_equivalent (x: p_uvar<'a>) (y: p_uvar<'a>): bool =
//     let curr_uf = !p_uf.uf in
//     (puf_find curr_uf x.id) = (puf_find curr_uf y.id)

// let p_union (x: p_uvar<'a>) (y: p_uvar<'a>): unit =
//     p_uf.uf := puf_union (!p_uf.uf) x.id y.id

(* Unionfind with path compression but without ranks *)
(* Provides transacational updates, based on a suggeestion from Francois Pottier *)

type cell<'a when 'a : not struct> = {mutable contents : contents<'a> }
and contents<'a when 'a : not struct> =
  | Data of list<'a> * int
  | Fwd of cell<'a>
type uvar<'a when 'a : not struct> = cell<'a>

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


// type uf_t<'a> = { uf: ref<puf_t>; elems: array<'a> }
// and p_uvar<'a> = { elem: 'a; id: int }

// let p_counter = ref 0
// let (p_uf: uf_t<'a>) = { uf = ref (puf_create 0); elems = Array.empty }

// let p_uvar_id uv =
//     uv.id

// let p_fresh x =
//     p_counter := !p_counter + 1;
//     let length = pa_length <| (!p_uf.uf).parent in
//     pa_new (!p_uf.uf).parent length;
//     pa_new (!p_uf.uf).ranks 0;
//     { elem = x; id = !p_counter }

// let p_find x =
//     let f = puf_find (!p_uf.uf) x.id in
//     Array. get p_uf.elems f

// let p_change (uv: p_uvar<'a>) (c: 'a): unit =
//     p_uf.elems.[uv.id] <- c

// let p_equivalent (x: p_uvar<'a>) (y: p_uvar<'a>): bool =
//     let curr_uf = !p_uf.uf in
//     (puf_find curr_uf x.id)= (puf_find curr_uf y.id)

// let p_union (x: p_uvar<'a>) (y: p_uvar<'a>): unit =
//     p_uf.uf := puf_union (!p_uf.uf) x.id y.id

let puf_test () =
    let (u: puf_t<string>) = puf_empty () in
    let u_a = puf_fresh u "a" in
    let u_b = puf_fresh u "b" in
    let u_c = puf_fresh u "c" in
    (Util.print1 "There are %s elements\n" (sprintf "%i" !(u.count)));
    let u_d = puf_fresh u "d" in
    let u_e = puf_fresh u "e" in
    let u_f = puf_fresh u "f" in
    let u_g = puf_fresh u "g" in
    let u_h = puf_fresh u "h" in
    let le= puf_find u u_e in
    let u = puf_union u u_a u_b in
    let u = puf_union u u_b u_c in
    let la = puf_find u u_a in
    let lc = puf_find u u_c in
    (Util.print1 "Rep of e is %s\n" le);
    (Util.print1 "Rep of a is %s\n" la);
    (Util.print1 "Rep of c is %s\n" lc);
    let u_i = (puf_fresh u "i") in
    let u_i2 = match u_i with | P a -> a in
    (Util.print2 "Id of i and count are %s %s\n" (sprintf "%i" u_i2) (sprintf "%i" !(u.count)));
    let li = puf_find u u_i in
    (Util.print1 "Rep of i is %s\n" li);
    let u = puf_union u u_b u_i in
    let li = puf_find u u_i in
    (Util.print1 "Rep of i is %s\n" li);
    (Util.print1 "There are %s elements\n" (sprintf "%i" !(u.count)))
