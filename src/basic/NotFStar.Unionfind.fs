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
open FSharp.Compatibility.OCaml
open FStar.Pervasives
open FStar.ST
open FStar.All
open FStar.Util

(* Persistent union-find implementation adapted from
   https:  / /www.lri.fr/~filliatr/puf/ *)

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

let pa_set (t:pa_t<'a>) (i:int) (v:'a) : pa_t<'a> =
    pa_reroot t;
    match !t with
        | PArray a ->
            let old = a.[i] in
            a.[i] <- v;
            let res = ref (PArray a) in
            t := PDiff (i, old, res);
            res
        | PDiff _ -> failwith "Impossible"

(* apply impure function from Array to a persistent array *)
let impure f t =
  pa_reroot t;
  match !t with PArray a -> f a | PDiff _ -> failwith "Impossible"

let pa_length t = impure Array.length t

(* double the array whenever its bounds are reached *)
let pa_new t x l empty =
    pa_reroot t;
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
type puf<'a> = {
    (* array of parents of each node
       contains either path or root element *)
    mutable parent: pa_t<(either<int, 'a>)>; (* mutable to allow path compression *)
    ranks: pa_t<int>;
    (* keep track of how many elements are allocated in the array *)
    count: ref<int> }
type p_uvar<'a> = P of int

let puf_empty () =
    { parent = pa_create 2 (Inl -1) ;
      ranks = pa_create 2 0;
      count = ref 0 }

let puf_fresh (h: puf<'a>) (x: 'a) =
    let count = !(h.count) in
    pa_new h.parent (Inr x) count (Inl -1);
    pa_new h.ranks 0 count 0;
    h.count := count + 1;
    (P count): p_uvar<'a>

(* implements path compression, returns new array *)
let rec puf_find_aux f i =
    match (pa_get f i) with
        | Inl fi ->
            let f, r, id = puf_find_aux f fi in
            let f = pa_set f i (Inl id) in
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

(* only return the equivalence class *)
let puf_id (h:puf<'a>) (x:p_uvar<'a>) : int =
    let _, i = puf_find_i h x in
    i

let puf_fromid (_:puf<'a>) (id : int) : p_uvar<'a> =
    P id

(* only return the rep *)
let puf_find (h: puf<'a>) (x: p_uvar<'a>) =
    let v, _ = puf_find_i h x in
    v

let puf_equivalent (h:puf<'a>) (x:p_uvar<'a>) (y:p_uvar<'a>) =
    (puf_id h x) = (puf_id h y)

let puf_change (h:puf<'a>) (x:p_uvar<'a>) (v:'a) : puf<'a> =
    let i = puf_id h x in
    let hp = pa_set h.parent i (Inr v) in
    { h with parent = hp}

let puf_union (h: puf<'a>) (x: p_uvar<'a>) (y: p_uvar<'a>) =
    let ix = puf_id h x in
    let iy = puf_id h y in
    if not (ix=iy) then begin
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
    end
    else h

let puf_test () =
    let (u: puf<string>) = puf_empty () in
    let u_a = puf_fresh u "a" in
    let u_b = puf_fresh u "b" in
    let u_c = puf_fresh u "c" in
    (Util.print1 "There are %s elements\n" (sprintf "%i" !(u.count)));
    let u_d = puf_fresh u "d" in
    let u_e = puf_fresh u "e" in
    let _ = puf_fresh u "f" in
    let u_g = puf_fresh u "g" in
    let u_h = puf_fresh u "h" in
    let le, i_e= puf_find_i u u_e in
    let u = puf_union u u_a u_b in
    let u = puf_union u u_b u_c in
    let la, i_a = puf_find_i u u_a in
    let lb, i_b = puf_find_i u u_b in
    let lc, i_c = puf_find_i u u_c in
    (Util.print2 "Rep of e is %s, i=%s\n" le (sprintf "%i" i_e));
    (Util.print2 "Rep of a is %s, i=%s\n" la (sprintf "%i" i_a));
    (Util.print2 "Rep of b is %s, i=%s\n" lb (sprintf "%i" i_b));
    (Util.print2 "Rep of c is %s, i=%s\n" lc (sprintf "%i" i_c));
    let u_i = (puf_fresh u "i") in
    let u_i2 = match u_i with | P a -> a in
    (Util.print2 "Id of i and count are %s %s\n" (sprintf "%i" u_i2) (sprintf "%i" !(u.count)));
    let li, i_i = puf_find_i u u_i in
    (Util.print2 "Rep of i is %s, i=%s\n" li (sprintf "%i" i_i));
    let lb, i_b = puf_find_i u u_b in
    (Util.print2 "Rep of b is %s, i=%s\n" lb (sprintf "%i" i_b));
    let u = puf_union u u_b u_i in
    let li, i_i = puf_find_i u u_i in
    (Util.print2 "Rep of i is %s, i=%s\n" li (sprintf "%i" i_i));
    let la, i_a = puf_find_i u u_a in
    (Util.print2 "Rep of a is %s, i=%s\n" la (sprintf "%i" i_a));
    let lb, i_b = puf_find_i u u_b in
    (Util.print2 "Rep of b is %s, i=%s\n" lb (sprintf "%i" i_b));
    let lc, i_c = puf_find_i u u_c in
    (Util.print2 "Rep of c is %s, i=%s\n" lc (sprintf "%i" i_c));
    (Util.print1 "%s" "\n");

    let lg, i_g = puf_find_i u u_g in
    (Util.print2 "Rep of g is %s, i=%s\n" lg (sprintf "%i" i_g));
    let lh, i_h = puf_find_i u u_h in
    (Util.print2 "Rep of h is %s, i=%s\n" lh (sprintf "%i" i_h));
    (Util.print1 "%s" "\n");

    let u = puf_union u u_g u_h in
    let lg, i_g = puf_find_i u u_g in
    (Util.print2 "Rep of g is %s, i=%s\n" lg (sprintf "%i" i_g));
    let lh, i_h = puf_find_i u u_h in
    (Util.print2 "Rep of h is %s, i=%s\n" lh (sprintf "%i" i_h));
    (Util.print1 "%s" "\n");

    let u = puf_union u u_h u_e in
    let lg, i_g = puf_find_i u u_g in
    (Util.print2 "Rep of g is %s, i=%s\n" lg (sprintf "%i" i_g));
    let lh, i_h = puf_find_i u u_h in
    (Util.print2 "Rep of h is %s, i=%s\n" lh (sprintf "%i" i_h));
    let le, i_e = puf_find_i u u_e in
    (Util.print2 "Rep of e is %s, i=%s\n" le (sprintf "%i" i_e));
    (Util.print1 "%s" "\n");

    let u = puf_union u u_h u_b in
    let lg, i_g = puf_find_i u u_g in
    (Util.print2 "Rep of g is %s, i=%s\n" lg (sprintf "%i" i_g));
    let lh, i_h = puf_find_i u u_h in
    (Util.print2 "Rep of h is %s, i=%s\n" lh (sprintf "%i" i_h));
    let le, i_e = puf_find_i u u_e in
    (Util.print2 "Rep of e is %s, i=%s\n" le (sprintf "%i" i_e));
    let la, i_a = puf_find_i u u_a in
    (Util.print2 "Rep of a is %s, i=%s\n" la (sprintf "%i" i_a));
    let lb, i_b = puf_find_i u u_b in
    (Util.print2 "Rep of b is %s, i=%s\n" lb (sprintf "%i" i_b));
    let lc, i_c = puf_find_i u u_c in
    (Util.print2 "Rep of c is %s, i=%s\n" lc (sprintf "%i" i_c));
    (Util.print1 "%s" "\n");

    let u = puf_change u u_c "new" in
    let lg, i_g = puf_find_i u u_g in
    (Util.print2 "Rep of g is %s, i=%s\n" lg (sprintf "%i" i_g));
    let lh, i_h = puf_find_i u u_h in
    (Util.print2 "Rep of h is %s, i=%s\n" lh (sprintf "%i" i_h));
    let le, i_e = puf_find_i u u_e in
    (Util.print2 "Rep of e is %s, i=%s\n" le (sprintf "%i" i_e));
    let la, i_a = puf_find_i u u_a in
    (Util.print2 "Rep of a is %s, i=%s\n" la (sprintf "%i" i_a));
    let lb, i_b = puf_find_i u u_b in
    (Util.print2 "Rep of b is %s, i=%s\n" lb (sprintf "%i" i_b));
    let lc, i_c = puf_find_i u u_c in
    (Util.print2 "Rep of c is %s, i=%s\n" lc (sprintf "%i" i_c));
    (Util.print1 "%s" "\n");

    let ld, i_d = puf_find_i u u_d in
    (Util.print2 "Rep of d is %s, i=%s\n" ld (sprintf "%i" i_d));
    (Util.print1 "There are %s elements\n" (sprintf "%i" !(u.count)))
