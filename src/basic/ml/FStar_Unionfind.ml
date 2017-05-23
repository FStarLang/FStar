(* Persistent union-find implementation adapted from
   https://www.lri.fr/~filliatr/puf/ *)

module U = FStar_Util
open U

(* Persistent arrays *)
type 'a pa_t = 'a data ref
and 'a data =
  | PArray of 'a array
  | PDiff of int * 'a * 'a pa_t

let pa_create n v = mk_ref (PArray (Array.make n v))

let pa_init n f = mk_ref (PArray (Array.init n f))

let rec pa_rerootk t k = match !t with
  | PArray _ -> k ()
  | PDiff (i, v, t') ->
      pa_rerootk t' (fun () -> begin match !t' with
        | PArray a as n ->
            let v' = a.(i) in
            a.(i) <- v;
            t := n;
            t' := PDiff (i, v', t)
        | PDiff _ -> failwith "Impossible" end; k())

let pa_reroot t = pa_rerootk t (fun () -> ())

let pa_get t i = match !t with
  | PArray a -> a.(i)
  | PDiff _ ->
      pa_reroot t;
      begin match !t with
        | PArray a -> a.(i)
        | PDiff _ -> failwith "Impossible" end

let pa_set t i v =
  pa_reroot t;
  match !t with
  | PArray a as n ->
      let old = a.(i) in
      if old == v then
        t
      else begin
        a.(i) <- v;
        let res = mk_ref n in
        t := PDiff (i, old, res);
        res
      end
  | PDiff _ -> failwith "Impossible"

(* apply impure function from Array to a persistent array *)
let impure f t =
  pa_reroot t;
  match !t with PArray a -> f a | PDiff _ -> failwith "Impossible"

let pa_length t = impure Array.length t

(* double the array whenever its bounds are reached *)
let pa_new_double t x l empty =
  pa_reroot t;
  match !t with
    | PArray a ->
      if (pa_length t == l) then begin
        let arr_tail = Array.make l empty in
        arr_tail.(0) <- x;
        t := PArray (Array.append a arr_tail)
      end else
        a.(l) <- x
    | PDiff _ -> failwith "Impossible"


(* Union-find implementation based on persistent arrays *)
type 'a puf_t = {
  mutable parent: (int, 'a) either pa_t; (* mutable to allow path compression *)
  ranks: int pa_t;
  (* keep track of how many elements are allocated in the array *)
  count: int ref
}
type 'a puf = 'a puf_t
type 'a p_uvar = P of int

let puf_empty () =
    { parent = pa_create 2 (Inl (-1)) ;
      ranks = pa_create 2 0;
      count = mk_ref 0 }

let puf_fresh (h: 'a puf) (x: 'a) =
    let count = !(h.count) in
    pa_new_double h.parent (Inr x) count (Inl (-1));
    pa_new_double h.ranks 0 count 0;
    h.count := count + 1;
    P count

(* implements path compression, returns new array *)
let rec puf_find_aux f i =
    match (pa_get f i) with
        | Inl fi ->
            let f, r, id = puf_find_aux f fi in
            let f = pa_set f i r in
            f, r, id
        | Inr x -> f, Inr x, i

(* return both rep and previous version of parent array *)
let puf_find_i (h: 'a puf) (x: 'a p_uvar) =
    let x = match x with | P a -> a in
    let f, rx, i = puf_find_aux h.parent x in
        h.parent <- f;
        match rx with
            | Inr r -> r, i
            | Inl _ -> failwith "Impossible"

(* only return the rep *)
let puf_find (h: 'a puf) (x: 'a p_uvar) =
    let v, _ = puf_find_i h x in
    v

let puf_union (h: 'a puf) (x: 'a p_uvar) (y: 'a p_uvar) =
    let rx, ix = puf_find_i h x in
    let ry, iy = puf_find_i h y in
    if rx != ry then begin
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

(* Unionfind with path compression but without ranks *)
(* Provides transacational updates, based on a suggeestion from Francois Pottier *)

type 'a cell = {mutable contents : 'a contents }
and 'a contents =
  | Data of 'a list * int (* data * id *)
  | Fwd of 'a cell

type 'a uvar = 'a cell

exception Impos

type tx = int

let log : ((tx * (unit -> unit) list) list) ref = mk_ref []

let log_undo x = match !log with
  | (tx, undos)::rest -> log := (tx, x::undos)::rest
  | _ -> () (* no current transaction; nothing to log  *)

let new_transaction =
  (* Ugly clash of names *)
  let log' = log in
  let open Pervasives in
  let tx_ctr = ref 0 in
  fun () ->
    let tx = incr tx_ctr; !tx_ctr in
    U.(log' := (tx, [])::!log') ;
    tx

(* apply undo logs for all transactions succeeding tx, including tx itself  *)
let rollback tx =
  let rec aux = function
    | [] -> failwith "Transaction identifier is invalid"
    | (tx', undo)::rest ->
      List.iter (fun f -> f()) undo;
      if tx=tx'
      then log := rest
      else aux rest
  in
  aux !log

(* discard undo logs for all transactions succeeding tx, including tx itself *)
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

let counter = mk_ref 0

let fresh x = counter := !counter + 1; {contents = Data ([x], !counter) }

let rec rep cell = match cell.contents with
  | Data _ -> cell
  | Fwd cell' ->
    if cell == cell'
    then failwith "YIKES! Cycle in unionfind graph"
    else rep cell'

let update x c =
    let cur = x.contents in
    let undo () = x.contents <- cur in
    log_undo undo;
    x.contents <- c

let find x =
    let y = rep x in
    if not (x == y) then update x (Fwd y); (* path compression *)
    match y.contents with
        | Data ((hd::tl), _) -> hd
        | _ -> failwith "impossible"

let uvar_id uv = match (rep uv).contents with
  | Data (_, id) -> Z.of_int id
  | _ -> failwith "impossible"

let union x y =
  let cellX = rep x in
  let cellY = rep y in
    if cellX == cellY then ()
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

let equivalent x y = (rep x)==(rep y)


let puf_test () =
    let (u: string puf) = puf_empty () in
    let u_a = puf_fresh u "a" in
    let u_b = puf_fresh u "b" in
    let u_c = puf_fresh u "c" in
    (print1 "There are %s elements\n" (Printf.sprintf "%i" !(u.count)));
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
    (print1 "Rep of e is %s\n" le);
    (print1 "Rep of a is %s\n" la);
    (print1 "Rep of c is %s\n" lc);
    let u_i = (puf_fresh u "i") in
    let u_i2 = match u_i with | P a -> a in
    (print2 "Id of i and count are %s %s\n" (Printf.sprintf "%i" u_i2) (Printf.sprintf "%i" !(u.count)));
    let li = puf_find u u_i in
    (print1 "Rep of i is %s\n" li);
    let u = puf_union u u_b u_i in
    let li = puf_find u u_i in
    (print1 "Rep of i is %s\n" li);
    (print1 "There are %s elements\n" (Printf.sprintf "%i" !(u.count)))
