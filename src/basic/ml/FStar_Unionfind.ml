(* Persistent union-find implementation adapted from
   https://www.lri.fr/~filliatr/puf/ *)

type 'a pa_t = 'a data ref
and 'a data =
  | PArray of 'a array
  | PDiff of int * 'a * 'a pa_t

let pa_create n v = ref (PArray (Array.make n v))
let pa_make = pa_create

let pa_init n f = ref (PArray (Array.init n f))

(* we rewrite it using CPS to avoid a possible stack overflow *)
let rec pa_rerootk t k = match !t with
  | PArray _ -> k ()
  | PDiff (i, v, t') ->
    pa_rerootk t' (fun () -> begin match !t' with
        | PArray a as n ->
          let v' = a.(i) in
          a.(i) <- v;
          t := n;
          t' := PDiff (i, v', t)
        | PDiff _ -> assert false end; k())

let pa_reroot t = pa_rerootk t (fun () -> ())

let pa_get t i = match !t with
  | PArray a ->
    a.(i)
  | PDiff _ ->
    pa_reroot t;
    begin match !t with PArray a -> a.(i) | PDiff _ -> assert false end

let pa_set t i v =
  pa_reroot t;
  match !t with
  | PArray a as n ->
    let old = a.(i) in
    if old == v then
      t
    else begin
      a.(i) <- v;
      let res = ref n in
      t := PDiff (i, old, res);
      res
    end
  | PDiff _ ->
    assert false


type puf_t = {
  mutable father: int pa_t; (* mutable to allow path compression *)
  c: int pa_t; (* ranks *)
}

let puf_create n =
  { c = pa_create n 0;
    father = pa_init n (fun i -> i) }

(* return both rep and previous version of parent array *)
let rec puf_find_aux f i =
  let fi = pa_get f i in
  if fi == i then
    f, i
  else
    let f, r = puf_find_aux f fi in
    let f = pa_set f i r in
    f, r

let puf_find h x =
  let f,rx = puf_find_aux h.father x in h.father <- f; rx

let puf_union h x y =
  let rx = puf_find h x in
  let ry = puf_find h y in
  if rx != ry then begin
    let rxc = pa_get h.c rx in
    let ryc = pa_get h.c ry in
    if rxc > ryc then
      { h with father = pa_set h.father ry rx }
    else if rxc < ryc then
      { h with father = pa_set h.father rx ry }
    else
      { c = pa_set h.c rx (rxc + 1);
        father = pa_set h.father ry rx }
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

let log : ((tx * (unit -> unit) list) list) ref = ref []

let log_undo x = match !log with
    | (tx, undos)::rest -> log := (tx, x::undos)::rest
    | _ -> () (* no current transaction; nothing to log  *)

let new_transaction =
    let tx_ctr = ref 0 in
    fun () ->
        let tx = incr tx_ctr; !tx_ctr in
        log := (tx, [])::!log ;
        tx

(* apply undo logs for all transactions succeeding tx, including tx itself  *)
let rollback tx =
    let rec aux = function
        | [] -> failwith "Transaction identifier is invalid"
        | (tx', undo)::rest ->
          List.iter (fun f -> f()) undo;
          if tx=tx'
          then log := rest
          else aux rest in
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

let counter = ref 0

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
