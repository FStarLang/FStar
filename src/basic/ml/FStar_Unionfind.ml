(* Unionfind with path compression but without ranks *)
(* Provides transacational updates, based on a suggeestion from Francois Pottier *)

type 'a cell = {mutable contents : 'a contents }
and 'a contents =
  | Data of 'a list * int
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
  | Data (_, id) -> id
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
