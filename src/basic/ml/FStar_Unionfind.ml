(* Unionfind with path compression but without ranks *)

type 'a cell = {mutable contents : 'a contents}
 and 'a contents =
   | Data of 'a list * Prims.int
   | Fwd of 'a cell
type 'a uvar = 'a cell

exception Impos

let counter = ref 0

let fresh x = counter := !counter + 1; {contents = Data ([x], !counter) }

let rec rep cell = match cell.contents with
  | Data _ -> cell
  | Fwd cell' ->
     if cell == cell' then
       failwith "YIKES! Cycle in unionfind graph"
     else
       rep cell'

let find x =
  let y = rep x in
  if not (x == y) then x.contents <- Fwd y; (* path compression *)
  match y.contents with
  | Data ((hd::tl), _) -> hd
  | _ -> failwith "impossible"

let uvar_id uv = match (rep uv).contents with
  | Data (_, id) -> id
  | _ -> failwith "impossible"

let union x y =
  let cellX = rep x in
  let cellY = rep y in
  if cellX == cellY then
    ()
  else
    match cellX.contents, cellY.contents with
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
  (rep x) == (rep y)
