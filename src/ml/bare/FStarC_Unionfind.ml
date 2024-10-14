(* Persistent union-find implementation adapted from
   https://www.lri.fr/~filliatr/puf/ *)

open FStarC_Compiler_Effect
open FStarC_Compiler_Util

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
        | PArray a ->
            let v' = a.(i) in
            a.(i) <- v;
            t := PArray a;
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

let pa_set (t: 'a pa_t) (i: int) (v: 'a): 'a pa_t =
  pa_reroot t;
  match !t with
  | PArray a ->
      let old = a.(i) in
      a.(i) <- v;
      let res = mk_ref (PArray a) in
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
      if (pa_length t == l) then begin
        let arr_tail = Array.make l empty in
        arr_tail.(0) <- x;
        t := PArray (Array.append a arr_tail)
      end else
        a.(l) <- x
    | PDiff _ -> failwith "Impossible"


(* Union-find implementation based on persistent arrays *)
type 'a puf = {
  (* array of parents of each node
      contains either path or root element *)
  mutable parent: (int, 'a) FStar_Pervasives.either pa_t; (* mutable to allow path compression *)
  ranks: int pa_t;
  (* keep track of how many elements are allocated in the array *)
  count: int ref
}
type 'a p_uvar = P of int
  [@printer fun fmt x -> Format.pp_print_string fmt "!!!"]
  [@@deriving yojson,show]
  (* failwith "cannot pretty-print a unification variable" *)

let puf_empty () =
    { parent = pa_create 2 (FStar_Pervasives.Inl (-1)) ;
      ranks = pa_create 2 0;
      count = mk_ref 0 }

let puf_fresh (h: 'a puf) (x: 'a): 'a p_uvar =
    let count = !(h.count) in
    pa_new h.parent (FStar_Pervasives.Inr x) count (FStar_Pervasives.Inl (-1));
    pa_new h.ranks 0 count 0;
    h.count := count + 1;
    P count

(* implements path compression, returns new array *)
let rec puf_find_aux f i =
    match (pa_get f i) with
        | FStar_Pervasives.Inl fi ->
            let f, r, id = puf_find_aux f fi in
            let f = pa_set f i (FStar_Pervasives.Inl id) in
            f, r, id
        | FStar_Pervasives.Inr x -> f, FStar_Pervasives.Inr x, i

(* return both rep and previous version of parent array *)
let puf_find_i (h: 'a puf) (x: 'a p_uvar) =
    let x = match x with | P a -> a in
    let f, rx, i = puf_find_aux h.parent x in
        h.parent <- f;
        match rx with
            | FStar_Pervasives.Inr r -> r, i
            | FStar_Pervasives.Inl _ -> failwith "Impossible"

(* only return the equivalence class *)
let puf_id' (h:'a puf) (x:'a p_uvar) : int =
    let _, i = puf_find_i h x in
    i

let puf_id (h: 'a puf) (x: 'a p_uvar): Prims.int =
    Z.of_int (puf_id' h x)

let puf_unique_id (x: 'a p_uvar): Prims.int =
  match x with
  | P a -> Z.of_int a

let puf_fromid (_:'a puf) (id : Prims.int) : 'a p_uvar =
    P (Z.to_int id)

(* only return the rep *)
let puf_find (h: 'a puf) (x: 'a p_uvar) =
    let v, _ = puf_find_i h x in
    v

let puf_equivalent (h:'a puf) (x:'a p_uvar) (y:'a p_uvar) =
    (puf_id' h x) = (puf_id' h y)

let puf_change (h:'a puf) (x:'a p_uvar) (v:'a) : 'a puf =
    let i = puf_id' h x in
    let hp = pa_set h.parent i (FStar_Pervasives.Inr v) in
    { h with parent = hp}

let puf_union (h: 'a puf) (x: 'a p_uvar) (y: 'a p_uvar) =
    let ix = puf_id' h x in
    let iy = puf_id' h y in
    if ix!=iy then begin
        let rxc = pa_get h.ranks ix in
        let ryc = pa_get h.ranks iy in
        if rxc > ryc then
            { parent = pa_set h.parent iy (FStar_Pervasives.Inl ix);
              ranks = h.ranks;
              count = h.count}
        else if rxc < ryc then
            { parent = pa_set h.parent ix (FStar_Pervasives.Inl iy);
              ranks = h.ranks;
              count = h.count}
        else
            { parent = pa_set h.parent iy (FStar_Pervasives.Inl ix);
              ranks = pa_set h.ranks ix (rxc+1);
              count = h.count }
        end else
            h
