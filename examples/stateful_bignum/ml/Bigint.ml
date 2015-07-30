
type int64 =
int

type integer =
int

type u8 =
int

let ocaml63 = 63

type template =
Support.Prims.nat  ->  Support.Prims.nat

type template_const =
template

type tint = int

type tarray =
tint array

type bigint =
| Bigint63 of tarray * template

let wordSize = (fun b -> (match (b) with
| Bigint63 (_, _) -> 63))

let get_content = (fun b i -> (match (b) with
| Bigint63 (data, t) -> data.(i)))

let get_length = (fun b -> (match (b) with
| Bigint63 (data, t) -> Array.length data))

(*
let get = (fun b n -> (match (b) with
| Bigint63 (data, t) -> begin
(let _46688 = (Support.Array.index data n)
in (match (_46688) with
| (size, v) -> begin
v
end))
end))
 *)


let geta a i =
  a.(i)

let upda a i v =
  a.(i) <- v

let get = fun b n ->
  match b with 
  | Bigint63 (data, _) -> data.(n)

let getTemplate = (fun b -> (match (b) with
| Bigint63 (_, t) -> t))

(*
let updateBigint = (fun b idx v -> (match (b) with
| Bigint63 (data, t) -> data.(idx) <- v))
 *)

let updateBigint = (fun b idx v -> (match (b) with
| Bigint63 (data, t) -> data.(idx) <- v))

let zero_tint = 0

let one_tint = 1

let zero_bigint = Bigint63 ((Support.Array.create 1 zero_tint), (fun x -> 63))

let one_bigint = Bigint63 ((Support.Array.create 1 one_tint), (fun x -> 63))

let mk_zero_bigint = (fun size template -> Bigint63 ((Support.Array.create size zero_tint), template))

let copy a = 
  match a with
  | Bigint63(array,t) -> Bigint63(Array.copy array, t)

let mk_one_bigint = (fun size template -> (let one = Bigint63 ((Support.Array.create size zero_tint), template)
in (let _46721 = (updateBigint one 0 one_tint)
in one)))

let mk_tint a size value = (value)

type array_pool =
{free_arrays : tarray list ref; array_size : Support.Prims.pos ref; pool_size : Support.Prims.nat ref}

let pool = {free_arrays = (ref []); array_size = (ref 1); pool_size = (ref 0)}

let initialize_pool = (fun max size -> (match (max) with
| 0 -> begin
(let _46730 = (pool.array_size := size)
in (pool.pool_size := max))
end
| _ -> begin
(pool.free_arrays := ((Support.Array.create size zero_tint))::(! (pool.free_arrays)))
end))

let get_from_pool = (fun size -> (match (((! (pool.free_arrays)), size)) with
| (hd::tl, _) -> begin
if (size = (! (pool.array_size))) then begin
(let _46746 = (pool.free_arrays := tl)
in hd)
end else begin
(Support.Array.create size zero_tint)
end
end
| (_, _) -> begin
(Support.Array.create size zero_tint)
end))

let return_to_pool = (fun a -> (pool.free_arrays := (a)::(! (pool.free_arrays))))




