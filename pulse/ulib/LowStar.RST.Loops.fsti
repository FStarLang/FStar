module LowStar.RST.Loops

open LowStar.Resource
open LowStar.RST
module HS = FStar.HyperStack
module AR = LowStar.RST.Array
module A = LowStar.Array
module U32 = FStar.UInt32
open FStar.Mul

inline_for_extraction
val while:
    res:resource
  -> inv: (res.t -> Type0)
  -> guard: (res.t -> GTot bool)
  -> test: (unit -> RST bool
                      (res)
                      (fun _ -> res)
                      (requires fun h -> inv (sel (view_of res) h))
                      (ensures fun h0 b h1 -> b == guard (sel (view_of res) h0) /\
                               sel (view_of res) h0 == sel (view_of res) h1))
  -> body: (unit -> RST unit
                      (res)
                      (fun _ -> res)
                      (requires fun h -> guard (sel (view_of res) h))
                      (ensures fun _ _ h -> inv (sel (view_of res) h)))
  -> RST unit
        (res)
        (fun _ -> res)
        (requires fun h -> inv (sel (view_of res) h))
        (ensures fun _ _ h -> inv (sel (view_of res) h) /\ ~(guard (sel (view_of res) h)))


val iteri_chunks:
  #a: Type ->
  #inner: resource ->
  b: A.array a ->
  chunk_size: U32.t{U32.v chunk_size > 0} ->
  #f_pre: (chunk:A.array a{A.length chunk = chunk_size} -> HS.mem ->  Type) ->
  #f_post: (chunk: A.array a{A.length chunk = chunk_size} -> HS.mem -> unit -> HS.mem -> Type) ->
  f: (
    i:U32.t{U32.v i < U32.v chunk_size} ->
    chunk: A.array a{A.length chunk = chunk_size} ->
    RST unit
      (AR.array_resource chunk <*> inner)
      (fun _ -> AR.array_resource chunk <*> inner)
      (fun h0 -> f_pre chunk h0)
      (fun h0 u h1 -> f_post chunk h0 u h1)
  ) ->
  RST unit
    (AR.array_resource b <*> inner)
    (fun _ -> AR.array_resource b <*> inner)
    (fun h0 ->
      forall (i:U32.t{(U32.v i + 1) * U32.v (chunk_size) < A.vlength b}). f_pre ((A.gsub b U32.(i *^ chunk_size) chunk_size)) h0
    )
    (fun h0 u h1 ->
      forall (i:U32.t{(U32.v i + 1) * U32.v (chunk_size) < A.vlength b}). f_post ((A.gsub b U32.(i *^ chunk_size) chunk_size)) h0 u h1
    )
