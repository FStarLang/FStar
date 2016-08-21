module MtE.CPA

open FStar.Heap
(* open FStar.HyperHeap *)
open FStar.Seq
open FStar.SeqProperties
(* open FStar.Monotonic.RRef *)

open Platform.Bytes
open CoreCrypto

open MtE.Plain


type cipher = AES.cipher



type entry = // records that c is an encryption of p with ad
  | Entry: p:plain -> c:cipher -> entry

let ideal_log : ref (seq entry) = alloc (createEmpty #entry)


abstract type key = AES.key

assume type encrypted: key -> bytes -> Type

let keysize = 16

val keygen: unit -> key
let keygen () =
  AES.gen ()


val encrypt: (k:key) -> (p:plain) -> ST (c:cipher{encrypted k c})
  (requires (fun h -> true))
  (ensures (fun h0 c h1 -> ind_cpa ==> (let s = (Heap.sel h1 ideal_log) in is_Some (seq_find (function Entry c' p' -> c=c') s))))

  (* (ensures (fun h0 c h2 -> true)) *)

(* Playing with the stateful specification style: *)
  (* (ensures (fun h0 c h2 -> ind_cpa ==> (let log = (Heap.sel h2 ideal_log) in exists (i:nat{i < Seq.length log}).  Seq.index log i == Entry p c)) ) *)

 
let encrypt k p =
  let text = if ind_cpa then createBytes AES.psize 0z else repr p in
  let c = (AES.enc k text) in
  if ind_cpa then
    ideal_log := snoc !ideal_log (Entry p c);
  assume(encrypted k c);
  admit();
  c
  

val decrypt: (k:key) -> (c:cipher{encrypted k c}) -> ST (p:plain)
  (* (requires (fun h -> true)) *)
  (requires (fun h -> (let s = (Heap.sel h ideal_log) in is_Some (seq_find (function Entry c' p -> c=c') s))) )

  (ensures (fun h0 c h2 -> true))

(* Playing with the stateful specification style: *)
(*   (requires (fun h -> (let s = (Heap.sel h ideal_log) in is_Some (seq_find (function Entry c' p -> c=c') s))) ) *)

(*   (requires (fun h -> (let log = (Heap.sel h ideal_log) in exists (i:nat{i < Seq.length log}). exists (p:plain).  Seq.index log i = Entry c p) )) *)


let decrypt k c=
  if ind_cpa then 
  begin
    let s = !ideal_log in
    match seq_find (function Entry c' p -> c=c') s with
    | Some e -> (Entry.p e )
  end
  else
    AES.dec k c

let test =
  let p = createBytes 1 0z in
  let k = keygen () in
  let c = (encrypt k (createBytes 32 0z)) in
  assert (encrypted k c);
  ignore (decrypt k c)
