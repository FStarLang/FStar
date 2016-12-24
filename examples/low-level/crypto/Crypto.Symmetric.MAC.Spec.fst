module Crypto.Symmetric.MAC.Spec

open Crypto.Symmetric.Bytes 
open Crypto.Indexing
module GS = Crypto.Symmetric.GF128.Spec
module PS = Crypto.Symmetric.Poly1305.Spec

let elem (a:macAlg) =
  match a with 
  | POLY1305 -> PS.elem
  | GHASH    -> GS.elem

let zero a : elem a = 
  match a with 
  | POLY1305 -> PS.zero
  | GHASH    -> GS.zero


let op_Plus_At (#a:macAlg) (e1:elem a) (e2:elem a) : Tot (elem a) =	
  match a with
  | POLY1305 -> PS.op_Plus_At e1 e2
  | GHASH -> GS.op_Plus_At e1 e2

let op_Star_At (#a:macAlg) (e1:elem a) (e2:elem a) : Tot (elem a) =	
  match a with
  | POLY1305 -> PS.op_Star_At e1 e2
  | GHASH -> GS.op_Star_At e1 e2
    
type polynomial a = Seq.seq (elem a)

val update: #a:macAlg -> r:elem a -> acc:elem a -> e:elem a -> Tot (acc':elem a)
let update #a r acc e = 
    (acc +@ e) *@ r

(** Polynomial evaluation *)
val poly_eval: #a:macAlg -> p:polynomial a -> r:elem a -> Tot (elem a) (decreases (Seq.length p))
let rec poly_eval #a p r =
    if Seq.length p = 0 then zero a
    else 
      let h = SeqProperties.head p in 
      let t = SeqProperties.tail p in 
      update #a r (poly_eval t r) h

(** message words (not necessarily a full word. *)
let wlen = 16ul
type word = b:bytes{Seq.length b <= UInt32.v wlen}
type word_16 = b:bytes{Seq.length b = UInt32.v wlen}

(** Encode a word of a message as a field element *)
val encode: #a:macAlg -> w:word_16 -> Tot (elem a)
let encode #a w =
  match a with 
  | POLY1305 -> PS.encode w
  | GHASH    -> GS.encode w


type text = Seq.seq word_16
val encode_text: #a:macAlg -> x:text -> Tot (polynomial a) (decreases (Seq.length x))
let rec encode_text #a x =
    if Seq.length x = 0 then Seq.createEmpty #(elem a)
    else 
      let h = SeqProperties.head x in 
      let t = SeqProperties.tail x in 
      SeqProperties.cons (encode #a h) (encode_text #a t)

let taglen = 16ul
type tag = word_16

val decode: #a:macAlg -> e:elem a -> Tot (w:word_16)
let decode #a e =
  match a with 
  | POLY1305 -> PS.decode e
  | GHASH    -> GS.decode e


val finish: #a:macAlg -> acc:elem a -> s:tag -> Tot tag
let finish #a acc s = 
  match a with 
  | POLY1305 -> PS.finish acc s
  | GHASH    -> GS.finish acc s


val mac_poly: #a:macAlg -> x:text -> r: elem a -> s: tag -> Tot tag 
let mac_poly #a x r s =
    let p = encode_text #a x in
    let v = poly_eval #a p r in
    finish #a v s


    