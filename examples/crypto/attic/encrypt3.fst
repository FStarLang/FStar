(*
   Copyright 2008-2018 Microsoft Research

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
module SymEnc (* a multi-key symmetric variant; for simplicity: (1) only using AES above; and (2) parsing is complete *)

type r = AES.plain

(* CPA variant: *) 
opaque type Encrypted: #k: Type -> p:Type -> k -> AES.bytes -> Type         (* an opaque predicate, keeping track of honest encryptions *)
type cipher (p:Type) (k:Type) (key:k) = c:AES.cipher { Encrypted p key c }  

type keyT: Type -> Type = 
  | Ideal    : p:Type -> AES.key -> i:int -> keyT p (* maybe no need to keep plain/repr around *)
  | Concrete : p:Type -> AES.key -> i:int -> keyT p  

type scheme: Type -> Type =
  | Scheme:  p:Type -> k:Type -> 
             keyrepr: (k -> AES.key) -> 
             keygen:  (bool -> k) ->   
             encrypt: (key:k -> p -> cipher p k key) ->
             decrypt: (key:k -> cipher p k key -> p) -> 
             scheme p 



type entry (p:Type) (k:Type) = 
  | Entry : key:k -> c:cipher p k key -> plain:p -> entry p k

val create: p: Type -> plain: (r -> p) -> repr: (p -> r) -> scheme p 
let create (p:Type) plain repr = 
  let c = ST.alloc 0 in
  let log : ref (list (entry p (keyT p))) = ST.alloc [] in

  let keygen : bool -> keyT p = fun safe ->
    let i = !c in
    c := !c + 1;
    let kv = AES.gen() in
    if safe
    then Ideal    p kv i 
    else Concrete p kv i in

  let keyrepr k : AES.key = 
    match k with 
    | Ideal kv _ -> failwith "no way!"
    | Concrete kv _ -> kv in

  let encrypt: (k:keyT p -> p -> cipher p (keyT p) k) = fun k text ->
    match k with
    | Ideal kv _ -> 
       let c = AES.enc kv AES.dummy in
       assume (Encrypted p k c); 
       log := Entry k c text :: !log; 
       c

    | Concrete kv _ -> 
       let rep = repr text in    (* NS: need the let-binding because repr is impure and we can't substitute it in the type of 'enc' *) 
       let c = AES.enc kv rep in
       assume (Encrypted p k c); 
       c in
    

  let decrypt: key:keyT p -> cipher p (keyT p) key -> p = fun k c ->
    match k with 
    | Ideal kv _ -> (match List.find (fun (Entry k' c' _) -> k=k' && c= c') !log with 
                     | Some e -> Entry.plain e
                     | _ -> failwith "never")
    | Concrete kv _ -> plain (AES.dec kv c)  in

  Scheme p (keyT p) keyrepr keygen encrypt decrypt
   
module SampleEncrypt
open SymEnc
let plain (x:AES.plain) = x
let repr (x:AES.plain) = x

let test() =
  let p = failwith "nice bytes" in
  let Scheme '_ 'k keyrepr keygen encrypt decrypt = SymEnc.create (AES.plain) plain repr in
  let k0 = keygen true in
  let k1 = keygen true in
  let c = encrypt k0 p in
  let p' = decrypt k0 c in
  //assert( p == p');           // this should eventually succeed, once we prove functional correctness
  (* let p'' = decrypt k1 c in     // this rightfully triggers an error *)
  ()


module EncryptThenMAC
open SymEnc

type p = AES.plain

let plain (x:AES.plain) = x
let repr (x:AES.plain) = x
 
let s = SymEnc.create p plain repr
type k = Scheme.k s

type k2 =
  | Key:  ke:k -> MAC3.pkey (SymEnc.Encrypted (Scheme.p s) ke) -> k2

type cipher = (AES.cipher * MAC3.tag)

val decrypt: key:k2 -> cipher -> option (Scheme.p s)
let decrypt (Key ke ka) (c,tag) =
  if MAC3.verify ka c tag
  then Some(Scheme.decrypt s ke c)
  else None

val keygen: unit -> k2
let keygen() =
  let ke = Scheme.keygen s true in
  let ka = MAC3.keygen (SymEnc.Encrypted (Scheme.p s) ke) in
  Key ke ka

val encrypt: key:k2 -> plain:Scheme.p s -> cipher
let encrypt (Key ke ka) plain =
  let c = Scheme.encrypt s ke plain in
  (c, MAC3.mac ka c)

