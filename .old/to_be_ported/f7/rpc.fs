(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
(* Copyright (c) Microsoft Corporation.  All rights reserved.  *)
#light
module RPC
open Data
open Crypto
open Pi


type fact<'a> =
  | Request of (str * str * str)
  | RecvRequest of (str * str * str)
  | Response of (str * str * str * str)
  | RecvResponse of (str * str * str * str)
  | Bad of str
  | KeyAB of ('a * str * str)
  | Requested of ('a * str)
  | Responded of ('a * str * str)

type payload = str
type keyab = key

let p = Net.http "http://localhost:8080" ""

let service req = 
#if fs
  printf "Received Request %s\n" (istr req);
#endif
  let resp = str "4" in
// (* needed for responses in general *)
// #if f7
//   assume (Pub_s(resp)); 
// #endif
  resp

(*--- AppBegin *)
let mkKeyAB a b = let k = hmac_keygen() in Assume (KeyAB(k,a,b)); k
let request s = concat (utf8(str "Request")) (utf8 s)
let response s t = 
  let sb = utf8 s in
  let tb = utf8 t in
  let stb = concat sb tb in
  let tag = utf8(str "Response") in
  let m = concat tag stb in
    m

let client (a:str) (b:str) (k:keyab) (s:str) =
  Assume (Request(a,b,s));
  let c = Net.connect p in
  let mac = hmacsha1 k (request s) in 
  Net.send c (concat (utf8 s) mac);
  let (pload',mac') = iconcat (Net.recv c) in
  let t = iutf8 pload' in 
  hmacsha1Verify k (response s t) mac';
  expect (RecvResponse(a,b,s,t))

let server(a:str) (b:str) (k:keyab) : unit =
  let c = Net.listen p in
  let (pload,mac) = iconcat (Net.recv c) in 
  let s = iutf8 pload in
  hmacsha1Verify k (request s) mac;
  expect (RecvRequest(a,b,s)); 
  let t = service s in
  Assume (Response(a,b,s,t));
  let mac' = hmacsha1 k (response s t) in 
  Net.send c (concat (utf8 t) mac')
(*--- AppEnd *)
// 09-10-31 typing request s takes forever, why?

let a = str "a"
let b = str "b"

#if pv
let k = mkKeyAB a b 
let client_ab: payload -> unit = fun s -> 
  let res = client a b k s  in
#if fs
  printf "Received Response %s\n" res;
#endif
  res
    
let server_ab: unit -> unit = fun _ -> server a b k
let compromise_a: unit -> key pub = fun _ -> Assume (Bad(a)); k
let compromise_b: unit -> key pub = fun _ -> Assume (Bad(b)); k
#else
(*--- AdversaryBegin *)
let setup (a:str) (b:str) =
  let k = mkKeyAB a b in
  (fun s -> client a b k s),
  (fun _ -> server a b k),
  (fun _ -> Assume (Bad(a)); (k:keypub)), 
  (fun _ -> Assume (Bad(b)); (k:keypub))
(*--- AdversaryEnd *)

let test:unit = 
  let client_ab, server_ab, _, _ = setup a b in
  Pi.fork (fun () -> server_ab (); ());
  client_ab (str "2 + 2?")
#endif
