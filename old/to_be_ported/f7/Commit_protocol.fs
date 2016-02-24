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
module Commit_protocol
open Global
open Data
open Pi
open Crypto
open Principals
open Sessions

let debug_impl = Global.debug "Impl"

let session = sha1 (utf8 (str"(c_start,c_cwqCommit),({c,w,q}Commit{c,w}),(w_start,w_cwqCommit))(w_cwqCommit,w_cwqCommit_Ack),({}Ack{}),(c_cwqCommit,c_cwqCommit_Ack))(c_cwqCommit_Ack,c_cwqAck_Reveal),({}Reveal{q}),(w_cwqCommit_Ack,w_cwqAck_Reveal))"))


type vars = {
  c: principal;
  w: principal;
  q: int}
type hashes = {
  hc:bytes;
  hw:bytes;
  hq:bytes}
type macs = {
  wCommitcwq: bytes;
  c_Acknowledge: bytes;
  wReveal: bytes}
type keys = {
  key_cw: bytes;
  key_wc: bytes}
type header = {
  ts: int;
  sid: bytes }
type store = 
  { vars: vars; hashes: hashes; macs: macs; keys: keys; header: header }

let empty_store_c role starting = 
  {vars = { c = role; w = ""; q = 0};
   hashes = { hc = utf8 (str ""); hw = utf8 (str ""); hq = utf8 (str "")};
   macs = { wCommitcwq = utf8 (str ""); c_Acknowledge = utf8 (str ""); wReveal = utf8 (str "")};
   keys = { key_cw = utf8 (str "");
            key_wc = utf8 (str "")};
   header = { sid = (if starting then let b:bytes = sha1 (concat (mkNonce()) session) in b else utf8 (str "")); ts = 0 } }

let empty_store_w role starting = 
  {vars = { c = ""; w = role; q = 0};
   hashes = { hc = utf8 (str ""); hw = utf8 (str ""); hq = utf8 (str "")};
   macs = { wCommitcwq = utf8 (str ""); c_Acknowledge = utf8 (str ""); wReveal = utf8 (str "")};
   keys = { key_cw = utf8 (str "");
            key_wc = utf8 (str "")};
   header = { sid = (if starting then let b:bytes = sha1 (concat (mkNonce()) session) in b else utf8 (str "")); ts = 0 } }

type preds = 
| Send_Commit of (principal * bytes * int* principal * principal * int)
| Send_Ack of (principal * bytes * int)
| Send_Reveal of (principal * bytes * int)
| Recv_Commit of (principal * bytes * int * principal * principal)
| Recv_Ack of (principal * bytes * int)
| Recv_Reveal of (principal * bytes * int * int)



(*******************************************)
(* Wired types, send and receive functions *)
(*******************************************)

(* Content of the MAC from role c at state c_cwqCommit with variables cwq*)
let content_c_cwqCommit_cwq ts store =
  let empty_str = str "" in
  let nil = utf8 empty_str in
  (* Marshalling hashes *)
  let hashes = concat store.hashes.hq nil in
  let hashes = concat store.hashes.hw hashes in
  let hashes = concat store.hashes.hc hashes in
  let nextstate = str "c_cwqCommit" in
  let nextstate_string = utf8 nextstate in
  let payload = concat nextstate_string hashes in
  let ts_string = string_of_int ts in
  let ts_str = str ts_string in
  let ts_mar = utf8 ts_str in
  let header = concat store.header.sid ts_mar in
  let content = concat header payload in
  content

(* Content of the MAC from role w at state w_cwqCommit_Ack with variables *)
let content_w_cwqCommit_Ack_ ts store =
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let hashes = nil in
  let nextstate = str "w_cwqCommit_Ack" in
  let nextstate_string = utf8 nextstate in
  let payload = concat nextstate_string hashes in
  let ts_string = string_of_int ts in
  let ts_str = str ts_string in
  let ts_mar = utf8 ts_str in
  let header = concat store.header.sid ts_mar in
  let content = concat header payload in
  content

(* Content of the MAC from role c at state c_cwqAck_Reveal with variables *)
let content_c_cwqAck_Reveal_ ts store =
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let hashes = nil in
  let nextstate = str "c_cwqAck_Reveal" in
  let nextstate_string = utf8 nextstate in
  let payload = concat nextstate_string hashes in
  let ts_string = string_of_int ts in
  let ts_str = str ts_string in
  let ts_mar = utf8 ts_str in
  let header = concat store.header.sid ts_mar in
  let content = concat header payload in
  content

(* Verification of a MAC from role c at state c_cwqCommit with variables cwq*)
let mac_verify_w_c_cwqCommit_cwq ts store k m =
  let content = content_c_cwqCommit_cwq ts store in
  Principals.hmacsha1Verify session (str store.vars.c) (str store.vars.w) k content m;
  content

(* Verification of a MAC from role w at state w_cwqCommit_Ack with variables *)
let mac_verify_c_w_cwqCommit_Ack_ ts store k m =
  let content = content_w_cwqCommit_Ack_ ts store in
  Principals.hmacsha1Verify session (str store.vars.w) (str store.vars.c) k content m;
  content

(* Verification of a MAC from role c at state c_cwqAck_Reveal with variables *)
let mac_verify_w_c_cwqAck_Reveal_ ts store k m =
  let content = content_c_cwqAck_Reveal_ ts store in
  Principals.hmacsha1Verify session (str store.vars.c) (str store.vars.w) k content m;
  content



type wired_w_start =
  | Wired_in_w_start_of_c_cwqCommit_cwq__ of ((principal * principal) * store)

type wired_c_cwqCommit =
  | Wired_in_c_cwqCommit_of_w_cwqCommit_Ack___ of ((unit) * store)

type wired_w_cwqCommit_Ack =
  | Wired_in_w_cwqCommit_Ack_of_c_cwqAck_Reveal___ of ((int) * store)


let receiveWired_w_start (store:store) : wired_w_start = 
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let msg = precv  store.vars.w in
  let header,content = iconcat (ibase64 msg) in
  let sid,ts_mar = iconcat header in
  let ts_str = iutf8 ts_mar in
  let ts_string = istr ts_str in
  let ts = int_of_string ts_string in
  let _ = check_cache store.vars.w "w" sid in
  let oldts = store.header.ts in
  let store = { store with 
      header = { sid = sid; ts = ts;}} in
  let tag,payload = iconcat content in
  match istr (iutf8 tag) with
  | "c_cwqCommit_cwq__" ->
  let variables,security = iconcat payload in
  let keys,protocol = iconcat security in
  let hashes,macs = iconcat protocol in
  (* Unmarshalling principal variables *)
  let mar_w,variables = iconcat variables in
  let string_w = iutf8 mar_w in
  let w = istr string_w in
  let hw = sha1 mar_w in
  let mar_c,variables = iconcat variables in
  let string_c = iutf8 mar_c in
  let c = istr string_c in
  let hc = sha1 mar_c in
  let store = { store with 
      vars = {store.vars with c = c; w = w;};} in
  (* Unmarshalling keys *)
  let key_cw,_ = iconcat keys in
  let _ = reg_keys session (str store.vars.c) (str store.vars.w) key_cw in
  let store = { store with 
      hashes = {store.hashes with hc = hc; hw = hw;};
      keys = {store.keys with key_cw = key_cw;};} in
  (* Unmarshalling hashes *)
  let hq,_ = iconcat hashes in
  (* Unmarshalling MACs *)
  let wCommitcwq,_ = iconcat macs in
  let store = { store with 
      hashes = {store.hashes with hq = hq;};
      macs = {store.macs with wCommitcwq = wCommitcwq;};} in
  (* Verification of a MAC from state c_cwqCommit with variables cwq*)
  let macheader,maccontent = iconcat store.macs.wCommitcwq in
  let macsid,ts_mar = iconcat macheader in
  let ts_str = iutf8 ts_mar in
  let ts_string = istr ts_str in
  let ts = int_of_string ts_string in
  let _ = Global.test_inf oldts ts "MAC verification" in
  let oldts = ts in
  let _ = Global.test_eq macsid sid "MAC verification" in
  let mackeycw = getMACKey session (str store.vars.c) (str store.vars.w) in
  let content = mac_verify_w_c_cwqCommit_cwq ts store mackeycw maccontent in
  let _ = Global.test_eq oldts store.header.ts "Time-stamp verification" in
  (* Verification Ended *)
    let wired = Wired_in_w_start_of_c_cwqCommit_cwq__((c,w),store) in
    wired

let receiveWired_c_cwqCommit (store:store) : wired_c_cwqCommit = 
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let msg = precv  store.vars.c in
  let header,content = iconcat (ibase64 msg) in
  let sid,ts_mar = iconcat header in
  let ts_str = iutf8 ts_mar in
  let ts_string = istr ts_str in
  let ts = int_of_string ts_string in
  let oldts = store.header.ts in
  let _ = Global.test_inf oldts ts "Replay attack!" in
  let _ = Global.test_eq store.header.sid sid "Session confusion attack!" in
  let store = { store with 
      header = {store.header with ts = ts;}} in
  let tag,payload = iconcat content in
  match istr (iutf8 tag) with
  | "w_cwqCommit_Ack___" ->
  let variables,security = iconcat payload in
  let keys,protocol = iconcat security in
  let hashes,macs = iconcat protocol in
  (* Unmarshalling keys *)
  let key_wc,_ = iconcat keys in
  let _ = reg_keys session (str store.vars.w) (str store.vars.c) key_wc in
  let store = { store with 
      keys = {store.keys with key_wc = key_wc;};} in
  (* Unmarshalling MACs *)
  let c_Acknowledge,_ = iconcat macs in
  let store = { store with 
      macs = {store.macs with c_Acknowledge = c_Acknowledge;};} in
  (* Verification of a MAC from state w_cwqCommit_Ack with variables *)
  let macheader,maccontent = iconcat store.macs.c_Acknowledge in
  let macsid,ts_mar = iconcat macheader in
  let ts_str = iutf8 ts_mar in
  let ts_string = istr ts_str in
  let ts = int_of_string ts_string in
  let _ = Global.test_inf oldts ts "MAC verification" in
  let oldts = ts in
  let _ = Global.test_eq macsid store.header.sid "MAC verification" in
  let mackeywc = getMACKey session (str store.vars.w) (str store.vars.c) in
  let content = mac_verify_c_w_cwqCommit_Ack_ ts store mackeywc maccontent in
  let _ = Global.test_eq oldts store.header.ts "Time-stamp verification" in
  (* Verification Ended *)
    let wired = Wired_in_c_cwqCommit_of_w_cwqCommit_Ack___((),store) in
    wired

let receiveWired_w_cwqCommit_Ack (store:store) : wired_w_cwqCommit_Ack = 
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let msg = precv  store.vars.w in
  let header,content = iconcat (ibase64 msg) in
  let sid,ts_mar = iconcat header in
  let ts_str = iutf8 ts_mar in
  let ts_string = istr ts_str in
  let ts = int_of_string ts_string in
  let oldts = store.header.ts in
  let _ = Global.test_inf oldts ts "Replay attack!" in
  let _ = Global.test_eq store.header.sid sid "Session confusion attack!" in
  let store = { store with 
      header = {store.header with ts = ts;}} in
  let tag,payload = iconcat content in
  match istr (iutf8 tag) with
  | "c_cwqAck_Reveal___" ->
  let variables,security = iconcat payload in
  let keys,protocol = iconcat security in
  let hashes,macs = iconcat protocol in
  (* Decrypting variables *)
  let keycw = getEncryptionKey session (str store.vars.c) (str store.vars.w) in
  let variables = unpickle (Principals.aes_decrypt session (str store.vars.c) (str store.vars.w) keycw variables) in
  (* Unmarshalling variables *)
  let mar_q,variables = iconcat variables in
  let string_q = iutf8 mar_q in
  let marred_q = istr string_q in
  let q = int_of_string marred_q in
  let hq = sha1 mar_q in
  let marred_q = string_of_int q in
  let string_q = str marred_q in
  let mar_q = utf8 string_q in
    let _ = sha1_verify mar_q store.hashes.hq in
  let store = { store with 
      vars = {store.vars with q = q;};} in
  (* Unmarshalling MACs *)
  let wReveal,_ = iconcat macs in
  let store = { store with 
      macs = {store.macs with wReveal = wReveal;};} in
  (* Verification of a MAC from state c_cwqAck_Reveal with variables *)
  let macheader,maccontent = iconcat store.macs.wReveal in
  let macsid,ts_mar = iconcat macheader in
  let ts_str = iutf8 ts_mar in
  let ts_string = istr ts_str in
  let ts = int_of_string ts_string in
  let _ = Global.test_inf oldts ts "MAC verification" in
  let oldts = ts in
  let _ = Global.test_eq macsid store.header.sid "MAC verification" in
  let mackeycw = getMACKey session (str store.vars.c) (str store.vars.w) in
  let content = mac_verify_w_c_cwqAck_Reveal_ ts store mackeycw maccontent in
  let _ = Global.test_eq oldts store.header.ts "Time-stamp verification" in
  (* Verification Ended *)
    let wired = Wired_in_w_cwqCommit_Ack_of_c_cwqAck_Reveal___((q),store) in
    wired
  | _ -> failwith "Critical Error"


(* Sending message from c to w *)
(* Message has to be MACed for w *)
let sendWired_Commit_c_start c w q store =
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let string_c = str c in
  let mar_c = utf8 string_c in
  let hc = sha1 mar_c in
  let string_w = str w in
  let mar_w = utf8 string_w in
  let hw = sha1 mar_w in
  let marred_q = string_of_int q in
  let string_q = str marred_q in
  let mar_q = utf8 string_q in
  let hq = sha1 mar_q in
  let ts = store.header.ts + 1 in
  let store = { store with 
      vars = {store.vars with c = c; w = w; q = q;};
      hashes = {store.hashes with hc = hc; hw = hw; hq = hq;};
      header = {store.header with ts = ts;}} in
  let ts_string = string_of_int store.header.ts in
  let ts_str = str ts_string in
  let ts_mar = utf8 ts_str in
  let header = concat store.header.sid ts_mar in
  let keys = nil in
  let key_cw = gen_keys session (str store.vars.c) (str store.vars.w) in
  let keys = concat key_cw keys in
  (* Generation of a MAC from state c_start to role w *)
  let content = content_c_cwqCommit_cwq store.header.ts store in
  let mackeycw = getMACKey session (str store.vars.c) (str store.vars.w) in
  let macmsg = Principals.hmacsha1 session (str store.vars.c) (str store.vars.w) mackeycw (pickle content) in
  let wCommitcwq = concat header macmsg in
  let store = { store with 
      macs = {store.macs with wCommitcwq = wCommitcwq;};} in
  let macs = nil in
  let macs = concat store.macs.wCommitcwq macs in
  (* Marshalling hashes *)
  let hashes = concat store.hashes.hq nil in
  (* Marshalling variables *)
  let variables = nil in
  let keycw = getEncryptionKey session (str store.vars.c) (str store.vars.w) in
  let variables = Principals.aes_encrypt session (str store.vars.c) (str store.vars.w) keycw (pickle variables) in
  let string_c = str store.vars.c in
  let mar_c = utf8 string_c in
  let variables = concat mar_c variables in
  let string_w = str store.vars.w in
  let mar_w = utf8 string_w in
  let variables = concat mar_w variables in
  let protocol = concat hashes macs in
  let security = concat keys protocol in
  let payload = concat variables security in
  let visib = str "c_cwqCommit_cwq__" in
  let visib_string = utf8 visib in
  let content = concat visib_string payload in
  let msg = base64 (concat header content) in
  let _ = psend  store.vars.w msg in 
  store 

(* Sending message from w to c *)
(* Message has to be MACed for c *)
let sendWired_Ack_w_cwqCommit store =
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let ts = store.header.ts + 1 in
  let store = { store with 
      header = {store.header with ts = ts;}} in
  let ts_string = string_of_int store.header.ts in
  let ts_str = str ts_string in
  let ts_mar = utf8 ts_str in
  let header = concat store.header.sid ts_mar in
  let keys = nil in
  let key_wc = gen_keys session (str store.vars.w) (str store.vars.c) in
  let keys = concat key_wc keys in
  (* Generation of a MAC from state w_cwqCommit to role c *)
  let content = content_w_cwqCommit_Ack_ store.header.ts store in
  let mackeywc = getMACKey session (str store.vars.w) (str store.vars.c) in
  let macmsg = Principals.hmacsha1 session (str store.vars.w) (str store.vars.c) mackeywc (pickle content) in
  let c_Acknowledge = concat header macmsg in
  let store = { store with 
      macs = {store.macs with c_Acknowledge = c_Acknowledge;};} in
  let macs = nil in
  let macs = concat store.macs.c_Acknowledge macs in
  let hashes = nil in
  let variables = nil in
  let protocol = concat hashes macs in
  let security = concat keys protocol in
  let payload = concat variables security in
  let visib = str "w_cwqCommit_Ack___" in
  let visib_string = utf8 visib in
  let content = concat visib_string payload in
  let msg = base64 (concat header content) in
  let _ = psend  store.vars.c msg in 
  store 

(* Sending message from c to w *)
(* Message has to be MACed for w *)
let sendWired_Reveal_c_cwqCommit_Ack store =
  let empty_str = str "" in
  let nil = utf8 empty_str in
  let ts = store.header.ts + 1 in
  let store = { store with 
      header = {store.header with ts = ts;}} in
  let ts_string = string_of_int store.header.ts in
  let ts_str = str ts_string in
  let ts_mar = utf8 ts_str in
  let header = concat store.header.sid ts_mar in
  let keys = nil in
  (* Generation of a MAC from state c_cwqCommit_Ack to role w *)
  let content = content_c_cwqAck_Reveal_ store.header.ts store in
  let mackeycw = getMACKey session (str store.vars.c) (str store.vars.w) in
  let macmsg = Principals.hmacsha1 session (str store.vars.c) (str store.vars.w) mackeycw (pickle content) in
  let wReveal = concat header macmsg in
  let store = { store with 
      macs = {store.macs with wReveal = wReveal;};} in
  let macs = nil in
  let macs = concat store.macs.wReveal macs in
  let hashes = nil in
  (* Marshalling variables *)
  let variables = nil in
  let marred_q = string_of_int store.vars.q in
  let string_q = str marred_q in
  let mar_q = utf8 string_q in
  let variables = concat mar_q variables in
  let keycw = getEncryptionKey session (str store.vars.c) (str store.vars.w) in
  let variables = Principals.aes_encrypt session (str store.vars.c) (str store.vars.w) keycw (pickle variables) in
  let protocol = concat hashes macs in
  let security = concat keys protocol in
  let payload = concat variables security in
  let visib = str "c_cwqAck_Reveal___" in
  let visib_string = utf8 visib in
  let content = concat visib_string payload in
  let msg = base64 (concat header content) in
  let _ = psend  store.vars.w msg in 
  store 


