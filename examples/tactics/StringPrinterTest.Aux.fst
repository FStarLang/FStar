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
module StringPrinterTest.Aux
include StringPrinter.RecC

module Ca = FStar.Int.Cast
module U32 = FStar.UInt32
module T = FStar.Tactics
module HST = FStar.HyperStack.ST
module B = FStar.Buffer

#reset-options "--z3rlimit 32 --using_facts_from '* -FStar.Tactics -FStar.Reflection'"

let rec example (x: U32.t) : Tot (m unit) (decreases (U32.v x)) =
  _ <-- print_char (Ca.uint32_to_uint8 x) ;
  if U32.lt x 256ul
  then ret ()
  else example (U32.div x 256ul)

let example_do_while : (x: U32.t) -> Tot (y: m unit { y () == example x () } ) =
  T.synth_by_tactic (fun () -> mk_do_while example )

#push-options "--admit_smt_queries true"
inline_for_extraction
let example_sz (x: U32.t) : Tot (m_sz (example x)) =
  coerce_sz
    _
    (example_do_while x)
    (T.synth_by_tactic u#1 (fun () -> mk_sz (example_do_while x)))
    (example x)
    ()
#pop-options

#push-options "--admit_smt_queries true"
inline_for_extraction
let example_st (x: U32.t) : Tot (m_st (example x)) =
  coerce_st
    _
    (example_do_while x)
    (T.synth_by_tactic (fun () -> mk_st (example_do_while x)))
    (example x)
    ()
#pop-options

module U8 = FStar.UInt8
module HS = FStar.HyperStack

#push-options "--admit_smt_queries true"
inline_for_extraction
let example_test
  (x: U32.t)
: HST.ST (option (B.buffer U8.t))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    match res with
    | None -> h' == h
    | Some b -> buffer_create_mm_post HS.root h h' b
  ))
= let res = phi
    (example x)
    (example_sz x)
    (example_st x)
    ()
  in
  match res with
  | None -> None
  | Some (_, b) -> Some b
#pop-options

type cipher_suite =
  | TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  | TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  | TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
  | TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
  | TLS_DH_anon_WITH_RC4_128_MD5
  | TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
  | TLS_DH_anon_WITH_AES_128_CBC_SHA
  | TLS_DH_anon_WITH_AES_256_CBC_SHA
  | TLS_DH_anon_WITH_AES_128_CBC_SHA256
  | TLS_DH_anon_WITH_AES_256_CBC_SHA256

let print_cipher_suite_spec (c: cipher_suite) : Tot (m unit) =
  if c = TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256
  then (_ <-- print_char 0xc0z; print_char 0x2fz)
  else if c = TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256
  then (_ <-- print_char 0xc0z; print_char 0x2bz)
  else if c = TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384
  then (_ <-- print_char 0xc0z; print_char 0x2cz)
  else if c = TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384
  then (_ <-- print_char 0xc0z; print_char 0x30z)
  else begin
    _ <-- print_char 0x00z ;
    if c = TLS_DH_anon_WITH_RC4_128_MD5
    then print_char 0x18z
    else if c = TLS_DH_anon_WITH_3DES_EDE_CBC_SHA
    then print_char 0x1Bz
    else if c = TLS_DH_anon_WITH_AES_128_CBC_SHA
    then print_char 0x34z
    else if c = TLS_DH_anon_WITH_AES_256_CBC_SHA
    then print_char 0x3Az
    else if c = TLS_DH_anon_WITH_AES_128_CBC_SHA256
    then print_char 0x6Cz
    else (* if c = TLS_DH_anon_WITH_AES_256_CBC_SHA256 *)
         print_char 0x6Dz
  end

module L = FStar.List.Tot

inline_for_extraction
let is_nil (#t: Type) (l: list t) : Tot bool =
match l with
| [] -> true
| _ -> false

let rec print_list_cipher_suite_spec (l: list cipher_suite) : Tot (m unit) =
  if is_nil l
  then ret ()
  else begin
    _ <-- print_cipher_suite_spec (L.hd l) ;
    print_list_cipher_suite_spec (L.tl l)
  end

let print_list_cipher_suite_spec_do_while :
  (l: list cipher_suite) -> Tot (y: m unit { y () == print_list_cipher_suite_spec l () } )
= T.synth_by_tactic (fun () -> mk_do_while print_list_cipher_suite_spec )

#push-options "--admit_smt_queries true"
inline_for_extraction
let print_list_cipher_suite_sz (l: list cipher_suite) : Tot (m_sz (print_list_cipher_suite_spec l)) =
  coerce_sz
    _
    (print_list_cipher_suite_spec_do_while l)
    (T.synth_by_tactic u#1 (fun () -> mk_sz (print_list_cipher_suite_spec_do_while l)))
    (print_list_cipher_suite_spec l)
    ()
#pop-options

#push-options "--admit_smt_queries true"
inline_for_extraction
let print_list_cipher_suite_st (l: list cipher_suite) : Tot (m_st (print_list_cipher_suite_spec l)) =
  coerce_st
    _
    (print_list_cipher_suite_spec_do_while l)
    (T.synth_by_tactic (fun () -> mk_st (print_list_cipher_suite_spec_do_while l)))
    (print_list_cipher_suite_spec l)
    ()
#pop-options

inline_for_extraction
let print_list_cipher_suite
  (x: list cipher_suite)
: HST.ST (option (B.buffer U8.t))
  (requires (fun _ -> True))
  (ensures (fun h res h' ->
    match res with
    | None -> h' == h
    | Some b -> buffer_create_mm_post HS.root h h' b
  ))
= let res = phi
    (print_list_cipher_suite_spec x)
    (print_list_cipher_suite_sz x)
    (print_list_cipher_suite_st x)
    ()
  in
  match res with
  | None -> None
  | Some (_, b) -> Some b
