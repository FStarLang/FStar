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
(* our encryption module is parameterized by a "native" RSA-OAEP
   implementation, available at least for F#/.NET *)

(* I am trying to capture functional correctness, which we did not
   have with F7; otherwise most refinements can be ignored.

   I think this would require coding "events" as membership of
   increasing mutable lists, possibly too advanced for a tutorial *)

module CCA2.CCA2  (* intuitively, parameterized by both Plain and RSA *)

open FStar.List.Tot
open CCA2

type cipher = RSA.cipher
noeq type entry =
(* indexing entry with ideal and pk triggers some bugs; meanwhile, using a simple type *)
  | Entry : ideal':bool
         -> pk':RSA.pkey
         -> c:RSA.cipher
         -> p:Plain.t{forall sk. (RSA.generated (pk',sk) && not ideal')
                       ==> RSA.dec sk c = Some (Plain.repr p)} (* may consider making plain/repr identities to simplify this *)
         -> entry

(* TODO: give type
val forget: t:Type
            -> p:(t -> Type)
            -> option (x:t{p x})
            -> Tot (option t)*)
let forget = function
  | Some x -> Some x
  | None -> None

let cca2 (ideal:bool) : (RSA.pkey * (Plain.t -> RSA.cipher) * (RSA.cipher -> option (Plain.t))) =
  (* the next step will be to deal with multiple keys. *)
  let pk, sk = RSA.gen ()  in
  let log : ref (list entry) = ST.alloc [] in

  let enc : Plain.t -> RSA.cipher = fun t ->
    let t' = if ideal then RSA.dummy else Plain.repr t in
    let c = RSA.enc pk t' in
    log := Entry ideal pk c t::!log;
    c  in

  let dec : RSA.cipher -> option (Plain.t) = fun c ->
    match ideal, List.Tot.find (function Entry _ _ c' _ -> c=c') !log with
      | true,  Some t  -> Some(Entry.p t)
      | _,  _       -> None
      | false, _ -> 
        (match RSA.dec sk c with
        | Some(t') -> forget (* #Plain.t *) #_ (Plain.coerce t')
        | None     -> None) in

  pk, enc, dec
