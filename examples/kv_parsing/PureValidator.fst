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
module PureValidator

open KeyValue
open Parsing
open IntegerParsing
open PureParser

open FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32

(*! Pure validation *)

(** Note that this was an experiment and is largely superseded by the stateful
versions (there isn't a compelling use case for spec-level validation; might as
well use the pure parser as the spec) *)

let validator = parser unit
// let parse_validator #t (p:parser t) = b:bytes -> (ok:bool{ok <==> Some? (p b)} * n:nat{n <= length b})

let seq (#t:Type) (#t':Type) (p:parser t) (p': parser t') : parser t' =
  fun b -> match p b with
        | Some (_, l) -> begin
                match p' (slice b l (length b)) with
                | Some (v, l') -> Some (v, l + l')
                | None -> None
          end
        | None -> None

unfold let invalid (#b:bytes): option (unit * n:nat{n <= length b}) = None
unfold let valid (#b:bytes) (n:nat{n <= length b}) : option (unit * n:nat{n <= length b}) = Some ((), n)

let skip_bytes (n:nat) : validator =
  fun b -> if length b < n then invalid
        else valid n

// this is analogous to the stateful version, validation_check_parse, but pure
// validators are a special case of parsers and don't return quite the same
// thing
let parser_validation_checks_parse #t (b: bytes)
  (v: option (unit * n:nat{n <= length b}))
  (p: option (t * n:nat{n <= length b})) : Type0 =
  Some? v ==> (Some? p /\ snd (Some?.v v) == snd (Some?.v p))

let validator_checks_on (v:validator) #t (p: parser t) (b:bytes{length b < pow2 32}) = parser_validation_checks_parse b (v b) (p b)

// NOTE: this proof about the whole validator works better than a function with
// built-in correctness proof (despite the universal quantifier)
(** a correctness condition for a validator, stating that it correctly reports
    when a parser will succeed (the implication only needs to be validated ==>
    will parse, but this has worked so far) *)
let validator_checks (v: validator) #t (p: parser t) : Type0 = forall b. validator_checks_on v p b

// this definitions assists type inference by forcing t'=unit; it also makes the
// code read a bit better
let then_validate (#t:Type) (p:parser t) (v:t -> validator) : validator =
    and_then p v

val validate_u16_array: v:validator{validator_checks v parse_u16_array}
let validate_u16_array =
  parse_u16 `then_validate`
  (fun array_len -> skip_bytes (U16.v array_len))

val validate_u32_array: v:validator{validator_checks v parse_u32_array}
let validate_u32_array =
  parse_u32 `then_validate`
  (fun array_len -> skip_bytes (U32.v array_len))

// TODO: this goes through in interactive mode but not in batch mode
let validate_entry: v:validator{validator_checks v parse_entry} =
  admit();
  validate_u16_array `seq`
  validate_u32_array

let validate_accept : validator =
  fun b -> valid 0
let validate_reject : validator =
  fun b -> invalid

val validate_many':
  n:nat ->
  v:validator ->
  v':validator
let rec validate_many' n v =
  match n with
  | 0 -> validate_accept
  | _ -> v `seq` validate_many' (n-1) v

#reset-options "--max_fuel 0 --z3rlimit 20"

val intro_validator_checks (#t:Type) (v: validator) (p:parser t)
  (pf : (b:bytes{length b < pow2 32} -> Lemma (validator_checks_on v p b))) :
  Lemma (validator_checks v p)
let intro_validator_checks #t v p pf =
  FStar.Classical.forall_intro
    #(b:bytes{length b < pow2 32})
    #(fun (b:bytes{length b < pow2 32}) -> validator_checks_on v p b)
    pf

// TODO: these proofs don't work reliably; pure validators are unused so it's
// not super important, but it would be nice to figure out what's going in

val validate_seq (#t:Type) (#t':Type)
  (p: parser t) (p': parser t')
  (v: validator{validator_checks v p})
  (v': validator{validator_checks v' p'}) :
  Lemma (validator_checks (v `seq` v') (p `seq` p'))
let validate_seq #t #t' p p' v v' =
  admit()
  // intro_validator_checks (v `seq` v') (p `seq` p') (fun b -> ())

val validate_parse_ret (#t:Type) (#t':Type) (f: t -> t')
  (p: parser t)
  (v: validator{validator_checks v p}) :
  Lemma (validator_checks v (p `and_then` (fun x -> parse_ret (f x))))
let validate_parse_ret #t #t' f p v =
  admit()
  // intro_validator_checks v (p `and_then` (fun x -> parse_ret (f x))) (fun b -> ())

val validate_liftA2 (#t:Type) (#t':Type) (#t'':Type)
  (p: parser t) (p': parser t') (f: t -> t' -> t'')
  (v: validator{validator_checks v p})
  (v': validator{validator_checks v' p'}) :
  Lemma (validator_checks (v `seq` v') (p `and_then` (fun (x:t) -> p' `and_then` (fun (y:t') -> parse_ret (f x y)))))
let validate_liftA2 #t #t' #t'' p p' f v v' =
  admit()
  //assert (forall x. validator_checks v' (p' `and_then` (fun y -> parse_ret (f x y))));
  //assert (forall (b: bytes{length b < pow2 32}). match v b with
  //             | Some (_, l) -> Some? (p b) /\ snd (Some?.v (p b)) == l
  //             | None -> True);
  //()

#reset-options "--z3rlimit 30"

val validate_many'_ok (n:nat) (#t:Type) (p: parser t) (v:validator{validator_checks v p}) :
  Lemma (validator_checks (validate_many' n v) (parse_many p n))
let rec validate_many'_ok n #t p v =
  match n with
  | 0 -> ()
  | _ -> let n':nat = n-1 in
        validate_many'_ok n' p v;
        let p' = parse_many p n' in
        let v': v:validator{validator_checks v p'} = validate_many' n' v in
        validate_liftA2 p p' (fun v l -> v::l) v v';
        ()

#reset-options

val validate_many:
  #t:Type -> p:parser t ->
  n:nat ->
  v:validator{validator_checks v p} ->
  v':validator{validator_checks v' (parse_many p n)}
let validate_many #t p n v = validate_many'_ok n p v; validate_many' n v

let validate_done : v:validator{validator_checks v parsing_done} =
  fun b -> if length b = 0 then valid 0
        else invalid

val validate: v:validator{validator_checks v parse_abstract_store}
let validate =
  // NOTE: this verification didn't go through
  admit();
  parse_u32 `then_validate`
  (fun num_entries -> validate_many parse_entry (U32.v num_entries) validate_entry `seq`
                   validate_done)
