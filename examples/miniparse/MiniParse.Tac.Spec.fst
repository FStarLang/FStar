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
module MiniParse.Tac.Spec
include MiniParse.Tac.Base
include MiniParse.Spec.Combinators
include MiniParse.Spec.Int
include MiniParse.Spec.List
include MiniParse.Spec.TEnum

module T = FStar.Tactics
module L = FStar.List.Tot

noeq
type package (t: Type0) =
  | Package :
    (p: parser_spec t) ->
    (s: serializer_spec p) ->
    package t

let mk_package (#t: Type0) (#p: parser_spec t) (s: serializer_spec p) : Tot (package t) =
  Package p s

let package_parser (#t: Type0) (p: package t) : Tot (parser_spec t) =
  Package?.p p

let package_serializer (#t: Type0) (p: package t) : Tot (serializer_spec (package_parser p)) =
  Package?.s p

let rec gen_package' (p: T.term) : T.Tac (T.term * T.term) =
  let (hd, tl) = app_head_tail p in
  if hd `T.term_eq` (`(FStar.UInt8.t))
  then begin
    ((`(parse_u8)), (`(serialize_u8)))
  end else
  if hd `T.term_eq` (`(tuple2))
  then match tl with
  | [(t1, _); (t2, _)] ->
    let (p1, s1) = gen_package' t1 in
    let (p2, s2) = gen_package' t2 in
    let p = T.mk_app (`(nondep_then)) [
      (t1, T.Q_Implicit);
      (p1, T.Q_Explicit);
      (t2, T.Q_Implicit);
      (p2, T.Q_Explicit);
    ]
    in
    let s = T.mk_app (`(serialize_nondep_then)) [
      (t1, T.Q_Implicit);
      (p1, T.Q_Implicit);
      (s1, T.Q_Explicit);
      (t2, T.Q_Implicit);
      (p2, T.Q_Implicit);
      (s2, T.Q_Explicit);
    ]
    in
    (p, s)
  | _ -> tfail "Not enough arguments to nondep_then"
  else
  if hd `T.term_eq` (`(nlist))
  then match tl with
  | [(n, _); (t, _)] ->
    let (p, s) = gen_package' t in
    let p' = T.mk_app (`(parse_nlist)) [(n, T.Q_Explicit); (t, T.Q_Implicit); (p, T.Q_Explicit)] in
    let s' = T.mk_app (`(serialize_nlist)) [
      (n, T.Q_Explicit);
      (t, T.Q_Implicit);
      (p, T.Q_Implicit);
      (s, T.Q_Explicit);
    ]
    in
    (p', s')
  | _ -> tfail "Not enough arguments to nlist"
  else match T.trytac (fun () -> gen_enum_specs p) with
  | Some res -> res
  | _ ->
    if L.length tl = 0
    then begin
      gen_package' (unfold_term p)
    end else
      tfail "Unknown parser combinator"

let gen_package (pol: T.guard_policy) (t: T.term) : T.Tac unit =
  let (p, s) = gen_package' t in
  let res = T.mk_app (`(mk_package)) [
    (t, T.Q_Implicit);
    (p, T.Q_Implicit);
    (s, T.Q_Explicit);
  ]
  in
  T.exact_guard res;
  according_to pol (fun () -> tconclude_with [
    synth_inverse_forall_bounded_u16_solve;
    synth_inverse_forall_tenum_solve;  
  ])

let gen_specs = gen_package

type u8 = FStar.UInt8.t

type t = (u8 * (nlist 79 u8 * u8))

let p : package t = T.synth_by_tactic (fun () -> gen_package T.Goal (`t))
