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

module ParametricStateIssue

open FStar.Integers
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer

#set-options "--admit_smt_queries true"  //we only care about extraction in this module


/// This module illustrates the issue of extracting a state effect that is parametric in the type of state
///
/// The underlying issue is as follows:
///
/// The code in layered effects is written in primitive F* let syntax:
///
/// let x = e1 in e2
///
/// which is essentially M.bind <some arguments> e1 (fun x -> e2)
///
/// The <some arguments> here refers to the "index" arguments of M.bind
///
/// When F* typechecks this code, it infers the instantiations of the index arguments
///
/// HOWEVER, these index arguments are not stored anywhere in the AST, instead
///   we only carry over the resulting computation type
///
/// As a result, when we reach the extraction, we have no choice but to pass `()` for these arguments
///
/// This becomes a problem if some index is crucial to determine the type of the terms,
///   parametic state is one such example
///
/// Specifically, if we have `let lift ... (state:Type0) ... : mrepr a state = e`
///
/// And we pass in `()` for state, it messes up the `mrepr a ()` annotation, and the term `e` gets
///   ascribed with `mrepr a unit` which down the line results in some `Obj.magic`s in the extracted
///   code
///
/// The example below illustrates a scenario, the double layering is not really necessary
///
/// Try with:
///
/// fstar.exe --codegen OCaml --extract '-* ParametricStateIssue' ParametricStateIssue.fst
///
/// ALSO: comp_no_args in Extraction.ML.Term.fs should not be done whenever this is fixed


inline_for_extraction
type repr (a:Type) (_:unit) =
  unit ->
  St (option a)


inline_for_extraction
let return (a:Type) (x:a)
: repr a ()
= fun _ -> Some x

inline_for_extraction
let bind (a:Type) (b:Type)
  (f:repr a ()) (g:(x:a -> repr b ()))
: repr b ()
= fun _ ->
  let r = f () in
  match r with
  | None -> None
  | Some x -> (g x) ()

inline_for_extraction
let subcomp (a:Type)
  (f:repr a ())
: Pure (repr a ())
  (requires True)
  (ensures fun _ -> True)
= f

inline_for_extraction
let if_then_else (a:Type)
  (f:repr a ()) (g:repr a ())
  (p:Type0)
: Type
= repr a ()


/// The effect definition

reifiable reflectable
layered_effect {
  EXN : a:Type -> unit -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


inline_for_extraction
let lift_div_exn (a:Type) (wp:pure_wp a) (f:unit -> DIV a wp)
: repr a ()
= fun _ -> Some (f ())


sub_effect DIV ~> EXN = lift_div_exn

assume val t1 : Type0

inline_for_extraction
type parser_t (a:Type0) =
  b:B.buffer uint_8 ->
  m_begin:uint_32   ->
  St (option (a & uint_32))

assume val t1_parser : parser_t t1

noeq
type rcv_state = {
  b  : B.buffer uint_8;
  id : i:uint_32{i <= B.len b}
}



inline_for_extraction
type mrepr (a:Type) (state:Type0) =
  state -> EXN (a & state) ()

inline_for_extraction noextract
let streturn (a:Type) (state:Type0) (x:a)
: mrepr a state
= fun st -> (x, st)


inline_for_extraction noextract
let stbind (a:Type) (b:Type)
  (state:Type0)
  (f:mrepr a state) (g:(a -> mrepr b state))
: mrepr b state
= fun st ->
  let (x, st) = f st in
  g x st

inline_for_extraction noextract
let stsubcomp (a:Type)
  (state:Type0)
  (f:mrepr a state)
: Pure (mrepr a state)
  (requires True)
  (ensures fun _ -> True)
= f

inline_for_extraction noextract
let stif_then_else (a:Type)
  (state:Type0)
  (f:mrepr a state) (g:mrepr a state)
  (p:Type0)
: Type
= mrepr a state

reifiable reflectable
layered_effect {
  STEXN : a:Type -> state:Type0 -> Effect
  with
  repr = mrepr;
  return = streturn;
  bind = stbind;
  subcomp = stsubcomp;
  if_then_else = stif_then_else
}


inline_for_extraction noextract
let lift_div_stexn (a:Type) (wp:pure_wp a) (state:Type0) (f:unit -> DIV a wp)
: mrepr a state
= fun st -> (f (), st)

sub_effect DIV ~> STEXN = lift_div_stexn

inline_for_extraction noextract
let parse_common_exn (#a:Type0)
  (parser:parser_t a)
  (_:unit)
  (st:rcv_state)
: EXN (a & rcv_state) ()
= EXN?.reflect (fun _ ->
    let r = parser st.b st.id in
    match r with
    | None -> None
    | Some (x, m_end) -> Some (x, st))

inline_for_extraction noextract
let parse_common (#a:Type0)
  (parser:parser_t a)
  (_:unit)
: STEXN a rcv_state
= STEXN?.reflect (parse_common_exn #a parser ())

inline_for_extraction noextract
let parse_t1 = parse_common #t1 t1_parser

//#set-options "--debug Test --debug_level Extraction --ugly --print_implicits --print_effect_args"
inline_for_extraction noextract
let parse_flt_aux ()
: STEXN t1 rcv_state
= let x = parse_t1 () in
  x
