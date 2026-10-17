(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Reflection.Typing.Builtins

open FStar.Stubs.Syntax.Syntax
open FStar.Reflection.V2
open FStar.Range

let dummy_range = range_0

let var_as_namedv (v:var) : namedv =
  pack_namedv {
    uniq = v;
    sort = FStar.Sealed.seal (pack_ln Tv_Unknown);
    ppname = as_ppname "_";
  }

let open_with t v = subst_term [DT 0 v] t

let open_term t v = subst_term [DB 0 (var_as_namedv v)] t

let close_term t v = subst_term [NM (var_as_namedv v) 0] t

let rename t x y = subst_term [NT (var_as_namedv x) (pack_ln (Tv_Var (var_as_namedv y)))] t
