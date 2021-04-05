(*
   Copyright 2020 Microsoft Research

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
#light "off"
(* -------------------------------------------------------------------- *)
module FStar.Extraction.ML.RemoveUnusedParameters
open FStar.Ident
open FStar.Extraction.ML.Syntax

type env_t
val initial_env : env_t
val set_current_module (e:env_t) (n:mlpath) : env_t

type tydef = mlsymbol * metadata * either<mltyscheme, int>
val elim_tydefs (env:env_t) (tds:list<tydef>) : env_t * list<tydef>
val elim_mllib (env:env_t) (m:mllib) : env_t * mllib
