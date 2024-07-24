(*
   Copyright 2023 Microsoft Research

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

module PulseSyntaxExtension.Desugar

open FStar.Compiler.Effect
module Sugar = PulseSyntaxExtension.Sugar
module SW = PulseSyntaxExtension.SyntaxWrapper
module D = FStar.Syntax.DsEnv
module R = FStar.Compiler.Range

// An error can be "None", which means all relevant
// errors were already logged via the error API.
type error = option (string & R.range)

let err a = nat -> either a error & nat

let env_t : Type0 = PulseSyntaxExtension.Env.env_t

val desugar_decl (env:env_t)
                 (p:Sugar.decl)
  : err SW.decl

let name = list string

val reinitialize_env (env:D.env)
                     (curmode:FStar.Ident.lident)
                     (open_namespaces: list name)
                     (module_abbrevs: list (string & name))
: env_t

val mk_env (env:D.env)
: env_t