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

module PulseSyntaxExtension.ASTBuilder
module R = FStar.Reflection
val sugar_decl : Type0

val parse_pulse (env:R.env) 
                (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
  : Dv (either Pulse.Syntax.decl (option (string & R.range)))
  // Option can be empty if all errors were already logged.

val desugar_pulse (env:R.env) 
                  (namespaces:list string)
                  (module_abbrevs:list (string & string))
                  (sugar:sugar_decl)
  : Dv (either Pulse.Syntax.decl (option (string & R.range)))
