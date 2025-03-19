
(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
module FStarC.Extraction.ML.Modul
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Extraction.ML.Syntax
open FStarC.Extraction.ML.UEnv

val iface : Type0

type extension_sigelt_extractor =
  uenv -> sigelt -> FStarC.Dyn.dyn -> either (list mlmodule1) string
type extension_sigelt_iface_extractor =
  uenv -> sigelt -> FStarC.Dyn.dyn -> either (uenv & iface) string

type extension_extractor = {
   extract_sigelt : extension_sigelt_extractor;
   extract_sigelt_iface : extension_sigelt_iface_extractor;
}

val register_extension_extractor
         (extension_name:string)
         (extractor:extension_extractor)
  : unit

val extract_iface: uenv -> modul -> uenv & iface
val extract : uenv -> modul -> uenv & option mlmodule
