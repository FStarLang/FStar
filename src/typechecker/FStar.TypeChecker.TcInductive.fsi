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
#light "off"
module FStar.TypeChecker.TcInductive
open FStar.ST
open FStar.All
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common

val check_inductive_well_typedness: env_t -> list<sigelt> -> list<qualifier> -> list<lident> -> (sigelt * list<sigelt> * list<sigelt>)
val check_positivity: sigelt -> env -> bool
val check_exn_positivity: lid -> env -> bool

val early_prims_inductives :list<string>

val is_haseq_lid: lid -> bool  //see if the given lid is that of an haseq axiom
val get_haseq_axiom_lid: lid -> lid  //for the given inductive tycon lid, get the haseq axiom lid
val optimized_haseq_scheme: sigelt -> list<sigelt> -> list<sigelt> -> env_t -> list<sigelt>
val unoptimized_haseq_scheme: sigelt -> list<sigelt> -> list<sigelt> -> env_t -> list<sigelt>

val mk_data_operations: list<qualifier> -> env -> list<sigelt> -> sigelt -> list<sigelt>  //elaborate discriminator and projectors
