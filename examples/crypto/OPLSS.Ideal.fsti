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
module OPLSS.Ideal
(* This interface captures the sequence of idealization steps 
   that we'll make. 
   
   Each concrete use of an idealization flag is a cryptographic
   hypothesis and should be treated as an `assume`, i.e., each such
   hypothesis should be validates as being cryptographically justified
   by an expert.
*)
open OPLSS.Flag

//we're idealizing MACs
val uf_cma : flag 

//after idealizing MAC's
//we're pre-idealizing encryption, but without any loss of security
val pre_ind_cpa : b:flag{ reveal b == reveal uf_cma }

//finally, we're idealizing encryption for secrecy, at the end
val ind_cpa : b:flag{ reveal b ==> reveal pre_ind_cpa }

//we get authenticated encryption after idealizing everyting
// -- we write it this way to make explicit 
//    that all the idealization flags are on, 
//    rather than just ind_cpa
val ae : b:flag{ reveal b = reveal pre_ind_cpa &&
                            reveal uf_cma &&
                            reveal ind_cpa }

//we get authenticity when uf_cma is on
let auth = uf_cma

//we get confidentiality when ind_cpa is on
let conf = ind_cpa
