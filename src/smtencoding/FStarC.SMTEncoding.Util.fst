(*
   Copyright 2008-2025 Microsoft Research

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

module FStarC.SMTEncoding.Util

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.SMTEncoding.Term
open FStarC.Ident

module Term = FStarC.SMTEncoding.Term
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module TcEnv = FStarC.TypeChecker.Env

let mkAssume x : ML decl =
    let (tm, cap, nm) = x in
    Assume ({
        assumption_name=escape nm;
        assumption_caption=cap;
        assumption_term=tm;
        assumption_fact_ids=[];
    })
let mkTrue = Term.mkTrue
let mkFalse = Term.mkFalse
let mkInteger = Term.mkInteger
let mkInteger' = Term.mkInteger'
let mkReal = Term.mkReal
let mkBoundV = Term.mkBoundV
let mkFreeV = Term.mkFreeV
let mkApp' = Term.mkApp'
let mkApp = Term.mkApp
let mkNot = Term.mkNot
let mkMinus = Term.mkMinus
let mkAnd = Term.mkAnd
let mkOr = Term.mkOr
let mkImp = Term.mkImp
let mkIff = Term.mkIff
let mkEq = Term.mkEq
let mkLT = Term.mkLT
let mkLTE = Term.mkLTE
let mkGT = Term.mkGT
let mkGTE = Term.mkGTE
let mkAdd = Term.mkAdd
let mkSub = Term.mkSub
let mkDiv = Term.mkDiv
let mkRealDiv = Term.mkRealDiv
let mkMul = Term.mkMul
let mkMod = Term.mkMod
let mkNatToBv = Term.mkNatToBv
let mkBvAnd = Term.mkBvAnd
let mkBvXor = Term.mkBvXor
let mkBvOr = Term.mkBvOr
let mkBvAdd = Term.mkBvAdd
let mkBvSub = Term.mkBvSub
let mkBvShl = Term.mkBvShl
let mkBvShr = Term.mkBvShr
let mkBvRol = Term.mkBvRol
let mkBvRor = Term.mkBvRor
let mkBvUdiv = Term.mkBvUdiv
let mkBvMod = Term.mkBvMod
let mkBvMul = Term.mkBvMul
let mkBvShl' = Term.mkBvShl'
let mkBvShr' = Term.mkBvShr'
let mkBvRol' = Term.mkBvRol'
let mkBvRor' = Term.mkBvRor'
let mkBvUdivUnsafe = Term.mkBvUdivUnsafe
let mkBvModUnsafe = Term.mkBvModUnsafe
let mkBvMul' = Term.mkBvMul'
let mkBvUlt = Term.mkBvUlt
let mkBvUext = Term.mkBvUext
let mkBvNot = Term.mkBvNot
let mkBvToNat = Term.mkBvToNat
let mkITE = Term.mkITE
let mkCases = Term.mkCases
let mk_Term_app = Term.mk_Term_app
let mk_and_l = Term.mk_and_l
let mk_or_l = Term.mk_or_l
let mk_ApplyTT = Term.mk_ApplyTT
let mk_String_const = Term.mk_String_const
let mk_Precedes = Term.mk_Precedes
let mk_LexCons = Term.mk_LexCons
let mk_lex_t = Term.mk_lex_t
let mk_LexTop = Term.mk_LexTop


(*
 * AR: When encoding abstractions that have a reifiable computation type
 *     for their bodies, we currently encode their reification
 *     Layered effects are also reifiable, but I don't think we want
 *     to encode their reification to smt
 *     So adding these utils, that are then used in Encode.fs and EncodeTerm.fs
 *
 *     Could revisit
 *
 *     06/22: reifying if the effect has the smt_reifiable_layered_effect attribute
 *     07/02: reverting, until we preserve the indices, no smt reification
 *)

let is_smt_reifiable_effect (en:TcEnv.env) (l:lident) : ML bool =
  TcEnv.is_reifiable_effect en l

let is_smt_reifiable_comp (en:TcEnv.env) (c:S.comp) : ML bool =
  match c.n with
  | Comp ct -> is_smt_reifiable_effect en ct.effect_name
  | _ -> false

//
// TAC rc are not smt reifiable
//

let is_smt_reifiable_rc (en:TcEnv.env) (rc:S.residual_comp) : ML bool =
  rc.residual_effect |> is_smt_reifiable_effect en

let is_smt_reifiable_function (en:TcEnv.env) (t:S.term) : ML bool =
  match (SS.compress t).n with
  | Tm_arrow _ ->
    snd (U.arrow_node_formals_comp_ln t) |> U.comp_effect_name |> is_smt_reifiable_effect en
  | _ -> false
