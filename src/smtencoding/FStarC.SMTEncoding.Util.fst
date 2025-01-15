(*
   Copyright 2008-2014 Microsoft Research

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
open FStarC.Effect

open FStarC
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.SMTEncoding.Term
open FStarC.Ident
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module SS = FStarC.Syntax.Subst
module TcEnv = FStarC.TypeChecker.Env

let mkAssume (tm, cap, nm) =
    Assume ({
        assumption_name=escape nm;
        assumption_caption=cap;
        assumption_term=tm;
        assumption_fact_ids=[];
        assumption_free_names=free_top_level_names tm;
    })
let norng f = fun x -> f x Range.dummyRange
let mkTrue   = mkTrue Range.dummyRange
let mkFalse  = mkFalse Range.dummyRange
let mkInteger  = norng mkInteger
let mkInteger' = norng mkInteger'
let mkReal     = norng mkReal
let mkBoundV   = norng mkBoundV
let mkFreeV    = norng mkFreeV
let mkApp'     = norng mkApp'
let mkApp      = norng mkApp
let mkNot = norng mkNot
let mkMinus = norng mkMinus
let mkAnd = norng mkAnd
let mkOr = norng mkOr
let mkImp = norng mkImp
let mkIff = norng mkIff
let mkEq = norng mkEq
let mkLT = norng mkLT
let mkLTE = norng mkLTE
let mkGT = norng mkGT
let mkGTE = norng mkGTE
let mkAdd = norng mkAdd
let mkSub = norng mkSub
let mkDiv = norng mkDiv
let mkRealDiv = norng mkRealDiv
let mkMul = norng mkMul
let mkMod = norng mkMod
let mkNatToBv sz = norng (mkNatToBv sz)
let mkBvAnd = norng mkBvAnd
let mkBvXor = norng mkBvXor
let mkBvOr = norng mkBvOr
let mkBvAdd = norng mkBvAdd
let mkBvSub = norng mkBvSub
let mkBvShl sz = norng (mkBvShl sz)
let mkBvShr sz = norng (mkBvShr sz)
let mkBvUdiv sz = norng (mkBvUdiv sz)
let mkBvMod sz = norng (mkBvMod sz)
let mkBvMul sz = norng (mkBvMul sz)
let mkBvShl' sz = norng (mkBvShl' sz)
let mkBvShr' sz = norng (mkBvShr' sz)
let mkBvUdivUnsafe sz = norng (mkBvUdivUnsafe sz)
let mkBvModUnsafe  sz = norng (mkBvModUnsafe sz)
let mkBvMul' sz = norng (mkBvMul' sz)
let mkBvUlt = norng mkBvUlt
let mkBvUext sz = norng (mkBvUext sz)
let mkBvToNat = norng mkBvToNat
let mkITE = norng mkITE
let mkCases = norng mkCases

let norng2 f = fun x y -> f x y Range.dummyRange
let norng3 f = fun x y z -> f x y z Range.dummyRange
let norng4 f = fun x y z w -> f x y z w Range.dummyRange
let mk_Term_app  = norng2 mk_Term_app
let mk_Term_uvar = norng mk_Term_uvar
let mk_and_l = norng mk_and_l
let mk_or_l = norng mk_or_l
let mk_ApplyTT = norng2 mk_ApplyTT
let mk_String_const = norng mk_String_const
let mk_Precedes = norng4 mk_Precedes


(*
 * AR: When encoding abstractions that have a reifiable computation type
 *     for their bodies, we currently encode their reification
 *     Earlier this was fine, since the only reifiable effects came from DM4F
 *     But now layered effects are also reifiable, but I don't think we want
 *     to encode their reification to smt
 *     So adding these utils, that are then used in Encode.fs and EncodeTerm.fs
 *
 *     Could revisit
 *
 *     06/22: reifying if the effect has the smt_reifiable_layered_effect attribute
 *     07/02: reverting, until we preserve the indices, no smt reification
 *)

let is_smt_reifiable_effect (en:TcEnv.env) (l:lident) : bool =
  let l = TcEnv.norm_eff_name en l in
  TcEnv.is_reifiable_effect en l &&
  not (l |> TcEnv.get_effect_decl en |> U.is_layered)

let is_smt_reifiable_comp (en:TcEnv.env) (c:S.comp) : bool =
  match c.n with
  | Comp ct -> is_smt_reifiable_effect en ct.effect_name
  | _ -> false

//
// TAC rc are not smt reifiable
//

let is_smt_reifiable_rc (en:TcEnv.env) (rc:S.residual_comp) : bool =
  rc.residual_effect |> is_smt_reifiable_effect en

let is_smt_reifiable_function (en:TcEnv.env) (t:S.term) : bool =
  match (SS.compress t).n with
  | Tm_arrow {comp=c} ->
    c |> U.comp_effect_name |> is_smt_reifiable_effect en
  | _ -> false
