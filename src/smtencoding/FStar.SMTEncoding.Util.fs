#light "off"

module FStar.SMTEncoding.Util
open FStar.ST
open FStar.All

open FStar
open FStar.TypeChecker.Env
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.SMTEncoding.Term
open FStar.Ident
open FStar.Const
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize
module TcEnv = FStar.TypeChecker.Env

let mkAssume (tm, cap, nm) =
    Assume ({
        assumption_name=escape nm;
        assumption_caption=cap;
        assumption_term=tm;
        assumption_fact_ids=[]
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
let mk_LexCons = norng3 mk_LexCons


(*
 * AR: When encoding abstractions that have a reifiable computation type
 *     for their bodies, we currently encode their reification
 *     Earlier this was fine, since the only reifiable effects came from DM4F
 *     But now layered effects are also reifiable, but I don't think we want
 *     to encode their reification to smt
 *     So adding these utils, that are then used in Encode.fs and EncodeTerm.fs
 *
 *     Could revisit
 *)

let is_smt_reifiable_effect (en:TcEnv.env) (l:lident) : bool =
  TcEnv.is_reifiable_effect en l &&
  not (l |> TcEnv.norm_eff_name en
         |> TcEnv.get_effect_decl en
         |> U.is_layered)

let is_smt_reifiable_comp (en:TcEnv.env) (c:S.comp) : bool =
  match c.n with
  | Comp ct -> is_smt_reifiable_effect en ct.effect_name
  | _ -> false

let is_smt_reifiable_rc (en:TcEnv.env) (rc:S.residual_comp) : bool =
  is_smt_reifiable_effect en rc.residual_effect

let is_smt_reifiable_function (en:TcEnv.env) (t:S.term) : bool =
  match (SS.compress t).n with
  | Tm_arrow (_, c) -> is_smt_reifiable_comp en c
  | _ -> false
