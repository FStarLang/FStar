#light "off"

module FStar.SMTEncoding.Util

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
module SS = FStar.Syntax.Subst
module N = FStar.TypeChecker.Normalize


let norng f = fun x -> f x Range.dummyRange
let mkTrue   = Term.mkTrue Range.dummyRange
let mkFalse  = Term.mkFalse Range.dummyRange
let mkInteger  = norng Term.mkInteger
let mkInteger' = norng Term.mkInteger'
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
let mkMul = norng mkMul
let mkMod = norng mkMod
let mkITE = norng mkITE
let mkCases = norng mkCases
let mkForall = norng mkForall
let mkForall' = norng mkForall'
let mkForall'' = norng mkForall''
let mkExists = norng mkExists

let norng2 f = fun x y -> f x y Range.dummyRange
let mk_Term_app  = norng2 mk_Term_app
let mk_Term_uvar = norng mk_Term_uvar
let mk_and_l = norng mk_and_l
let mk_or_l = norng mk_or_l
let mk_ApplyTT = norng2 mk_ApplyTT
let mk_String_const = norng mk_String_const
let mk_Precedes = norng2 mk_Precedes
let mk_LexCons = norng2 mk_LexCons

