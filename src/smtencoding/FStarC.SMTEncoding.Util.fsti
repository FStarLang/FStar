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

module S = FStarC.Syntax.Syntax
module TcEnv = FStarC.TypeChecker.Env

val mkAssume : term & caption & string -> ML decl

val norng  (f : 'a -> Range.t -> ML term) : 'a -> ML term
val norng2 (f : 'a -> 'b -> Range.t -> ML term) : 'a -> 'b -> ML term
val norng3 (f : 'a -> 'b -> 'c -> Range.t -> ML term) : 'a -> 'b -> 'c -> ML term
val norng4 (f : 'a -> 'b -> 'c -> 'd -> Range.t -> ML term) : 'a -> 'b -> 'c -> 'd -> ML term

val mkTrue : term
val mkFalse : term
val mkInteger : string -> ML term
val mkInteger' : int -> ML term
val mkReal : string -> ML term
val mkBoundV : int -> ML term
val mkFreeV : fv -> ML term

val mkApp' : op & list term -> ML term
val mkApp : string & list term -> ML term
val mkNot : term -> ML term
val mkMinus : term -> ML term
val mkAnd : term & term -> ML term
val mkOr : term & term -> ML term
val mkImp : term & term -> ML term
val mkIff : term & term -> ML term
val mkEq : term & term -> ML term
val mkLT : term & term -> ML term
val mkLTE : term & term -> ML term
val mkGT : term & term -> ML term
val mkGTE : term & term -> ML term
val mkAdd : term & term -> ML term
val mkSub : term & term -> ML term
val mkDiv : term & term -> ML term
val mkRealDiv : term & term -> ML term
val mkMul : term & term -> ML term
val mkMod : term & term -> ML term

(* bitvector ops, some indexed by bitvector size *)
val mkNatToBv : int -> term -> ML term
val mkBvAnd   : term & term -> ML term
val mkBvXor   : term & term -> ML term
val mkBvOr    : term & term -> ML term
val mkBvAdd   : term & term -> ML term
val mkBvSub   : term & term -> ML term
val mkBvShl   : int -> term & term -> ML term
val mkBvShr   : int -> term & term -> ML term
val mkBvRol   : int -> term & term -> ML term
val mkBvRor   : int -> term & term -> ML term
val mkBvUdiv  : int -> term & term -> ML term
val mkBvMod   : int -> term & term -> ML term
val mkBvMul   : int -> term & term -> ML term
val mkBvShl'  : int -> term & term -> ML term
val mkBvShr'  : int -> term & term -> ML term
val mkBvRol'  : int -> term & term -> ML term
val mkBvRor'  : int -> term & term -> ML term
val mkBvUdivUnsafe : int -> term & term -> ML term
val mkBvModUnsafe  : int -> term & term -> ML term
val mkBvMul'   : int -> term & term -> ML term
val mkBvUlt    : term & term -> ML term
val mkBvUext   : int -> term -> ML term
val mkBvNot    : term -> ML term
val mkBvToNat  : term -> ML term

val mkITE : term & term & term -> ML term
val mkCases : list term -> ML term

val mk_Term_app : term -> term -> ML term
val mk_and_l : list term -> ML term
val mk_or_l : list term -> ML term
val mk_ApplyTT : term -> term -> ML term
val mk_String_const : string -> ML term
val mk_Precedes : term -> term -> term -> term -> term -> term -> ML term
val mk_LexCons : term -> term -> term -> ML term
val mk_lex_t : term
val mk_LexTop : term


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

val is_smt_reifiable_effect (en:TcEnv.env) (l:lident) : ML bool

val is_smt_reifiable_comp (en:TcEnv.env) (c:S.comp) : ML bool

//
// TAC rc are not smt reifiable
//

val is_smt_reifiable_rc (en:TcEnv.env) (rc:S.residual_comp) : ML bool

val is_smt_reifiable_function (en:TcEnv.env) (t:S.term) : ML bool
