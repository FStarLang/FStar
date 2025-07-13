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

val mkAssume : term & caption & string -> decl

val norng  (f : 'a -> Range.t -> term) : 'a -> term
val norng2 (f : 'a -> 'b -> Range.t -> term) : 'a -> 'b -> term
val norng3 (f : 'a -> 'b -> 'c -> Range.t -> term) : 'a -> 'b -> 'c -> term
val norng4 (f : 'a -> 'b -> 'c -> 'd -> Range.t -> term) : 'a -> 'b -> 'c -> 'd -> term

val mkTrue : term
val mkFalse : term
val mkInteger : string -> term
val mkInteger' : int -> term
val mkReal : string -> term
val mkBoundV : int -> term
val mkFreeV : fv -> term

val mkApp' : op & list term -> term
val mkApp : string & list term -> term
val mkNot : term -> term
val mkMinus : term -> term
val mkAnd : term & term -> term
val mkOr : term & term -> term
val mkImp : term & term -> term
val mkIff : term & term -> term
val mkEq : term & term -> term
val mkLT : term & term -> term
val mkLTE : term & term -> term
val mkGT : term & term -> term
val mkGTE : term & term -> term
val mkAdd : term & term -> term
val mkSub : term & term -> term
val mkDiv : term & term -> term
val mkRealDiv : term & term -> term
val mkMul : term & term -> term
val mkMod : term & term -> term

(* bitvector ops, some indexed by bitvector size *)
val mkNatToBv : int -> term -> term
val mkBvAnd   : term & term -> term
val mkBvXor   : term & term -> term
val mkBvOr    : term & term -> term
val mkBvAdd   : term & term -> term
val mkBvSub   : term & term -> term
val mkBvShl   : int -> term & term -> term
val mkBvShr   : int -> term & term -> term
val mkBvUdiv  : int -> term & term -> term
val mkBvMod   : int -> term & term -> term
val mkBvMul   : int -> term & term -> term
val mkBvShl'  : int -> term & term -> term
val mkBvShr'  : int -> term & term -> term
val mkBvUdivUnsafe : int -> term & term -> term
val mkBvModUnsafe  : int -> term & term -> term
val mkBvMul'   : int -> term & term -> term
val mkBvUlt    : term & term -> term
val mkBvUext   : int -> term -> term
val mkBvToNat  : term -> term

val mkITE : term & term & term -> term
val mkCases : list term -> term

val mk_Term_app : term -> term -> term
val mk_and_l : list term -> term
val mk_or_l : list term -> term
val mk_ApplyTT : term -> term -> term
val mk_String_const : string -> term
val mk_Precedes : term -> term -> term -> term -> term


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

val is_smt_reifiable_effect (en:TcEnv.env) (l:lident) : bool

val is_smt_reifiable_comp (en:TcEnv.env) (c:S.comp) : bool

//
// TAC rc are not smt reifiable
//

val is_smt_reifiable_rc (en:TcEnv.env) (rc:S.residual_comp) : bool

val is_smt_reifiable_function (en:TcEnv.env) (t:S.term) : bool
