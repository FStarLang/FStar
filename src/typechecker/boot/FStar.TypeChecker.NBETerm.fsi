#light "off"
module FStar.TypeChecker.NBETerm
open FStar.All
open FStar.Exn
open FStar
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module P = FStar.Syntax.Print
module BU = FStar.Util
module Env = FStar.TypeChecker.Env
module Z = FStar.BigInt
module C = FStar.Const

type var = bv
type sort = int

type constant =
  | Unit
  | Bool of bool
  | Int of Z.t
  | String of string * Range.range
  | Char of FStar.Char.char

//IN F*: type atom : Type0 =
type atom = //JUST FSHARP
  | Var of var
  | Match of t *
             (t -> t) * 
             ((t -> term) -> list<branch>)
  | Rec of letbinding * list<letbinding> * list<t>
//IN F*: and t : Type0 =
and t = //JUST FSHARP
  | Lam of (t -> t) * (unit -> t) * aqual
  | Accu of atom * args
  | Construct of fv * list<universe> * args
  | FV of fv * list<universe> * args
  | Constant of constant
  | Type_t of universe
  | Univ of universe
  | Unknown
  | Refinement of binder * t
and args = list<(t * aqual)>

type head = t
type annot = option<t>


// Printing functions

val constant_to_string : constant -> string
val t_to_string : t -> string
val atom_to_string : atom -> string

// NBE term manipulation 

val isAccu : t -> bool
val isNotAccu : t -> bool

val mkConstruct : fv -> list<universe> -> args -> t
val mkFV : fv -> list<universe> -> args -> t

val mkAccuVar : var -> t
val mkAccuMatch : t -> (t -> t) -> ((t -> term) -> list<branch>) -> t
val mkAccuRec : letbinding -> list<letbinding> -> list<t> -> t
