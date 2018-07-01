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
open FStar.Char

type var = bv
type sort = int

type constant =
  | Unit
  | Bool of bool
  | Int of Z.t
  | String of string * Range.range
  | Char of FStar.Char.char
  | Range of Range.range

type atom
//IN F*: : Type0
  =
  | Var of var
  | Match of t *
             (t -> t) *
             ((t -> term) -> list<branch>)
  | Rec of letbinding * list<letbinding> * list<t>

and t
//IN F*: : Type0
  =
  | Lam of (list<t> -> t) * list<(unit -> arg)> * int
  | Accu of atom * args
  | Construct of fv * list<universe> * args
  | FV of fv * list<universe> * args
  | Constant of constant
  | Type_t of universe
  | Univ of universe
  | Unknown
  | Arrow of (list<t> -> comp) * list<(unit -> arg)>
  | Refinement of (t -> t) * (unit -> arg) 
  | Quote of S.term * S.quoteinfo
  | Lazy of S.lazyinfo
and comp = 
  | Tot of t * option<universe>
  | GTot of t * option<universe>
  | Comp of comp_typ
and comp_typ = {
  comp_univs:universes;
  effect_name:lident;
  result_typ:t;
  effect_args:args;
  flags:list<cflags>
}

and arg = t * aqual
and args = list<(arg)>

type head = t
type annot = option<t>

// Term equality
val eq_t : t -> t -> U.eq_result
val eq_atom : atom -> atom -> U.eq_result
val eq_arg : arg -> arg -> U.eq_result
val eq_args : args -> args -> U.eq_result
val eq_constant : constant -> constant -> U.eq_result

// Printing functions

val constant_to_string : constant -> string
val t_to_string : t -> string
val atom_to_string : atom -> string
val arg_to_string : arg -> string
val args_to_string : args -> string

// NBE term manipulation

val isAccu : t -> bool
val isNotAccu : t -> bool

val mkConstruct : fv -> list<universe> -> args -> t
val mkFV : fv -> list<universe> -> args -> t

val mkAccuVar : var -> t
val mkAccuMatch : t -> (t -> t) -> ((t -> term) -> list<branch>) -> t
val mkAccuRec : letbinding -> list<letbinding> -> list<t> -> t

val as_arg : t -> arg
val as_iarg : t -> arg

type embedding<'a> = {
  em  : 'a -> t;
  un  : t -> option<'a>;
  typ : t;
}

val mk_emb : ('a -> t) -> (t -> option<'a>) -> t -> embedding<'a>

val embed : embedding<'a> -> 'a -> t
val unembed : embedding<'a> -> t -> option<'a> 
val type_of : embedding<'a> -> t

val e_bool   : embedding<bool>
val e_string : embedding<string>
val e_char   : embedding<char>
val e_int    : embedding<Z.t>
val e_unit   : embedding<unit>
val e_any    : embedding<t>
val e_range  : embedding<Range.range>
val e_list   : embedding<'a> -> embedding<list<'a>>
val e_option : embedding<'a> -> embedding<option<'a>>
val e_tuple2 : embedding<'a> -> embedding<'b> -> embedding<('a * 'b)>

// Interface for NBE interpretations

val arg_as_int : arg -> option<Z.t>
val arg_as_bool : arg -> option<bool>
val arg_as_char : arg -> option<FStar.Char.char>
val arg_as_string : arg -> option<string>
val arg_as_list : embedding<'a> -> arg -> option<list<'a>>
val arg_as_bounded_int : arg -> option<(fv * Z.t)>

val int_as_bounded : fv -> Z.t -> t

val unary_int_op : (Z.t -> Z.t) -> (args -> option<t>)
val binary_int_op : (Z.t -> Z.t -> Z.t) -> (args -> option<t>)

val unary_bool_op : (bool -> bool) -> (args -> option<t>)
val binary_bool_op : (bool -> bool -> bool) -> (args -> option<t>)

val binary_string_op : (string -> string -> string) -> (args -> option<t>)

val string_of_int : Z.t -> t
val string_of_bool : bool -> t
val string_of_list' : list<char> -> t
val string_compare' : string -> string -> t
val string_concat' : args -> option<t>
val string_substring' : args -> option<t>
val string_split' : args -> option<t>

val list_of_string' : (string -> t)

val decidable_eq : bool -> args -> option<t>
val interp_prop : args -> option<t>

val mixed_binary_op : (arg -> option<'a>) -> (arg -> option<'b>) -> ('c -> t) ->
                      ('a -> 'b -> 'c) -> args -> option<t>
val unary_op : (arg -> option<'a>) -> ('a -> t) -> (args -> option<t>)
val binary_op : (arg -> option<'a>) -> ('a -> 'a -> t) -> (args -> option<t>)

val dummy_interp : Ident.lid -> args -> option<t>
val prims_to_fstar_range_step : args -> option<t>
