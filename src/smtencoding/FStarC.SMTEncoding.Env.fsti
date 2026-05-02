(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.SMTEncoding.Env

open FStarC
open FStarC.Effect
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.SMTEncoding.Term
open FStarC.Ident
open FStarC.SMTEncoding.Util

open FStarC.Class.Show

val add_fuel : 'a -> list 'a -> ML (list 'a)
val withenv : 'c -> ('a & 'b) -> ('a & 'b & 'c)
val vargs : list (either typ term & 'b) -> ML (list (either typ term & 'b))

val escape : string -> string
val mk_term_projector_name : lident -> bv -> ML string
val mk_univ_projector_name : lident -> int -> ML string
val primitive_projector_by_pos : Env.env -> lident -> int -> ML string
val mk_term_projector_name_by_pos : lident -> int -> ML string
val mk_term_projector : lident -> bv -> ML term
val mk_term_projector_by_pos : lident -> int -> ML term
val mk_data_tester : 'a -> lident -> term -> ML term

type varops_t = {
    push: unit -> ML unit;
    pop: unit -> ML unit;
    snapshot: unit -> ML (int & unit);
    rollback: option int -> ML unit;
    new_var:ident -> int -> ML string;
    new_fvar:lident -> ML string;
    fresh:string -> string -> ML string;
    reset_fresh:unit -> ML unit;
    next_id: unit -> ML int;
    mk_unique:string -> ML string;
    reset_scope: unit -> ML unit
}

val varops : varops_t

type fvar_binding = {
    fvar_lid:  lident;
    univ_arity : int;
    smt_arity: int;
    smt_id:    string;
    smt_token: option term;
    smt_fuel_partial_app:option (term & term);
    fvb_thunked: bool;
    needs_fuel_and_universe_instantiations: option univ_names;
}

val list_of : int -> (int -> ML 'a) -> ML (list 'a)
val kick_partial_app : fvar_binding -> ML (option term)
val fvb_to_string : fvar_binding -> ML string

instance val showable_fvar_binding : showable fvar_binding

val check_valid_fvb : fvar_binding -> ML unit
val binder_of_eithervar : 'a -> ('a & option 'b)

type env_t = {
    bvar_bindings: PSMap.t (PIMap.t (bv & term));
    fvar_bindings: (PSMap.t fvar_binding & list fvar_binding);
    depth:int;
    tcenv:Env.env;
    warn:bool;
    nolabels:bool;
    use_zfuel_name:bool;
    encode_non_total_function_typ:bool;
    current_module_name:string;
    encoding_quantifier:bool;
    global_cache:SMap.t (decls_elt & lident);
}

val print_env : env_t -> ML string
val lookup_bvar_binding : env_t -> bv -> option (bv & term)
val lookup_fvar_binding : env_t -> lident -> option fvar_binding
val add_bvar_binding : (bv & term) -> PSMap.t (PIMap.t (bv & term)) -> ML (PSMap.t (PIMap.t (bv & term)))
val add_fvar_binding : fvar_binding -> (PSMap.t fvar_binding & list fvar_binding) -> (PSMap.t fvar_binding & list fvar_binding)
val fresh_fvar : string -> string -> sort -> ML (string & term)
val gen_term_var : env_t -> bv -> ML (string & term & env_t)
val new_term_constant : env_t -> bv -> ML (string & term & env_t)
val new_term_constant_from_string : env_t -> bv -> string -> ML (string & term & env_t)
val push_term_var : env_t -> bv -> term -> ML env_t
val lookup_term_var : env_t -> bv -> ML term
val mk_fvb : lident -> string -> int -> int -> option term -> option (term & term) -> bool -> option univ_names -> ML fvar_binding
val new_term_constant_and_tok_from_lid : env_t -> lident -> int -> int -> ML (string & string & env_t)
val new_term_constant_and_tok_from_lid_maybe_thunked : env_t -> lident -> int -> int -> bool -> ML (string & option string & env_t)
val fail_fvar_lookup : env_t -> lident -> ML 'a
val lookup_lid : env_t -> lident -> ML fvar_binding
val push_free_var_maybe_thunked_with_univs : env_t -> lident -> int -> int -> string -> option term -> bool -> option univ_names -> ML env_t
val push_free_var_maybe_thunked : env_t -> lident -> int -> int -> string -> option term -> bool -> ML env_t
val push_free_var_tok_with_fuel_and_univs : env_t -> lident -> int -> int -> string -> option term -> univ_names -> ML env_t
val push_free_var : env_t -> lident -> int -> int -> string -> option term -> ML env_t
val push_free_var_thunk : env_t -> lident -> int -> int -> string -> option term -> ML env_t
val push_zfuel_name : env_t -> lident -> string -> string -> ML env_t
val force_thunk : fvar_binding -> ML term
val try_lookup_free_var : env_t -> lident -> ML (option term)
val lookup_free_var : env_t -> lident -> ML term
val lookup_free_var_name : env_t -> lident -> ML fvar_binding
val lookup_free_var_sym : env_t -> lident -> ML (either op term & list term & int)
val tok_of_name : env_t -> string -> ML (option term)
val reset_current_module_fvbs : env_t -> env_t
val get_current_module_fvbs : env_t -> list fvar_binding
val add_fvar_binding_to_env : fvar_binding -> env_t -> ML env_t
