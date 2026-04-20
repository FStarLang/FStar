module FStarC.TypeChecker.Primops

(* This module just contains the list of all builtin primitive steps
with their implementations. *)

open FStarC
open FStarC.Effect
open FStarC.List
open FStar.String
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Class.Monad
open FStarC.Class.Show

module BU = FStarC.Util
module PC = FStarC.Parser.Const
module EMB = FStarC.Syntax.Embeddings

open FStarC.TypeChecker.Primops.Base

(*******************************************************************)
(* Semantics for primitive operators (+, -, >, &&, ...)            *)
(*******************************************************************)

(* Most primitive steps don't use the NBE cbs, so they can use this wrapper. *)
let as_primitive_step is_strong l arity u_arity (f:interp_t) (f_nbe : nbe_interp_t) =
  Primops.Base.as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, f_nbe)

(* and_op and or_op are special cased because they are short-circuting,
  * can run without unembedding its second argument. *)
let and_op : psc -> EMB.norm_cb -> universes -> args -> ML (option term)
  = fun psc _norm_cb _us args ->
    match args with
    | [(a1, None); (a2, None)] ->
        begin match try_unembed_simple a1 with
        | Some false ->
          Some (embed_simple psc.psc_range false)
        | Some true ->
          Some a2
        | _ -> None
        end
    | _ -> failwith "Unexpected number of arguments"

let or_op : psc -> EMB.norm_cb -> universes -> args -> ML (option term)
  = fun psc _norm_cb _us args ->
    match args with
    | [(a1, None); (a2, None)] ->
        begin match try_unembed_simple a1 with
        | Some true ->
          Some (embed_simple psc.psc_range true)
        | Some false ->
          Some a2
        | _ -> None
        end
    | _ -> failwith "Unexpected number of arguments"


let division_modulus_op (f : int -> int -> int) (x y : int) : option int =
  if y <> 0
  then Some (f x y)
  else None

(* Simple primops that are just implemented by some concrete function
over embeddable types. *)
let simple_ops : list primitive_step = [
  (* Basic *)
  mk1' 0 PC.string_of_int_lid (fun z -> Some (show #int z)) (fun z -> Some (show #int z));
  mk1 0 PC.int_of_string_lid (fun s -> BU.safe_int_of_string s);
  mk1 0 PC.string_of_bool_lid string_of_bool;
  mk1 0 PC.bool_of_string_lid (function "true" -> Some true | "false" -> Some false | _ -> None);

  (* Integer opts *)
  mk1 0 PC.op_Minus        (fun x -> -x);
  mk2 0 PC.op_Addition     (+);
  mk2 0 PC.op_Subtraction  (-);
  mk2 0 PC.op_Star         ( * );
  mk2 0 PC.op_LT           (<);
  mk2 0 PC.op_LTE          (<=);
  mk2 0 PC.op_GT           (>);
  mk2 0 PC.op_GTE          (>=);

  (* Use ' variant to allow for non-reduction. Impl is the same on each normalizer. *)
  mk2' 0 PC.op_Division (division_modulus_op ( / )) ((division_modulus_op ( / )));
  mk2' 0 PC.op_Modulus  (division_modulus_op ( % )) ((division_modulus_op ( % )));

  (* Bool opts. NB: && and || are special-cased since they are
  short-circuiting, and can run even if their second arg does not
  try_unembed_simple. Otherwise the strict variants are defined as below. *)
  mk1 0 PC.op_Negation not;
  // mk2 0 PC.op_And (&&);
  // mk2 0 PC.op_Or  ( || );

  (* Operations from FStar.String *)
  mk2 0 PC.string_concat_lid String.concat;
  mk2 0 PC.string_split_lid String.split;
  mk2 0 PC.prims_strcat_lid (^);
  mk2 0 PC.string_compare_lid (fun s1 s2 -> String.compare s1 s2);
  mk1 0 PC.string_string_of_list_lid string_of_list;
  mk2' 0 PC.string_make_lid
    (fun x y -> Some (String.make x y))
    (fun x y -> Some (String.make x y));
  mk1 0 PC.string_list_of_string_lid list_of_string;
  mk1 0 PC.string_lowercase_lid String.lowercase;
  mk1 0 PC.string_uppercase_lid String.uppercase;
  mk2' 0 PC.string_index_lid
    (fun s i -> Some (String.index s i))
    (fun s i -> Some (String.index s i));
  mk2' 0 PC.string_index_of_lid
    (fun s c -> Some (String.index_of s c))
    (fun s c -> Some (String.index_of s c));
  mk3' 0 PC.string_sub_lid
    (fun s o l -> Some (String.substring s o l))
    (fun s o l -> Some (String.substring s o l));
]

let short_circuit_ops : list primitive_step =
  let nbe_and : nbe_interp_t =
    fun _cb _us args -> NBETerm.and_op args in
  let nbe_or : nbe_interp_t =
    fun _cb _us args -> NBETerm.or_op args in
  let s1 = as_primitive_step true PC.op_And 2 0 and_op nbe_and in
  let s2 = as_primitive_step true PC.op_Or 2 0 or_op nbe_or in
  [s1; s2]

let built_in_primitive_steps_list : list primitive_step =
  simple_ops
  @ short_circuit_ops
  @ Primops.Issue.ops
  @ Primops.Array.ops
  @ Primops.Sealed.ops
  @ Primops.Erased.ops
  @ Primops.Docs.ops
  @ Primops.MachineInts.ops
  @ Primops.Errors.Msg.ops
  @ Primops.Range.ops
  @ Primops.Real.ops

let env_dependent_ops (env:Env.env_t) : ML _ = Primops.Eq.dec_eq_ops env

let simplification_ops_list (env:Env.env_t) : ML (list primitive_step) =
  Primops.Eq.prop_eq_ops env
  @ Primops.Real.simplify_ops
  @ Primops.Erased.simplify_ops
