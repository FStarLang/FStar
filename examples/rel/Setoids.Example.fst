module Setoids.Example

open Setoids

module DM = FStar.DependentMap

/// Some basic functions and the same effect as for the crypto example, but without random tape.

let option_rel (#a:Type) (arel:rel a) =
  fun (x:option a) (y:option a) ->
    match x,y with
    | None,None -> True // <: prop
    | Some some_x, Some some_y -> (arel some_y some_x) // <: prop
    | _, _ -> False // <: prop

let eff (#s:Type) (#a:Type) (srel:rel s) (arel:rel a) =
  srel ^--> ((option_rel arel) ** srel)

#set-options "--z3rlimit 150 --query_stats"
let eff_rel #s #a
    (srel: erel s)
    (arel: erel a)
    : erel (eff srel arel)
  = arrow_rel srel ((option_rel #a arel) ** srel)

/// returning a result into a computation
let return (#s:Type) (#a:Type) (#srel:erel s) (#arel:erel a) (x:a)
  : eff #s #a srel arel
  = fun s0 -> Some x, s0

let lift_left (#s1:Type) (#s1rel:erel s1{lo s1 == s1rel}) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s1rel arel)
  : ((s1rel ** s2rel) ^--> ((option_rel arel) ** (s1rel ** s2rel)))
  = fun (s1, s2) ->
      match f s1 with
      | None, s1' ->
        None, (s1', s2)

      | Some x, s1' ->
        Some x, (s1', s2)

let lift_right #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2{s2rel == lo s2}) #a (#arel:erel a) (f:eff s2rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (s1, s2) ->
      match f s2 with
      | None, s2' -> None, (s1, s2')
      | Some x, s2' -> Some x, (s1, s2')

/// sequential composition of `eff` computations
#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 2 --query_stats"
let bind #s #a (#srel:erel s) (#arel:erel a) #b (#brel:erel b)
         ($f:eff #s #a srel arel)
         (g:arel ^--> eff_rel #s #b srel brel)
   : eff #s #b srel brel =
   fun s0 ->
     match f s0 with
     | Some x, s1 ->
       g x (s1)
     | None, s1 ->
       None, s1

/// reading the entire state
let get #s (#srel:erel s) : eff srel srel =
  fun s0 -> Some s0, s0

/// writing the entire state
let put #s (#srel:erel s) : (srel ^--> eff_rel srel (lo unit)) =
  fun s _ -> Some (), s

let get_oracle #sig (m:module_t sig) (o:sig.labels) : sig.ops o = DM.sel m o

/// Examples of simple module compositions using the simple state monad
/// introduced in the Setoids package.

/// First, we introduce a package that contains an integer and that exposes a
/// function to "get" the integer. Then we introduce another package that
/// exposes a function that calls the "get" function and compares its input to
/// the integer contained in the integer container.

let int_container_st = int
let int_container_state_rel = lo int

let get_int_t = lo unit ^--> eff_rel int_container_state_rel (lo int)
let get_int :get_int_t =
  fun _ ->
    st <-- get;
    return st

type int_container_labels =
  | GET

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let int_container_field_types : int_container_labels -> Type =
    function GET -> get_int_t

let int_container_field_rels : (l:int_container_labels -> erel (int_container_field_types l)) =
  function
    GET ->
      arrow
        (lo unit)
        (eff_rel (int_container_state_rel) (lo int))

let int_container_sig = {
    labels = int_container_labels;
    ops = int_container_field_types;
    rels = int_container_field_rels
  }

let int_container_module : module_t (int_container_sig) =
  DM.create #_ #(int_container_sig).ops
    (function GET -> get_int)

let int_container_functor
  : functor_t (sig_unit) (int_container_sig)
  = fun (k:module_t (sig_unit)) ->
      int_container_module

let eq_checker_st = int
let eq_checker_state_rel = lo int

let combined_state_rel = int_container_state_rel ** eq_checker_state_rel

/// This function compares the input of the function with either
/// 1. the value in the composed int_container
/// or
/// 2. the value in the eq_checker itself.
/// The whole module only casts to a functor if 2. is the case.
let is_eq_t = lo int ^--> eff_rel combined_state_rel (lo bool)
let is_eq (ih:module_t int_container_sig) : is_eq_t =
  fun x ->
    let get_int : get_int_t = get_oracle ih GET in
    // 1:
    st <--
      lift_left
      (get_int ());
    return (st = x)
    // 2:
    //st <-- get;
    //let st1,st2 = st in
    //return (st1 = x)

type eq_checker_labels =
  | IS_EQ

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 1"
let eq_checker_field_types : eq_checker_labels -> Type =
    function  IS_EQ -> is_eq_t

let eq_checker_field_rels : (l:eq_checker_labels -> erel (eq_checker_field_types l)) =
  function
      IS_EQ ->
        arrow
          (lo int)
          (eff_rel (combined_state_rel) (lo bool))

let eq_checker_sig = {
    labels = eq_checker_labels;
    ops = eq_checker_field_types;
    rels = eq_checker_field_rels
  }

let eq_checker_module (ih:module_t int_container_sig) : module_t (eq_checker_sig) =
  DM.create #_ #(eq_checker_sig).ops
    (function IS_EQ -> is_eq ih)

#set-options "--z3rlimit 350 --max_fuel 0 --max_ifuel 0"
#set-options "--query_stats"
let eq_checker_functor
  : functor_t (int_container_sig) (eq_checker_sig)
  = fun (ih:module_t (int_container_sig)) ->
      eq_checker_module ih
