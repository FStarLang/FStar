module Setoids.Example

open Setoids
module C = FStar.Classical
module DM = FStar.DependentMap

#set-options "--max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
/// Some basic functions and the same effect as for the crypto example, but without random tape.

let option_rel (#a:Type) (arel:erel a) : erel (option a) =
  fun (x:option a) (y:option a) ->
    match x,y with
    | None,None -> True
    | Some some_x, Some some_y -> (arel some_y some_x)
    | _, _ -> False

let eff (#s:Type) (#a:Type) (srel:erel s) (arel:erel a) =
  srel ^--> ((option_rel arel) ** srel)

let eff_rel #s #a
    (srel: erel s)
    (arel: erel a)
    : erel (eff srel arel)
  = e_arrow_rel srel ((option_rel #a arel) ** srel)

/// returning a result into a computation
unfold
let return (#s:Type) (#a:Type) (#srel:erel s) (#arel:erel a) (x:a)
  : eff #s #a srel arel
  = fun s0 -> Some x, s0

unfold
let lift_left (#s1:Type) (#s1rel:erel s1) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s1rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (s1, s2) ->
      match f s1 with
      | None, s1' ->
        None, (s1', s2)
      | Some x, s1' ->
        Some x, (s1', s2)

unfold
let lift_right #s1 (#s1rel:erel s1) #s2 (#s2rel:erel s2) #a (#arel:erel a) (f:eff s2rel arel)
  : eff (s1rel ** s2rel) arel
  = fun (s1, s2) ->
      match f s2 with
      | None, s2' -> None, (s1, s2')
      | Some x, s2' -> Some x, (s1, s2')

/// sequential composition of `eff` computations
unfold
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
unfold
let get #s (#srel:erel s) : eff srel srel =
  fun s0 -> Some s0, s0

/// writing the entire state
unfold
let put #s (#srel:erel s) : (srel ^--> eff_rel srel (lo unit)) =
  fun s _ -> Some (), s

let get_oracle #sig (l:sig.labels) : (sig_rel sig ^--> sig.rels l) = fun m -> DM.sel m l

/// Examples of simple module compositions using the simple state monad
/// introduced in the Setoids package.

/// First, we introduce a package that contains an integer and that exposes a
/// function to "get" the integer. Then we introduce another package that
/// exposes a function that calls the "get" function and compares its input to
/// the integer contained in the integer container.

let int_container_st = int
let int_container_state_rel : erel _ = lo int

let get_int_t = lo unit ^--> eff_rel int_container_state_rel (lo int)
let get_int :get_int_t =
  fun _ ->
    st <-- get;
    return st

type int_container_labels =
  | GET

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

/// The eq_checker has no state.
let eq_checker_st = unit
let eq_checker_state_rel : erel _ = lo unit

let combined_state_rel : erel _ = int_container_state_rel ** eq_checker_state_rel

/// In order for two modules to be composed, every function needs to get an
/// instance of a module with the desired signature as input. However, we don't
/// want this additional input to appear in the signature. The solution here is
/// to have two types, where in the signature, only the truncated type (without
/// the additional input) is used. The consequence is, that the module can then
/// only be instantiated with the composed module as input (which seems sensible
/// to me), which implicitly makes it a functor (which I also think is not a bad
/// thing).
let is_eq_t = ((sig_rel int_container_sig) ** lo int) ^--> eff_rel combined_state_rel (lo bool)
let is_eq_t_trunc = (lo int) ^--> eff_rel combined_state_rel (lo bool)
let ( ^^--> ) (#a:Type) (#b:Type) (arel:rel a) (brel:rel b) =
  f:(a -> b)
let is_eq_t_base = ((sig_rel int_container_sig) ** lo int) ^^--> eff_rel combined_state_rel (lo bool)
let is_eq_t_rel = e_arrow_rel ((sig_rel int_container_sig) ** lo int) (eff_rel combined_state_rel (lo bool))

let cmp : (lo int ^--> (e_arrow_rel (lo int) (lo bool))) = fun x y -> x = y

let is_eq'  : is_eq_t_base =
  fun (ih, x) ->
    ((let get_int : get_int_t = get_oracle GET ih in
     ((st <-- lift_left (get_int ());
       return (x = st)) <: eff combined_state_rel (lo bool))))

module T = FStar.Tactics
open FStar.Tactics

let _goes_through_easily (a0 a1:type_of (sig_rel int_container_sig))
                         (s0 s1:type_of int_container_state_rel)
  : Lemma
      (requires
        a0 `(sig_rel int_container_sig)` a1 /\
        s0 `int_container_state_rel` s1)
      (ensures (
        let g0 : get_int_t = get_oracle GET a0 in
        let g1 : get_int_t = get_oracle GET a1 in
        g0 () s0 == g1 () s1))
  = ()

val get_related (a0 a1:type_of ((sig_rel int_container_sig) ** lo int))
                (s0 s1:type_of combined_state_rel)
  : Lemma
      (requires
        a0 `((sig_rel int_container_sig) ** lo int)` a1 /\
        s0 `combined_state_rel` s1)
      (ensures (
        let g0 : get_int_t = get_oracle GET (fst a0) in
        let g1 : get_int_t = get_oracle GET (fst a1) in
        let g00 : eff combined_state_rel (lo int) = lift_left (g0 () <: eff int_container_state_rel (lo int)) in
        let g11 : eff combined_state_rel (lo int) = lift_left (g1 () <: eff int_container_state_rel (lo int)) in
        g00 s0 == g11 s1))
let get_related a0 a1 s0 s1  =
    let g0 : get_int_t = get_oracle GET (fst a0) in
    let g1 : get_int_t = get_oracle GET (fst a1) in
    assert (g0 () (fst s0) `((option_rel (lo int)) ** (int_container_state_rel))` g1 () (fst s1))

let is_eq : is_eq_t =
  let aux (a0 a1:type_of ((sig_rel int_container_sig) ** lo int))
          (s0 s1:type_of combined_state_rel)
  : Lemma
      (requires
        a0 `((sig_rel int_container_sig) ** lo int)` a1 /\
        s0 `combined_state_rel` s1)
      (ensures
        (is_eq' a0 s0 `((option_rel (lo bool)) ** combined_state_rel)`
         is_eq' a1 s1))
     [SMTPat (is_eq' a0 s0);
      SMTPat (is_eq' a1 s1)]
  = get_related a0 a1 s0 s1
 in
 is_eq'

type eq_checker_labels =
  | IS_EQ

let eq_checker_field_types : eq_checker_labels -> Type =
  function  IS_EQ -> is_eq_t_trunc

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

let eq_checker_functor'
  : module_t int_container_sig -> module_t eq_checker_sig
  = fun ih ->
      let is_eq' : is_eq_t_trunc = fun x -> is_eq (ih,x) in
      let m : module_t (eq_checker_sig) = DM.create #_ #(eq_checker_sig).ops (function IS_EQ -> is_eq') in
      m

let eq_checker_functor
  : functor_t int_container_sig eq_checker_sig
  =
    let intro_eq_checker (i0 i1:module_t int_container_sig)
      : Lemma
        (requires
          i0 `sig_rel int_container_sig` i1)
        (ensures
          eq_checker_functor' i0 `sig_rel eq_checker_sig` eq_checker_functor' i1)
        [SMTPat (eq_checker_functor' i0);
         SMTPat (eq_checker_functor' i1)]
    = let m0 = eq_checker_functor' i0 in
      let m1 = eq_checker_functor' i1 in
      let is_eq_0 : is_eq_t_trunc = get_oracle IS_EQ m0 in
      let is_eq_1 : is_eq_t_trunc = get_oracle IS_EQ m1 in
      let aux (v0 v1:int) (s0 s1:_)
        : Lemma
          (requires
             v0 `lo int` v1 /\
             s0 `combined_state_rel` s1)
          (ensures
             is_eq_0 v0 s0
               `(option_rel (lo bool) ** combined_state_rel)`
             is_eq_1 v1 s1)
          [SMTPat (is_eq_0 v0 s0);
           SMTPat (is_eq_1 v1 s1)]
        = assert (is_eq_0 v0 s0 == is_eq (i0, v0) s0);
          assert (is_eq_1 v1 s1 == is_eq (i1, v1) s1);
          assert ((i0, v0) `(sig_rel int_container_sig ** lo int)` (i1, v1))
      in
      ()
    in
    eq_checker_functor'
