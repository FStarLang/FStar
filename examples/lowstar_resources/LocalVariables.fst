module LocalVariables
module DM = FStar.DependentMap

// Here's a sketch of how I'd like to see mutable local variables
// modeled in Low*. The basic idea is in the style of modeling
// register files in typed assembly language.

// At a given program point, the values of all the local variables are
// held in a hetergeneous map. As the program evolves, both the type
// of this map can evolve (e.g., as new local variables are created)
// as well as the values of variables (as they are updated)

// We first define a notion of local variable typings

// Then, the local variable store, desribed by those typings

// Finally, an effect for stateful computations that use both heap and
// local variables

(*** LOCAL VARIABLE TYPING ***)

/// var_name: we'll reference local variables by nats
let var_name = nat

/// lvar_types: the type of the entire register file
let lvar_types
  : Type
  = var_name -> Type

/// unit_map: a default local variable, where they're all just unit
let unit_map
  : lvar_types
  = fun _ -> unit

/// upd_t: updating the register type of `n`
let upd_t (l:lvar_types) (n:var_name) (t:Type)
  : lvar_types
  = fun x -> if x = n then t else l x

/// sel_t: selecting the register type for `n`
let sel_t (l:lvar_types) (n:var_name)
  : Type
  = l n

(*** LOCAL VARIABLE STATE ***)

/// local_variables t: a map that holds the current value of all variables
/// The type of the map is `t`
let local_variables (t:lvar_types)
  : Type
  = DM.t var_name t

/// empty_map: unit in all the cells
let empty_map
  : local_variables unit_map
  = DM.create (fun _ -> ())

/// upd_map: updates the map at x; does not update the map's type
let upd_map (l:local_variables 't) (x:var_name) (v:'t x)
  : local_variables 't
  = DM.upd l x v

/// strong_upd_map: updates the map at x, changing its type from `'t x` to `'s`
let strong_upd_map (l:local_variables 't) (x:var_name) (y:'s)
  : local_variables (upd_t 't x 's)
  = DM.create #var_name #(upd_t 't x 's) (fun i -> if i = x then y else DM.sel l i)

/// sel_map: reading the contents of local variable x
let sel_map (l:local_variables 't) (x:var_name)
  : 't x
  = DM.sel l x

(*** An effect for programming with local variables ***)

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

/// lst_pre: preconditions are predicates on both the local variables
/// and the heap
let lst_pre (t:lvar_types) =
    local_variables t ->
    HS.mem ->
    Type0

/// lst_post: postconditions relate the initial state (locals , heap)
/// to the result and final state
let lst_post (t0 t1:lvar_types) (a:Type) =
    local_variables t0 ->
    HS.mem ->
    a ->
    local_variables t1 ->
    HS.mem ->
    Type0

/// `st_with_locals`: An effect layered on top of ST.  It explicitly
///  threads through a local variable map in addition to the state
let st_with_locals
      (a:Type)                  //result type
      (t0 t1:lvar_types)        //local var typing evolves from t0 to t1
      (pre:lst_pre t0)          //requires
      (post:lst_post t0 t1 a)   //ensures
  = l0:local_variables t0 ->
    ST.ST (a & local_variables t1)
     (requires fun h0 ->
       pre l0 h0)
     (ensures fun h0 (x, l1) h1 ->
       post l0 h0 x l1 h1)

/// create_var: There's no need to explicitly allocate a slot for a
/// variable `x`. At the first usage of `x` (e.g., var x := 10), we
/// just update the variable map at `x` with the type `a` of `x` and
/// its value
let create_var (#a:Type) (#t:lvar_types) (x:var_name) (v:a)
  : st_with_locals unit t (upd_t t x a)
    (requires fun _ _ -> True)
    (ensures fun l0 h0 _ l1 h1 ->
      l1 == strong_upd_map l0 x v /\
      h0 == h1)
  = fun l0 ->
    (), strong_upd_map l0 x v

/// set_var: To mutate a local variable, just call set_var
let set_var (#a:Type) (#t:lvar_types) (x:var_name) (v:t x)
  : st_with_locals unit t t
    (requires fun _ _ -> True)
    (ensures fun l0 h0 _ l1 h1 ->
      l1 == upd_map l0 x v /\
      h0 == h1)
  = fun l0 ->
    (), upd_map l0 x v

/// get_var: Reading a local variable `x`
let get_var (#a:Type) (#t:lvar_types) (x:var_name)
  : st_with_locals (t x) t t
    (requires fun _ _ -> True)
    (ensures fun l0 h0 v l1 h1 ->
      l1 == l0 /\
      h0 == h1 /\
      v == sel_map l0 x)
  = fun l0 ->
    sel_map l0 x, l0


/// run_st_with_locals:
///
///    This is the key rule that creates an runs a computation in a
///    new scope
///
///    Given a computation `f` that can be run with an empty local
///    variable set, we can turn it into a regular ST computation, by
///    just running it and returning its result, and discarding the
///    final state of the locals
///
///    This run_st is a kind of effect promotion rule that works by
///    reifying `f` to its `ST` representation and running it there.
///
///    Top-level computations should always have ST effect (or RST),
///    and should not expose any of their local state.
let run_st_with_locals (f:st_with_locals 'a unit_map 'l1 'pre 'post)
    : ST.ST 'a
      (requires fun h -> 'pre empty_map h)
      (requires fun h0 x h1 -> exists l1. 'post empty_map h0 x l1 h1)
    = fst (f empty_map)


