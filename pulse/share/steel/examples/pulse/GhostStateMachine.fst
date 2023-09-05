module GhostStateMachine
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.SpinLock

(*  
  A small example of a ghost state machine (although this implementation
  does not actually use ghost references) that corresponds to a concrete
  state machine. This is useful when we a client wants assurance that a 
  state update occurred but they should not know anything more about the 
  concrete state. To accomplish this, the client gets partial permission on 
  a ghost state machine that models the concrete state. They must provide 
  their knowledge of the ghost state machine in order to update the concrete
  state, and they get back assurance that the state machines advanced to the
  next state. 

  In this example, there is a single global reference to the concrete state
  and a single global reference to the pure state (called the handles). In DPE, 
  the handles should change with each advancement of the state. This requires
  a hash table for dynamically creating and destroying handles in the global state. 
*)

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

type pure_st_t =
  | Init
  | Next
  | Final

assume
val payload_t : Type0

noeq
type st_t = 
  | CInit
  | CNext : payload_t -> st_t
  | CFinal : payload_t -> st_t

type pure_handle_t = ref pure_st_t

type handle_t = ref st_t

let pure_handle_has_state (h:pure_handle_t) (s:pure_st_t) : vprop = pts_to h #one_half s

let handle_has_state (h:handle_t) (s:st_t) : vprop = pts_to h s

let states_correspond (s:st_t) (ps:pure_st_t) : prop
  = (CInit? s) /\ (Init? ps)
  \/(CNext? s) /\ (Next? ps)
  \/(CFinal? s) /\ (Final? ps)

// TODO: concrete and pure handles should not exist in the same record, because
// the client should not have access to the concrete handle
noeq
type locked_state_t = 
{ h:handle_t; 
  ph:pure_handle_t; 
  lk:lock (exists_ (fun s ->
      exists_ (fun ps -> 
          handle_has_state h s **
          pure_handle_has_state ph ps **
          pure (states_correspond s ps))));}
let mk_locked_st h ph lk = {h; ph; lk;}

assume
val some_payload : payload_t

// -------------------------------------------------------------------------- //

// TODO: init establishes the global state, so we cannot reference global state
// before this function. the next and close signatures reference the global state,
// so we can't include the API before the implementation of init
val init (_:unit) : stt locked_state_t emp (fun st -> pure_handle_has_state st.ph Init)

```pulse
fn init' (_:unit)
  requires emp
  returns st:locked_state_t
  ensures pure_handle_has_state st.ph Init
{
  let ph = alloc Init;
  let h = alloc CInit;

  share2 #pure_st_t #emp_inames ph #Init;
  fold pure_handle_has_state ph Init;
  fold pure_handle_has_state ph Init;
  fold handle_has_state h CInit;

  let lk = new_lock (exists_ (fun s ->
                     exists_ (fun ps -> 
                        handle_has_state h s **
                        pure_handle_has_state ph ps **
                        pure (states_correspond s ps))));

  let locked_st = mk_locked_st h ph lk;
  rewrite (pure_handle_has_state ph Init)
       as (pure_handle_has_state locked_st.ph Init);

  locked_st
}
```
let init = init'

let global_locked_state : locked_state_t = run_stt (init' ())

val next (_:unit) : stt unit (pure_handle_has_state global_locked_state.ph Init) (fun st -> pure_handle_has_state global_locked_state.ph Next)

```pulse
fn next' (_:unit)
  requires pure_handle_has_state global_locked_state.ph Init
  ensures pure_handle_has_state global_locked_state.ph Next
{
  acquire global_locked_state.lk;
  with s. assert (handle_has_state global_locked_state.h s);
  with ps. assert (pure_handle_has_state global_locked_state.ph ps);
  unfold handle_has_state global_locked_state.h s;
  unfold pure_handle_has_state global_locked_state.ph Init;
  unfold pure_handle_has_state global_locked_state.ph ps;

  pts_to_injective_eq #pure_st_t #one_half #one_half #Init #ps global_locked_state.ph;
  rewrite (pts_to global_locked_state.ph #one_half ps)
       as (pts_to global_locked_state.ph #one_half Init);
  gather2 #pure_st_t #emp_inames global_locked_state.ph #Init;

  let st = CNext some_payload;
  global_locked_state.h := st;
  global_locked_state.ph := Next;

  share2 #pure_st_t #emp_inames global_locked_state.ph #Next;
  fold pure_handle_has_state global_locked_state.ph Next;
  fold pure_handle_has_state global_locked_state.ph Next;
  fold handle_has_state global_locked_state.h st;

  release global_locked_state.lk;
}
```
let next = next'

val close (_:unit) : stt unit (pure_handle_has_state global_locked_state.ph Next) (fun st -> pure_handle_has_state global_locked_state.ph Final)

```pulse
fn close' (_:unit)
  requires pure_handle_has_state global_locked_state.ph Next
  ensures pure_handle_has_state global_locked_state.ph Final
{
  acquire global_locked_state.lk;
  with s. assert (handle_has_state global_locked_state.h s);
  with ps. assert (pure_handle_has_state global_locked_state.ph ps);
  unfold handle_has_state global_locked_state.h s;
  unfold pure_handle_has_state global_locked_state.ph Next;
  unfold pure_handle_has_state global_locked_state.ph ps;

  pts_to_injective_eq #pure_st_t #one_half #one_half #Next #ps global_locked_state.ph;
  rewrite (pts_to global_locked_state.ph #one_half ps)
       as (pts_to global_locked_state.ph #one_half Next);
  gather2 #pure_st_t #emp_inames global_locked_state.ph #Next;

  let st = CFinal some_payload;
  global_locked_state.h := st;
  global_locked_state.ph := Final;

  share2 #pure_st_t #emp_inames global_locked_state.ph #Final;
  fold pure_handle_has_state global_locked_state.ph Final;
  fold pure_handle_has_state global_locked_state.ph Final;
  fold handle_has_state global_locked_state.h st;

  release global_locked_state.lk;
}
```
let close = close'
