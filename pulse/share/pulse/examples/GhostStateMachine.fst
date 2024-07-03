(*
   Copyright 2023 Microsoft Research

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

module GhostStateMachine
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.SpinLock

module R = Pulse.Lib.Reference

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
val run_stt (#a:Type) (#post:a -> slprop) (f:stt a emp post) : a

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

let pure_handle_has_state (h:pure_handle_t) (s:pure_st_t) : slprop = pts_to h #0.5R s

let handle_has_state (h:handle_t) (s:st_t) : slprop = pts_to h s

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
  lk:lock }
let mk_locked_st h ph lk = {h; ph; lk;}

let lock_inv (h:handle_t) (ph:pure_handle_t) : v:slprop { is_slprop2 v } =
  exists* s ps. 
  handle_has_state h s **
  pure_handle_has_state ph ps **
  pure (states_correspond s ps)

assume
val some_payload : payload_t

// -------------------------------------------------------------------------- //

// TODO: init establishes the global state, so we cannot reference global state
// before this function. the next and close signatures reference the global state,
// so we can't include the API before the implementation of init
// val init () : stt locked_state_t emp (fun st -> pure_handle_has_state st.ph Init)

```pulse
fn init ()
  requires emp
  returns st:locked_state_t
  ensures pure_handle_has_state st.ph Init ** lock_alive st.lk #1.0R (lock_inv st.h st.ph)
{
  let ph = alloc Init;
  let h = alloc CInit;

  R.share2 #pure_st_t ph #Init;
  fold pure_handle_has_state ph Init;
  fold pure_handle_has_state ph Init;
  fold handle_has_state h CInit;

  fold (lock_inv h ph);
  let lk = new_lock (lock_inv h ph);

  let locked_st = mk_locked_st h ph lk;
  rewrite (pure_handle_has_state ph Init)
       as (pure_handle_has_state locked_st.ph Init);

  rewrite (lock_alive lk #1.0R (lock_inv h ph)) as
          (lock_alive locked_st.lk (lock_inv locked_st.h locked_st.ph));

  locked_st
}
```

let global_locked_state : locked_state_t = run_stt (init ())

```pulse
fn next ()
  requires pure_handle_has_state global_locked_state.ph Init **
           lock_alive global_locked_state.lk #1.0R (lock_inv global_locked_state.h global_locked_state.ph)
  ensures pure_handle_has_state global_locked_state.ph Next **
          lock_alive global_locked_state.lk #1.0R (lock_inv global_locked_state.h global_locked_state.ph)

{
  acquire global_locked_state.lk;
  unfold (lock_inv global_locked_state.h global_locked_state.ph);
  with s. assert (handle_has_state global_locked_state.h s);
  with ps. assert (
    pure_handle_has_state global_locked_state.ph Init **
    pure_handle_has_state global_locked_state.ph ps
  );
  unfold handle_has_state global_locked_state.h s;
  unfold pure_handle_has_state global_locked_state.ph Init;
  unfold pure_handle_has_state global_locked_state.ph ps;

  pts_to_injective_eq #pure_st_t #0.5R #0.5R #Init #ps global_locked_state.ph;
  rewrite (pts_to global_locked_state.ph #0.5R ps)
       as (pts_to global_locked_state.ph #0.5R Init);
  Pulse.Lib.Reference.gather2 #pure_st_t global_locked_state.ph #Init;

  let st = CNext some_payload;
  global_locked_state.h := st;
  global_locked_state.ph := Next;

  R.share2 #pure_st_t global_locked_state.ph #Next;
  fold pure_handle_has_state global_locked_state.ph Next;
  fold pure_handle_has_state global_locked_state.ph Next;
  fold handle_has_state global_locked_state.h st;

  fold (lock_inv global_locked_state.h global_locked_state.ph);
  release global_locked_state.lk;
}
```

```pulse
fn close ()
  requires pure_handle_has_state global_locked_state.ph Next **
           lock_alive global_locked_state.lk #1.0R (lock_inv global_locked_state.h global_locked_state.ph)
  ensures pure_handle_has_state global_locked_state.ph Final **
          lock_alive global_locked_state.lk #1.0R (lock_inv global_locked_state.h global_locked_state.ph)

{
  acquire global_locked_state.lk;
  unfold (lock_inv global_locked_state.h global_locked_state.ph);
  with s. assert (handle_has_state global_locked_state.h s);
  with ps. assert (
    pure_handle_has_state global_locked_state.ph Next **
    pure_handle_has_state global_locked_state.ph ps
  );
  unfold handle_has_state global_locked_state.h s;
  unfold pure_handle_has_state global_locked_state.ph Next;
  unfold pure_handle_has_state global_locked_state.ph ps;

  pts_to_injective_eq #pure_st_t #0.5R #0.5R #Next #ps global_locked_state.ph;
  rewrite (pts_to global_locked_state.ph #0.5R ps)
       as (pts_to global_locked_state.ph #0.5R Next);
  Pulse.Lib.Reference.gather2 #pure_st_t global_locked_state.ph #Next;

  let st = CFinal some_payload;
  global_locked_state.h := st;
  global_locked_state.ph := Final;

  R.share2 #pure_st_t global_locked_state.ph #Final;
  fold pure_handle_has_state global_locked_state.ph Final;
  fold pure_handle_has_state global_locked_state.ph Final;
  fold handle_has_state global_locked_state.h st;

  fold (lock_inv global_locked_state.h global_locked_state.ph);
  release global_locked_state.lk;
}
```
