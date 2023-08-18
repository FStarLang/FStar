module GhostState
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.SpinLock

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

let pure_handle_has_state (h:pure_handle_t) (s:pure_st_t) : vprop = pts_to h #half_perm s

let handle_has_state (h:handle_t) (s:st_t) : vprop = pts_to h s

let states_correspond (s:st_t) (ps:pure_st_t) : prop
  = (CInit? s) /\ (Init? ps)
  \/(CNext? s) /\ (Next? ps)
  \/(CFinal? s) /\ (Final? ps)

type locked_state_t = h:handle_t 
                    & ph:pure_handle_t 
                    & lock (exists_ (fun s ->
                            exists_ (fun ps -> 
                                handle_has_state h s **
                                pure_handle_has_state ph ps **
                                pure (states_correspond s ps))))

// -------------------------------------------------------------------------- //

[@@expect_failure]
```pulse
fn init' (_:unit)
  requires emp
  returns tup:locked_state_t
  ensures pure_handle_has_state tup._2 Init
{
  let ph = alloc Init;
  let h = alloc CInit;

  share #pure_st_t #emp_inames ph #Init;
  fold pure_handle_has_state ph Init;
  fold pure_handle_has_state ph Init;
  fold handle_has_state h CInit;

  let lk = new_lock (exists_ (fun s ->
                     exists_ (fun ps -> 
                        handle_has_state h s **
                        pure_handle_has_state ph ps **
                        pure (states_correspond s ps))));

  let tup = (| h, ph, lk |);
  rewrite (pure_handle_has_state ph Init)
       as (pure_handle_has_state tup._2 Init);

  // FIXME: cannot prove 
  //   pure_handle_has_state (Mkdtuple3?._2 x) Init 
  // in the context
  //   pure_handle_has_state (Mkdtuple3?._2 p) Init
  // ISSUE: idk

  ph
}
```
let global_locked_state : locked_state_t = admit() // run_stt (init' ())

#set-options "--print_implicits"

assume
val some_payload : payload_t

[@@expect_failure]
```pulse
fn next' (_:unit)
  requires pure_handle_has_state global_locked_state._2 Init
  ensures pure_handle_has_state global_locked_state._2 Next
{
  acquire global_locked_state._3;
  with s. assert (handle_has_state global_locked_state._1 s);
  with ps. assert (pure_handle_has_state global_locked_state._2 ps);
  unfold handle_has_state global_locked_state._1 s;
  unfold pure_handle_has_state global_locked_state._2 Init;
  unfold pure_handle_has_state global_locked_state._2 ps;

  // ISSUE: the unfold of
  //   pure_handle_has_state global_locked_state._2 ps
  // unfolded too much, so now there is not syntactic equality 

  pts_to_injective_eq #pure_st_t #half_perm #half_perm #Init #ps global_locked_state._2;
  rewrite (pts_to global_locked_state._2 #half_perm ps)
       as (pts_to global_locked_state._2 #half_perm Init);
  gather #pure_st_t #emp_inames global_locked_state._2 #Init;

  let st = CNext some_payload;
  global_locked_state._1 := st;
  global_locked_state._2 := Next;

  share #pure_st_t #emp_inames global_locked_state._2 #Next;
  fold pure_handle_has_state global_locked_state._2 Next;
  fold pure_handle_has_state global_locked_state._2 Next;
  fold handle_has_state global_locked_state._2 st;
  assert (pure (states_correspond st Next));

  release global_locked_state._3;
}
```