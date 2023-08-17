module GhostState
open Pulse.Lib.Pervasives
open Pulse.Lib.Reference
open Pulse.Lib.SpinLock

assume
val run_stt (#a:Type) (#post:a -> vprop) (f:stt a emp post) : a

type st_t =
  | Init
  | Next
  | Final

// assume
// val payload_t : Type0

// noeq
// type concrete_st_t = 
//   | CInit 
//   | CNext : payload_t -> concrete_st_t
//   | CState2 : payload_t -> concrete_st_t

type handle_t = ref st_t

let handle_has_state (h:handle_t) (s:st_t) : vprop = pts_to h #half_perm s

type locked_handle_t = h:handle_t & lock (exists_ (fun s -> handle_has_state h s))

// -------------------------------------------------------------------------- //

[@@expect_failure]
```pulse
fn init' (_:unit)
  requires emp
  returns p:locked_handle_t
  ensures handle_has_state p._1 Init
{
  let h = alloc Init;
  share #st_t #emp_inames h #Init;
  fold handle_has_state h Init;
  fold handle_has_state h Init;
  let lk = new_lock (exists_ (fun s -> handle_has_state h s));
  let p = (| h, lk |);
  rewrite (handle_has_state h Init)
       as (handle_has_state p._1 Init);

  // FIXME: cannot prove 
  //   handle_has_state (Mkdtuple2?._1 x) Init 
  // in the context
  //   handle_has_state (Mkdtuple2?._1 p) Init

  p
}
```
let global_locked_handle : locked_handle_t = admit() // run_stt (init' ())

#set-options "--print_implicits"

[@@expect_failure]
```pulse
fn next' (_:unit)
  requires handle_has_state global_locked_handle._1 Init
  ensures handle_has_state global_locked_handle._1 Next
{
  acquire global_locked_handle._2;
  with s. assert (handle_has_state global_locked_handle._1 s);
  unfold handle_has_state global_locked_handle._1 Init;
  unfold handle_has_state global_locked_handle._1 s;

  // FIXME: cannot prove
  //   pts_to #st_t (Mkdtuple2?._1 #handle_t #(fun h -> lock (exists_ #st_t (fun s -> handle_has_state h s))) global_locked_handle) #half_perm Init
  // in the context
  //   pts_to #st_t (Mkdtuple2?._1 #handle_t #(fun h -> lock (exists_ #st_t (fun s -> pts_to #st_t h #half_perm s <: Prims.Tot vprop))) global_locked_handle) #half_perm Init
  // Issue: the unfold of
  //   handle_has_state global_locked_handle._1 s
  // unfolded too much, so now there is not syntactic equality 

  pts_to_injective_eq #st_t #half_perm #half_perm #Init #s global_locked_handle._1;
  rewrite (pts_to global_locked_handle._1 #half_perm s)
       as (pts_to global_locked_handle._1 #half_perm Init);
  gather #st_t #emp_inames global_locked_handle._1 #Init;
  global_locked_handle._1 := Next;
  share #st_t #emp_inames global_locked_handle._1 #Next;
  fold handle_has_state global_locked_handle._1 Next;
  release global_locked_handle._2;
}
```