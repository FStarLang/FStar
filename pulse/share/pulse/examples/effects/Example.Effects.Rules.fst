module Example.Effects.Rules
#lang-pulse

open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module Rules = Pulse.Lib.Effects.Rules
module C = Example.Effects.Graded

let next_post (r:ref int) (b:bool) (x:int) =
  R.pts_to r 2 ** pure (b /\ x == 20)

fn next (r:ref int) (b:bool) (x:int)
  requires C.normal_post r b x
  returns v:Rules.outcome int int
  ensures Rules.exit_post (next_post r b) (C.exceptional_post r b) v
{
  unfold (C.normal_post r b x);
  r := 2;
  fold (next_post r b (x + 10));
  Rules.Normal (x + 10)
}

let reraised (r s:ref int) (b:bool) (e:int) =
  R.pts_to r 3 ** R.pts_to s 6 ** pure (not b /\ e == 8)

fn normal (r s:ref int) (b:bool) (x:int)
  requires next_post r b x ** R.pts_to s 5
  returns v:Rules.outcome int int
  ensures Rules.exit_post (fun x -> next_post r b x ** R.pts_to s 5) (reraised r s b) v
{ Rules.Normal x }

fn caught (r s:ref int) (b:bool) (e:int{e == 7})
  requires C.exceptional_post r b e ** R.pts_to s 5
  returns v:Rules.outcome int int
  ensures Rules.exit_post (fun x -> next_post r b x ** R.pts_to s 5) (reraised r s b) v
{
  unfold (C.exceptional_post r b e);
  r := 3;
  s := 6;
  fold (reraised r s b 8);
  Rules.Raised 8
}

ghost fn impossible_forward (r s:ref int) (b:bool) (e:int{not (e = 7)})
  requires C.exceptional_post r b e ** R.pts_to s 5
  ensures reraised r s b e
{
  unfold (C.exceptional_post r b e);
  assert pure False;
}

// The exceptional path skips next, transfers the frame to caught, and raises
// again with both cells updated. The normal path never executes caught.
let program (r s:ref int) (b:bool)
  : stt (Rules.outcome int int) (R.pts_to r 0 ** R.pts_to s 5)
      (fun v -> Rules.exit_post
        (fun x -> next_post r b x ** R.pts_to s 5) (reraised r s b) v) =
  Rules.handle (fun e -> e = 7)
    (fun () -> Rules.frame (R.pts_to s 5)
      (fun () -> Rules.bind (fun () -> C.raw_callback r b) (next r b)))
    (normal r s b) (caught r s b) (impossible_forward r s b)

fn bind_frame_reraise (b:bool)
  returns result:int & (int & int)
  ensures pure (result == ((if b then 20 else 8),
    ((if b then 2 else 3), (if b then 5 else 6))))
{
  let mut r = 0;
  let mut s = 5;
  let v = program r s b;
  match v {
    Rules.Normal x -> {
      unfold (next_post r b x);
      let rv = !r;
      let sv = !s;
      (x, (rv, sv))
    }
    Rules.Raised e -> {
      unfold (reraised r s b e);
      let rv = !r;
      let sv = !s;
      (e, (rv, sv))
    }
  }
}

fn local_body (r:ref int) (b:bool) (local:ref int)
  requires R.pts_to r 0 ** R.pts_to local 0
  returns v:Rules.outcome int int
  ensures Rules.exit_post
    (fun x -> C.normal_post r b x ** R.pts_to_uninit local)
    (fun e -> C.exceptional_post r b e ** R.pts_to_uninit local) v
{
  local := 42;
  let v = C.raw_callback r b;
  R.forget_init local;
  match v {
    Rules.Normal x -> { Rules.Normal x }
    Rules.Raised e -> { Rules.Raised e }
  }
}

let with_local (r:ref int) (b:bool)
  : stt (Rules.outcome int int) (R.pts_to r 0)
      (fun v -> Rules.exit_post (C.normal_post r b) (C.exceptional_post r b) v) =
  Rules.with_local 0 (local_body r b)

divergent fn rec divergent_callback (r:ref int) (loop b:bool)
  requires R.pts_to r 0
  returns v:Rules.outcome int int
  ensures Rules.exit_post (C.normal_post r b) (C.exceptional_post r b) v
{
  if loop { divergent_callback r loop b }
  else { C.raw_callback r b }
}

let divergent_program (r s:ref int) (loop b:bool)
  : stt_div (Rules.outcome int int) (R.pts_to r 0 ** R.pts_to s 5)
      (fun v -> Rules.exit_post
        (fun x -> next_post r b x ** R.pts_to s 5) (reraised r s b) v) =
  Rules.handle_div (fun e -> e = 7)
    (fun () -> Rules.frame_div (R.pts_to s 5)
      (fun () -> Rules.bind_div
        (fun () -> divergent_callback r loop b)
        (fun x -> lift_stt_div (next r b x))))
    (fun x -> lift_stt_div (normal r s b x))
    (fun e -> lift_stt_div (caught r s b e))
    (impossible_forward r s b)
