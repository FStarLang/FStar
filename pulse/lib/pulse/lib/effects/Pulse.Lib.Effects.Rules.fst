module Pulse.Lib.Effects.Rules
#lang-pulse

(* These implementations derive the two-exit rules solely from existing Pulse
   sequencing, matching, framing, ghost consequence, and scoped allocation.
   There are no assumed control operators or discarded ownership tokens. *)

open Pulse.Lib.Core
open Pulse.Main
module R = Pulse.Lib.Reference

fn return_ (#exn #a:Type0) (#q:a -> slprop) (#r:exn -> slprop) (x:a)
  requires q x
  returns v:outcome exn a
  ensures exit_post q r v
{ Normal x }

fn raise_ (#exn #a:Type0) (#q:a -> slprop) (#r:exn -> slprop) (e:exn)
  requires r e
  returns v:outcome exn a
  ensures exit_post q r v
{ Raised e }

fn bind (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#s:b -> slprop) (#r:exn -> slprop)
  (action:unit -> stt (outcome exn a) p (fun v -> exit_post q r v))
  (next:(x:a -> stt (outcome exn b) (q x) (fun v -> exit_post s r v)))
  requires p
  returns v:outcome exn b
  ensures exit_post s r v
{
  let v = action ();
  match v {
    Normal x -> { next x }
    Raised e -> { Raised e }
  }
}

divergent fn bind_div (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#s:b -> slprop) (#r:exn -> slprop)
  (action:unit -> stt_div (outcome exn a) p (fun v -> exit_post q r v))
  (next:(x:a -> stt_div (outcome exn b) (q x) (fun v -> exit_post s r v)))
  requires p
  returns v:outcome exn b
  ensures exit_post s r v
{
  let v = action ();
  match v {
    Normal x -> { next x }
    Raised e -> { Raised e }
  }
}

fn frame (#exn #a:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (f:slprop)
  (action:unit -> stt (outcome exn a) p (fun v -> exit_post q r v))
  requires p ** f
  returns v:outcome exn a
  ensures exit_post (fun x -> q x ** f) (fun e -> r e ** f) v
{
  let v = action ();
  match v {
    Normal x -> { Normal x }
    Raised e -> { Raised e }
  }
}

divergent fn frame_div (#exn #a:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (f:slprop)
  (action:unit -> stt_div (outcome exn a) p (fun v -> exit_post q r v))
  requires p ** f
  returns v:outcome exn a
  ensures exit_post (fun x -> q x ** f) (fun e -> r e ** f) v
{
  let v = action ();
  match v {
    Normal x -> { Normal x }
    Raised e -> { Raised e }
  }
}

fn lift (#exn #a:Type0) (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  requires p
  returns v:outcome exn a
  ensures exit_post q no_exceptions v
{
  let x = action ();
  Normal x
}

divergent fn lift_div (#exn #a:Type0) (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt_div a p (fun x -> q x))
  requires p
  returns v:outcome exn a
  ensures exit_post q no_exceptions v
{
  let x = action ();
  Normal x
}

fn consequence (#exn #a:Type0) (#p #p':slprop)
  (#q #q':a -> slprop) (#r #r':exn -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (normal:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  (exceptional:(e:exn -> stt_ghost unit emp_inames (r e) (fun _ -> r' e)))
  (action:unit -> stt (outcome exn a) p (fun v -> exit_post q r v))
  requires p'
  returns v:outcome exn a
  ensures exit_post q' r' v
{
  before ();
  let v = action ();
  match v {
    Normal x -> { normal x; Normal x }
    Raised e -> { exceptional e; Raised e }
  }
}

divergent fn consequence_div (#exn #a:Type0) (#p #p':slprop)
  (#q #q':a -> slprop) (#r #r':exn -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (normal:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  (exceptional:(e:exn -> stt_ghost unit emp_inames (r e) (fun _ -> r' e)))
  (action:unit -> stt_div (outcome exn a) p (fun v -> exit_post q r v))
  requires p'
  returns v:outcome exn a
  ensures exit_post q' r' v
{
  before ();
  let v = action ();
  match v {
    Normal x -> { normal x; Normal x }
    Raised e -> { exceptional e; Raised e }
  }
}

fn handle (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop)
  (#s:b -> slprop) (#outer:exn -> slprop)
  (matches:exn -> bool)
  (action:unit -> stt (outcome exn a) p (fun v -> exit_post q r v))
  (normal:(x:a -> stt (outcome exn b) (q x) (fun v -> exit_post s outer v)))
  (caught:(e:exn{matches e} -> stt (outcome exn b) (r e) (fun v -> exit_post s outer v)))
  (forward:(e:exn{not (matches e)} ->
    stt_ghost unit emp_inames (r e) (fun _ -> outer e)))
  requires p
  returns v:outcome exn b
  ensures exit_post s outer v
{
  let v = action ();
  match v {
    Normal x -> { normal x }
    Raised e -> {
      if (matches e) { caught e }
      else { forward e; Raised e }
    }
  }
}

divergent fn handle_div (#exn #a #b:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop)
  (#s:b -> slprop) (#outer:exn -> slprop)
  (matches:exn -> bool)
  (action:unit -> stt_div (outcome exn a) p (fun v -> exit_post q r v))
  (normal:(x:a -> stt_div (outcome exn b) (q x) (fun v -> exit_post s outer v)))
  (caught:(e:exn{matches e} -> stt_div (outcome exn b) (r e) (fun v -> exit_post s outer v)))
  (forward:(e:exn{not (matches e)} ->
    stt_ghost unit emp_inames (r e) (fun _ -> outer e)))
  requires p
  returns v:outcome exn b
  ensures exit_post s outer v
{
  let v = action ();
  match v {
    Normal x -> { normal x }
    Raised e -> {
      if (matches e) { caught e }
      else { forward e; Raised e }
    }
  }
}

fn with_local (#exn #a #t:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (init:t)
  (body:(local:R.ref t ->
    stt (outcome exn a) (p ** R.pts_to local init)
      (fun v -> exit_post
        (fun x -> q x ** R.pts_to_uninit local)
        (fun e -> r e ** R.pts_to_uninit local) v)))
  requires p
  returns v:outcome exn a
  ensures exit_post q r v
{
  let mut local = init;
  let v = body local;
  match v {
    Normal x -> { Normal x }
    Raised e -> { Raised e }
  }
}

divergent fn with_local_div (#exn #a #t:Type0) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop) (init:t)
  (body:(local:R.ref t ->
    stt_div (outcome exn a) (p ** R.pts_to local init)
      (fun v -> exit_post
        (fun x -> q x ** R.pts_to_uninit local)
        (fun e -> r e ** R.pts_to_uninit local) v)))
  requires p
  returns v:outcome exn a
  ensures exit_post q r v
{
  let mut local = init;
  let v = body local;
  match v {
    Normal x -> { Normal x }
    Raised e -> { Raised e }
  }
}
