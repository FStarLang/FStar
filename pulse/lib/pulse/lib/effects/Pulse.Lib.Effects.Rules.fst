module Pulse.Lib.Effects.Rules
#lang-pulse

(* The rules construct trees and execute the common interpreter. Scoped local
   allocation remains a Pulse primitive around interpretation of the body.
   There are no assumed control operators or discarded ownership tokens. *)

open Pulse.Lib.Core
open Pulse.Main
module R = Pulse.Lib.Reference
module E = Pulse.Lib.Effects.Core
module X = Pulse.Lib.Effects.Exception

let run_tree #exn #ops #r #a #p #q c = E.run_closed (observe c)

let run_tree_div #exn #ops #g #r #a #p #q c = E.run_closed_div (observe c)

let return_ #exn #a #q #r x =
  run_tree #exn #E.empty_ops #r (E.Return x)

let raise_ #exn #a #q #r e =
  run_tree #exn #E.empty_ops #r (X.throw e)

let bind #exn #a #b #p #q #s #r action next =
  run_tree #exn #E.empty_ops #r
    (E.bind (of_outcome action) (fun x -> of_outcome (fun () -> next x)))

let bind_div #exn #a #b #p #q #s #r action next =
  run_tree_div #exn #E.empty_ops #E.MayDiverge #r
    (E.bind (of_outcome action) (fun x -> of_outcome (fun () -> next x)))

let frame #exn #a #p #q #r f action =
  run_tree (X.frame f (of_outcome #E.empty #exn #E.empty_ops #r #E.Terminating action))

let frame_div #exn #a #p #q #r f action =
  run_tree_div (X.frame f (of_outcome #E.empty #exn #E.empty_ops #r #E.MayDiverge action))

let lift #exn #a #p #q action =
  run_tree #exn #E.empty_ops #no_exceptions (E.lift action)

let lift_div #exn #a #p #q action =
  run_tree_div #exn #E.empty_ops #E.MayDiverge #no_exceptions (E.lift action)

let consequence_tree (#exn #a:Type0) (g:E.grade) (#p #p':slprop)
  (#q #q':a -> slprop) (#r #r':exn -> slprop)
  (before:unit -> stt_ghost unit emp_inames p' (fun _ -> p))
  (normal:(x:a -> stt_ghost unit emp_inames (q x) (fun _ -> q' x)))
  (exceptional:(e:exn -> stt_ghost unit emp_inames (r e) (fun _ -> r' e)))
  (action:unit -> E.comp g (outcome exn a) p (fun v -> exit_post q r v))
  : X.prog E.empty_ops r' g a p' q' =
  let c : X.prog (X.extend E.empty_ops r') r g a p q = of_outcome action in
  E.Step (fun () -> E.ghost_comp g before) (fun _ ->
    X.handle #_ #_ #_ #_ #g #g c
      (fun x -> E.Step (fun () -> E.ghost_comp g (fun () -> normal x))
        (fun _ -> E.Return x))
      (fun e -> E.Step (fun () -> E.ghost_comp g (fun () -> exceptional e))
        (fun _ -> X.throw e)))

let consequence #exn #a #p #p' #q #q' #r #r' before normal exceptional action =
  run_tree (consequence_tree E.Terminating before normal exceptional action)

let consequence_div #exn #a #p #p' #q #q' #r #r' before normal exceptional action =
  run_tree_div (consequence_tree E.MayDiverge before normal exceptional action)

let handle_tree (#exn #a #b:Type0) (g:E.grade) (#p:slprop)
  (#q:a -> slprop) (#r:exn -> slprop)
  (#s:b -> slprop) (#outer:exn -> slprop)
  (matches:exn -> bool)
  (action:unit -> E.comp g (outcome exn a) p (fun v -> exit_post q r v))
  (normal:(x:a -> E.comp g (outcome exn b) (q x) (fun v -> exit_post s outer v)))
  (caught:(e:exn{matches e} -> E.comp g (outcome exn b) (r e) (fun v -> exit_post s outer v)))
  (forward:(e:exn{not (matches e)} ->
    stt_ghost unit emp_inames (r e) (fun _ -> outer e)))
  : X.prog E.empty_ops outer g b p s =
  let c : X.prog (X.extend E.empty_ops outer) r g a p q = of_outcome action in
  X.handle #_ #_ #_ #_ #g #g c
    (fun x -> of_outcome (fun () -> normal x))
    (fun e -> if matches e then of_outcome (fun () -> caught e)
      else E.Step (fun () -> E.ghost_comp g (fun () -> forward e))
        (fun _ -> X.throw e))

let handle #exn #a #b #p #q #r #s #outer matches action normal caught forward =
  run_tree (handle_tree E.Terminating matches action normal caught forward)

let handle_div #exn #a #b #p #q #r #s #outer matches action normal caught forward =
  run_tree_div (handle_tree E.MayDiverge matches action normal caught forward)

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
  let v = run_tree #exn #E.empty_ops (of_outcome (fun () -> body local));
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
  let v = run_tree_div #exn #E.empty_ops #E.MayDiverge (of_outcome (fun () -> body local));
  match v {
    Normal x -> { Normal x }
    Raised e -> { Raised e }
  }
}
