module Pulse.Lib.Effects.Core
#lang-pulse

(* All transformations below are total and preserve resource indices.
   Only execution of an embedded action or an operation implementation may
   diverge. Aborts have no continuation in which ownership could be stranded. *)

open Pulse.Lib.Core
open Pulse.Main

// Pulse bodies keep execution visible to extraction, unlike semantic stt rules.
fn return_value (#a:Type0) (x:a) (#q:a -> slprop)
  requires q x
  returns y:a
  ensures q y
{ x }

fn sequence (#a #b:Type0) (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  (next:(x:a -> stt b (q x) (fun y -> s y)))
  requires p
  returns y:b
  ensures s y
{
  let x = action ();
  next x
}

fn framed_action (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (f:slprop) (action:unit -> stt a p (fun x -> q x))
  requires p ** f
  returns x:a
  ensures q x ** f
{ action () }

divergent fn return_value_div (#a:Type0) (x:a) (#q:a -> slprop)
  requires q x
  returns y:a
  ensures q y
{ x }

divergent fn sequence_div (#a #b:Type0) (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (action:unit -> stt_div a p (fun x -> q x))
  (next:(x:a -> stt_div b (q x) (fun y -> s y)))
  requires p
  returns y:b
  ensures s y
{
  let x = action ();
  next x
}

divergent fn framed_action_div (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (f:slprop) (action:unit -> stt_div a p (fun x -> q x))
  requires p ** f
  returns x:a
  ensures q x ** f
{ action () }

divergent fn lift_action (#a:Type0) (#p:slprop) (#q:a -> slprop)
  (action:unit -> stt a p (fun x -> q x))
  requires p
  returns x:a
  ensures q x
{ action () }

let frame_comp #a g #p #q f =
  match g returns (comp g a p q -> comp g a (p ** f) (fun x -> q x ** f)) with
  | Terminating -> fun action -> framed_action f (fun () -> action)
  | MayDiverge -> fun action -> framed_action_div f (fun () -> action)

let lift_comp #a #g h #p #q =
  let up =
    match g returns
      (h:grade{below g h} -> comp g a p q -> comp h a p q) with
    | Terminating -> (fun h ->
        match h returns (comp Terminating a p q -> comp h a p q) with
        | Terminating -> fun action -> action
        | MayDiverge -> fun action -> lift_action (fun () -> action))
    | MayDiverge -> (fun h ->
        match h returns (comp MayDiverge a p q -> comp h a p q) with
        | MayDiverge -> fun action -> action)
  in
  up h

fn ghost_action (#p #q:slprop)
  (proof:unit -> stt_ghost unit emp_inames p (fun _ -> q))
  requires p
  ensures q
{ proof () }

let ghost_comp g #p #q proof = lift_comp g (ghost_action proof)

let rec weaken_grade #tag #ops #g #a #p #q h c =
  match c with
  | Return x -> Return x
  | Step action k -> Step (fun () -> lift_comp h (action ()))
      (fun x -> weaken_grade h (k x))
  | Perform op arg k -> Perform op arg (fun y -> weaken_grade h (k y))
  | Abort op arg -> Abort op arg

let lift #tag #ops #g #a #p #q action = Step action (fun x -> Return x)

inline_for_extraction
let rec bind_same (#tag:Type0) (#ops:signature tag) (#g:grade)
  (#a #b:Type0) (#p:slprop) (#q:a -> slprop) (#s:b -> slprop)
  (c:tree ops g a p q)
  ([@@@FStar.Attributes.monomorphize] next:(x:a -> tree ops g b (q x) s))
  : Tot (tree ops g b p s) (decreases c) =
  match c with
  | Return x -> next x
  | Step action k -> Step action (fun x -> bind_same (k x) next)
  | Perform op arg k -> Perform op arg (fun y -> bind_same (k y) next)
  | Abort op arg -> Abort op arg

let bind #tag #ops #g #h #a #b #p #q #s c next =
  bind_same (weaken_grade (join g h) c)
    (fun x -> weaken_grade (join g h) (next x))

inline_for_extraction
let reindex_pre (#tag:Type0) (#ops:signature tag) (#g:grade) (#a:Type0)
  (#p:slprop) (#q:a -> slprop) (p':slprop) (_:squash (p == p'))
  (c:tree ops g a p q) : tree ops g a p' q = c

let rec frame #tag #ops #g #a #p #q f c =
  match c with
  | Return x -> Return x
  | Step action k ->
      Step (fun () -> frame_comp g f (action ())) (fun x -> frame f (k x))
  | Perform #_ #_ #_ #_ #_ #r op arg k ->
      let next y =
        star_assoc (reply (ops op) arg y) r f;
        reindex_pre (reply (ops op) arg y ** (r ** f)) () (frame f (k y))
      in
      star_assoc (request (ops op) arg) r f;
      reindex_pre (p ** f) ()
        (Perform #_ #(frame_signature f ops) #g #a #(fun x -> q x ** f) #(r ** f) op arg next)
  | Abort op arg -> Abort #tag #(frame_signature f ops) op arg

let perform #tag #ops #g op arg =
  let next y =
    star_comm (reply (ops op) arg y) emp;
    emp_unit (reply (ops op) arg y);
    reindex_pre (reply (ops op) arg y ** emp) () (Return y)
  in
  star_comm (request (ops op) arg) emp;
  emp_unit (request (ops op) arg);
  reindex_pre (request (ops op) arg) ()
    (Perform #tag #ops #g #(output (ops op)) #(reply (ops op) arg) #emp op arg next)

let rec relabel #tag #other #ops #target #g #a #p #q embed c =
  match c with
  | Return x -> Return x
  | Step action k -> Step action (fun x -> relabel embed (k x))
  | Perform op arg k ->
      Perform #other #target (embed op) arg
        (fun y -> relabel #tag #other #ops #target embed (k y))
  | Abort op arg -> Abort #other #target (embed op) arg

let consequence #tag #ops #g #a #p #p' #q #q' before c after =
  Step (fun () -> ghost_comp g before)
    (fun _ -> bind_same c (fun x ->
      Step (fun () -> ghost_comp g (fun () -> after x)) (fun _ -> Return x)))

let rec run_terminating #tag #ops #a #p #q impl c =
  match c with
  | Return x -> return_value x
  | Step action k -> sequence action (fun x -> run_terminating impl (k x))
  | Perform #_ #_ #_ #_ #_ #r op arg k ->
      sequence (fun () -> framed_action r (fun () -> impl op arg))
        (fun y -> run_terminating impl (k y))
  | Abort op arg ->
      sequence (fun () -> impl op arg)
        (fun y -> let impossible:empty = y in match impossible with)

let rec run_divergent #tag #ops #a #p #q impl c =
  match c with
  | Return x -> return_value_div x
  | Step action k -> sequence_div action (fun x -> run_divergent impl (k x))
  | Perform #_ #_ #_ #_ #_ #r op arg k ->
      sequence_div (fun () -> framed_action_div r (fun () -> impl op arg))
        (fun y -> run_divergent impl (k y))
  | Abort op arg ->
      sequence_div (fun () -> impl op arg)
        (fun y -> let impossible:empty = y in match impossible with)

let run #tag #ops #g #h #a #p #q =
  let dispatch = match g returns
    (h:grade -> implementations ops h -> tree ops g a p q ->
      comp (join g h) a p q) with
  | Terminating -> (fun h ->
      match h returns
        (implementations ops h -> tree ops Terminating a p q ->
          comp (join Terminating h) a p q) with
      | Terminating -> fun impl c -> run_terminating impl c
      | MayDiverge -> fun impl c -> run_divergent impl (weaken_grade MayDiverge c))
  | MayDiverge -> (fun h ->
      match h returns
        (implementations ops h -> tree ops MayDiverge a p q ->
          comp (join MayDiverge h) a p q) with
      | Terminating -> fun impl c ->
          run_divergent (fun op arg -> lift_action (fun () -> impl op arg)) c
      | MayDiverge -> fun impl c -> run_divergent impl c)
  in dispatch h

let run_closed #ops #a #p #q c =
  run_terminating (fun op -> match op with) c

let run_closed_div #ops #g #a #p #q c =
  run_divergent (fun op -> match op with) (weaken_grade MayDiverge c)
