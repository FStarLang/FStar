module MetaCoq

open FStar.Exn
open FStar.All

(*
The Next 700 Safe Tactic Languages.
B. Ziliani, Y. Régis-Gianas, J.-O. Kaiser.
https://www.mpi-sws.org/~beta/papers/metacoq-paper.pdf
https://github.com/MetaCoq/MetaCoq/
*)

noeq type goal : Type =
| Goal : #a:Type -> a -> goal
| AHyp : #a:Type -> option a -> (a -> Tot goal) -> goal

let tactic : Type = goal -> ML (list goal)

let idtac : tactic = fun g -> [g]

let fail (e : exn) : tactic = fun g -> raise e

let ttry (t : tactic) : tactic = fun g ->
  try t g with | _ -> [g]

let or (t :tactic) (u : tactic) : tactic = fun g ->
  try t g with _ -> u g

(* exception NotCumul of (a:Type & (a * a))
-- universe problem, exceptions have to be in Type0 currently (#737) *)

exception NotCumul

exception NotAGoal

type unification = | UniCoq (* MetaCoq has more *)

assume val munify_cumul : #a:Type -> a -> #b:Type -> b -> unification -> ML bool

let exact (#a:Type) (x : a) : tactic = fun g ->
  match g with
  | Goal e ->
    let b = munify_cumul x e UniCoq in
    if b then [] else raise NotCumul (* NotCumul x e *)
  | _ -> raise NotAGoal

assume val goal_type : goal -> ML Type

assume val evar : a:Type -> ML a

assume val is_evar : #a:Type -> a -> ML bool

exception CantApply

type dyn = t:Type & t

let apply (#t:Type) (c : t) : tactic = fun g ->
  let rec app (d : dyn) : ML (list goal) =
    let (| _, el |) = d in
    try exact el g
    with _ ->
      (*m*)match d with
      | _ -> (* [? t1 t2 f] (| x:t1 -> Tot (t2 x), f |) *)
          let t1 : Type = magic() in
          let t2 : t1 -> Type = magic() in
          let f : x:t1 -> Tot (t2 x) = magic() in
          let e = evar t1 in
          let r = app (| _, f e |) in
          if is_evar e then Goal e :: r
          else r
      | _ ->
          raise CantApply (* CantApply c gT *)
  in app (| t, c |)

let cut u : tactic = fun g ->
  let t = goal_type g in
  let ut = evar (u -> Tot t) in
  let u = evar u in
  ignore u#1 (exact (ut u) g);
  [Goal ut; Goal u]

let select (t:Type) (f : t -> tactic) : tactic = fun g ->
  admit()
  // let g = goal_type u#0 g in
  (* match_goal ([| (x : T) |- G |] => f x) g *)
