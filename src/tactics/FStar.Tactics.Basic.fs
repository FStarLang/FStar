#light "off"
module FStar.Tactics.Basic
open FStar.All
open FStar.Syntax.Syntax

module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module Env = FStar.TypeChecker.Env
module U = FStar.Syntax.Util
module Rel = FStar.TypeChecker.Rel

type name = bv

type goal = {
    context :Env.env;
    witness :term;
    goal_typ:term
}

type proofstate = {
    current_goal:goal;
    other_goals:list<goal>
}

type tac<'a> = proofstate -> option<('a * proofstate)>

let ret (a:'a)
    : tac<'a>
    = fun p -> Some (a, p)

let bind (t1:tac<'a>) (t2:'a -> tac<'b>)
    : tac<'b>
    = fun p ->
        match t1 p with
        | None -> None
        | Some (a, q) -> t2 a q

let or_else (t1:tac<'a>) (t2:tac<'a>)
    : tac<'a>
    = fun p ->
        match t1 p with
        | None -> t2 p
        | q -> q
(* Initial experiments with some basic trusted (kernel-level) tactics *)

let intros : tac<(list<name>)>
   = fun p ->
     match U.destruct_typ_as_formula p.current_goal.goal_typ with
     | Some (U.QAll(bs, pats, body)) ->
      //TODO!
      //ignoring the qualifiers on bs and the pats for now
      //need to restore that!
      let names = List.map fst bs in
      let p = {context = Env.push_binders p.context bs;
               goal=body} in
      Some (names, p)
     | _ -> None

let split : tac<unit>
    = fun p ->


let exact (x:name)
    : tac<unit>
    = fun p ->
        try let t = Env.lookup_bv p.context x in
            if Rel.teq_nosmt p.context t p.goal
            then Some ((), {p with goal=U.t_true})
            else None
        with _ -> None

let rewrite (x:name) (e:term) : tac<unit>
    = fun p ->
      let q = {p with goal=SS.subst [NT(x, e)] p.goal} in
      Some ((), q)



