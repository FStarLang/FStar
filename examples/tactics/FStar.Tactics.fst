// This should be moved to the standard libary, e.g., FStar/ulib
module FStar.Tactics
assume type binder //FStar.Syntax.Syntax.binder
assume type term
assume type env
type typ     = term
type binders = list binder
type goal    = env * term
type goals   = list goal
type state   = goals  //active goals 
             * goals  //goals that have to be dispatched to SMT: maybe change this part of the state to be opaque to a user program

assume val binders_of_env : env -> binders
assume val type_of_binder: binder -> term 
assume val term_eq : term -> term -> bool
assume val quote   : #a:Type -> a -> term

(* This is meant to be all named representation
     -- while providing some conveniences for 
        handling the logical structure of a term 
   NB: rename this to term_view? or something like that
*)
noeq type formula = 
  //the logical skeleton of a term
  | True_  : formula
  | False_ : formula  
  | Eq     : typ -> term -> term -> formula
  | And    : term -> term -> formula  //Prims.l_and
  | Or     : term -> term -> formula
  | Not    : term -> formula
  | Implies: term -> term -> formula
  | Iff    : term -> term -> formula  
  | Forall : binders -> term -> formula
  | Exists : binders -> term -> formula
  | App    : term -> term -> formula
  | Name   : binder -> formula
   (* TODO more cases *) 
  //Abs   : binders -> term -> formula //Named repr
  //Match : ....

//This primitive provides a way to destruct a term as a formula
assume val term_as_formula: term -> option formula
//TODO: We should add a formula_as_term also

noeq type result (a:Type) =
  | Success: a -> state -> result a
  | Failed: string -> state -> result a

let tac (a:Type) = state -> M (result a)

(* monadic return *)
val ret : a:Type -> x:a -> tac a
let ret a x = fun (s:state) -> Success x s

(* monadic bind *)
let bind (a:Type) (b:Type) 
         (t1:tac a)
         (t2:a -> tac b)
    : tac b
    = fun p ->
        let r = t1 p in
        match r with
        | Success a q  -> t2 a q
        | Failed msg q -> Failed msg q

(* Actions *)
let get () : tac state = fun s0 -> Success s0 s0 


(* total  *) //disable the termination check, although it remains reifiable
reifiable reflectable new_effect {
  TAC : a:Type -> Effect
  with repr     = tac
     ; bind     = bind
     ; return   = ret
     ; get      = get
}
effect Tac (a:Type) = TAC a (fun i post -> forall j. post j)
let tactic (a:Type) = unit -> Tac a

(* working around #885 *)
let fail_ (a:Type) (msg:string) : tac a = fun s0 -> Failed #a msg s0
let fail (#a:Type) (msg:string) = TAC?.reflect (fail_ a msg)

let or_else (#a:Type) (t1:tactic a) (t2:tactic a)
        : Tac a
        = TAC?.reflect (fun p -> 
            match reify (t1 ()) p with
            | Failed _ _ -> 
              reify (t2 ()) p
              | q -> q)

abstract 
let by_tactic (t:state -> result unit) (a:Type) : Type = a

let reify_tactic (t:tactic unit) : tac unit =
  fun s -> reify (t ()) s

let assert_by_tactic (t:tactic unit) (p:Type)
  : Pure unit 
         (requires (by_tactic (reify_tactic t) p))
         (ensures (fun _ -> p))
  = ()

(* Many of these could be derived from apply_lemma, 
   rather than being assumed as primitives. 
   E.g., forall_intros could be an application of 
         FStar.Classical.forall_intro
 *)         
assume val forall_intros_: tac binders
let forall_intros () : Tac binders = TAC?.reflect forall_intros_

assume val implies_intro_: tac binder
let implies_intro () : Tac binder = TAC?.reflect implies_intro_

assume val trivial_  : tac unit
let trivial () : Tac unit = TAC?.reflect trivial_

assume val revert_  : tac unit
let revert () : Tac unit = TAC?.reflect revert_

assume val clear_   : tac unit
let clear () : Tac unit = TAC?.reflect clear_

assume val split_   : tac unit
let split () : Tac unit = TAC?.reflect split_

assume val merge_   : tac unit
let merge () : Tac unit = TAC?.reflect merge_

assume val rewrite_ : binder -> tac unit
let rewrite (b:binder) : Tac unit = TAC?.reflect (rewrite_ b)

assume val smt_     : tac unit
let smt () : Tac unit = TAC?.reflect smt_

assume val visit_   : tac unit -> tac unit
let visit (f:tactic unit) : Tac unit = TAC?.reflect (visit_ (reify_tactic f))

assume val focus_: tac unit -> tac unit
let focus (f:tactic unit) : Tac unit = TAC?.reflect (focus_ (reify_tactic f))

(* could be implemented using focus_ *)
assume val seq_ : tac unit -> tac unit -> tac unit
let seq (f:tactic unit) (g:tactic unit) : tactic unit = fun () -> 
  TAC?.reflect (seq_ (reify_tactic f) (reify_tactic g))

assume val exact_ : term -> tac unit
let exact (t:term) : Tac unit = TAC?.reflect (exact_ t)

assume val apply_lemma_ : term -> tac unit
let apply_lemma (t:term) : Tac unit = TAC?.reflect (apply_lemma_ t)

assume val print_ : string -> tac unit
let print (msg:string) : Tac unit = TAC?.reflect (print_ msg)

abstract let embed (#a:Type0) (x:a) : Tot a = a
