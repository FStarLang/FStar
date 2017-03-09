module FStar.Tactics

assume type binder
assume type term
assume type env

type typ     = term
type binders = list binder
type goal    = env * term
type goals   = list goal
type state   = goals  //active goals 
             * goals  //goals that have to be dispatched to SMT
noeq type formula = 
  | True_  : formula
  | False_ : formula  
  | Eq     : typ -> term -> term -> formula
  | And    : term -> term -> formula
  | Or     : term -> term -> formula
  | Not    : term -> formula
  | Implies: term -> term -> formula
  | Iff    : term -> term -> formula  
  | Forall : binders -> term -> formula
  | Exists : binders -> term -> formula

assume val term_as_formula: term -> option formula

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
reifiable reflectable new_effect_for_free {
  TAC : a:Type -> Effect
  with repr     = tac
     ; bind     = bind
     ; return   = ret
  and effect_actions
       get      = get
}

(* working around #885 *)
let fail_ (a:Type) (msg:string) : tac a = fun s0 -> Failed #a "No message for now" s0
let fail (#a:Type) (msg:string) = TAC?.reflect (fail_ a msg)

effect Tac (a:Type) = TAC a (fun i post -> forall j. post j)
let tactic = unit -> Tac unit

abstract 
let by_tactic (t:state -> result unit) (a:Type) : Type = a

let reify_tactic (t:tactic) : tac unit =
  fun s -> reify (t ()) s

let assert_by_tactic (t:tactic) (p:Type)
  : Pure unit 
         (requires (by_tactic (reify_tactic t) p))
         (ensures (fun _ -> p))
  = ()

assume val forall_intros_: unit -> tac binders
let forall_intros () : Tac binders = TAC?.reflect (forall_intros_ ())

assume val implies_intro_: unit -> tac binder
let implies_intro () : Tac binder = TAC?.reflect (implies_intro_ ())

assume val revert_  : unit -> tac unit
let revert () : Tac unit = TAC?.reflect (revert_ ())

assume val clear_   : unit -> tac unit
let clear () : Tac unit = TAC?.reflect (clear_ ())

assume val split_   : unit -> tac unit
let split () : Tac unit = TAC?.reflect (split_ ())

assume val merge_   : unit -> tac unit
let merge () : Tac unit = TAC?.reflect (merge_ ())

assume val rewrite_ : binder -> tac unit
let rewrite (b:binder) : Tac unit = TAC?.reflect (rewrite_ b)

assume val smt_     : unit -> tac unit
let smt () : Tac unit = TAC?.reflect (smt_ ())

assume val visit_   : tac unit -> tac unit
let visit (f:tactic) : Tac unit = TAC?.reflect (visit_ (reify_tactic f))

assume val focus_: tac unit -> tac unit
let focus (f:tactic) : Tac unit = TAC?.reflect (focus_ (reify_tactic f))


(* Primitives provided natively by the tactic engine *)
//assume val forall_intros: unit -> Tac binders
