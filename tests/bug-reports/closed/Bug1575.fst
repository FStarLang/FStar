module Bug1575

// A partially applied recursive function in an SMT pattern used to be encoded
// with the wrong number of arguments to its fuel-instrumented symbol.
assume val q : prop
assume Q : q

#push-options "--warn_error -328"
let rec existsL (p l:int) = True

// A nontrivial postcondition is important: Lemma True could hide the bug.
let lem (p:int) : Lemma q [SMTPat (existsL p)] = ()
#pop-options

// Exercise the same pattern with a function that actually recurses.
let rec contains (p:int) (l:list int) : prop =
  match l with
  | [] -> False
  | h :: tl -> h == p \/ contains p tl

let lem_rec (p:int) : Lemma q [SMTPat (contains p)] = ()

// The discussion also reported a partial application of a mutually recursive
// function inside a lemma's postcondition.
type variable = { v_name: string }
type term =
  | Var : v:variable -> term
  | Name : n:int -> term
  | Func : s:int -> l:list term -> term

val occurs: variable -> term -> bool
val occurs_list: variable -> list term -> bool
let rec occurs x t =
  match t with
  | Var v -> v = x
  | Name _ -> false
  | Func _ args -> occurs_list x args
and occurs_list x l =
  match l with
  | [] -> false
  | t :: tl -> occurs x t || occurs_list x tl

assume val spec_occurs_list_exists: x:variable -> l:list term -> Lemma
  (ensures (occurs_list x l <==> FStar.List.Tot.existsb (occurs x) l))
  [SMTPat (occurs_list x l)]

// Force a query so Z3 checks the generated declarations and patterns.
assume val phi : prop
assume Phi : phi
let _ = assert phi
