module Part4.UTLCEx2
let var = nat
type term = 
  | Var  : var -> term
  | Int  : int -> term
  | Lam  : term -> term
  | App  : term -> term -> term

//SNIPPET_START: free$
let max (x y:int) : int = if x < y then y else x
let rec free (t:term)
  : int
  = match t with
    | Var x -> x
    | Int _ -> -1
    | Lam t -> free t - 1
    | App t0 t1 -> max (free t0) (free t1)
//SNIPPET_END: free$

noeq
type dyn = 
  | DErr  : string -> dyn
  | DInt  : int -> dyn
  | DFun  : (dyn -> Dv dyn) -> dyn

//SNIPPET_START: ctx_t$
let ctx_t (i:int) = x:nat{x <= i} -> dyn
//SNIPPET_END: ctx_t$

let shift #i (ctx:ctx_t i) (v:dyn) 
  : ctx_t (i + 1)
  = fun n -> if n = 0 then v else ctx (n - 1)

(* This is similar to the interpreter, but
   "interprets" terms into the F* type dyn
    rather than just reducing syntax to syntax *)
let rec denote (t:term)
               (ctx:ctx_t (free t))
  : Dv dyn 
  = match t with
    | Var v -> ctx v
    | Int i -> DInt i
    | Lam t -> DFun (fun v -> denote t (shift ctx v))
    | App t0 t1 -> 
      match denote t0 ctx with
      | DFun f -> f (denote t1 ctx)
      | DErr msg -> DErr msg
      | DInt _ -> DErr "Cannot apply an integer"

//SNIPPET_START: empty_context$
let empty_context : ctx_t (-1) = fun _ -> false_elim ()
//SNIPPET_END: empty_context$

let closed t = free t = -1
let denote_closed (t:term { closed t }) 
  : Dv dyn
  = denote t empty_context
