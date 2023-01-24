module Part4.UTLCEx1

let var = nat
type term = 
  | Var  : var -> term
  | Int  : int -> term
  | Lam  : term -> term
  | App  : term -> term -> term

//SNIPPET_START: closed$
let rec closed' (t:term) (offset:int) 
  : bool
  = match t with
    | Int _ -> true
    | Var i -> i <= offset
    | Lam t -> closed' t (offset + 1)
    | App t0 t1 -> closed' t0 offset && closed' t1 offset
let closed t = closed' t (-1)
//SNIPPET_END: closed$

let rec closed'_weaken (t:term) (offset offset':int)
  : Lemma 
    (requires closed' t offset /\
              offset <= offset')
    (ensures closed' t offset')
  = match t with
    | Int _ -> ()
    | Var _ -> ()
    | Lam t -> closed'_weaken t (offset + 1) (offset' + 1)
    | App t0 t1 -> 
      closed'_weaken t0 offset offset';
      closed'_weaken t1 offset offset' 

let rec subst (x:var) 
              (v:term { closed v })
              (t:term { closed' t x })
  : Tot (t1:term { closed' t1 (x - 1) }) (decreases t) = 
  match t with
  | Var y -> if x = y then (closed'_weaken v (-1) (x - 1); v) else t
  | Int _ -> t
  | Lam t -> Lam (subst (x + 1) v t)
  | App t0 t1 -> App (subst x v t0) (subst x v t1)

//SNIPPET_START: interpret$
let rec interpret (t:term { closed t })
  : Dv (option (t:term { closed t }))
  = match t with
    | Var _
    | Int _
    | Lam _ -> Some t
    | App t0 t1 ->
      let head = interpret t0 in
      match head with
      | None -> None
      | Some (Lam body) -> interpret (subst 0 t1 body)
      | _ -> None //type error, expected a function
//SNIPPET_END: interpret$
