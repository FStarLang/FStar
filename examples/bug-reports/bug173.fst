module Bug173

(* binary operators *)
type binop =
| Plus
| Minus
| Times
| Lt
| Gt
| Eq
| Or
| And

(* identifiers for variables *)
type id = nat

(* values (just constants) *)
type value =
| VBool : bool -> value
| VInt  : int  -> value

(* arithmetic expressions *)
type exp =
| Val : value -> exp
| Var : id -> exp
| If  : condition:exp -> then_branch:exp -> else_branch:exp -> exp
| Op  : binop -> exp -> exp -> exp

(* statements *)
type stmt =
| Skip   : stmt
| Assign : var:id -> term:exp -> stmt
| Seq    : first:stmt -> second:stmt -> stmt
| Cond   : cond:exp -> then_branch:stmt -> else_branch:stmt -> stmt
| While  : cond:exp -> body:stmt -> stmt

(* types *)
type typ =
| TInt  : typ
| TBool : typ

(* heaps *)
type heap = id -> Tot value

(* updating the heap *)
val update : heap -> id -> value -> Tot heap
let update h x v = fun y -> if y = x then v else h y

(* small step evaluation functino for expressions *)
val step_exp : h:heap -> exp -> Tot (option exp)
let rec step_exp h e = match e with
| Var x -> Some (Val (h x))
| If c tb eb -> (match c with
  | Val (VBool true) -> Some tb
  | Val (VBool false) -> Some eb
  | Val _ -> None
  | _ -> (match step_exp h c with
    | Some c' -> Some (If c' tb eb)
    | None -> None))
| Op op op1 op2 -> (match (op1, op2) with
  | (Val x, Val y) -> (match (x,y) with
    | (VInt i1, VInt i2) -> (match op with
      | Plus -> Some (Val (VInt (i1 + i2)))
      | Minus -> Some (Val (VInt (i1 - i2)))
      | Times -> Some (Val (VInt (op_Multiply i1 i2)))
      | Gt -> Some (Val (if (i1 > i2) then VBool true else VBool false))
      | Lt -> Some (Val (if (i1 < i2) then VBool true else VBool false))
      | Eq -> Some (Val (if (i1 = i2) then VBool true else VBool false))
      | _ -> None)
    | (VInt _, _)
    | (_, VInt _) -> None
    | _ -> (match op with
      | Or -> (match (x,y) with
        | (VBool false, VBool false) -> Some (Val (VBool false))
        | _ -> Some (Val (VBool true)))
      | And -> (match (x,y) with
        | (VBool true, VBool true) -> Some (Val (VBool true))
        | _ -> Some (Val (VBool false)))
      | _ -> None))
  | (Val _, _) -> (match step_exp h op2 with
    | Some op2' -> Some (Op op op1 op2')
    | None -> None)
  | _ -> (match step_exp h op1 with
    | Some op1' -> Some (Op op op1' op2)
    | None -> None))
| _ -> None

(* small step evaluation function for statements *)
val step : heap -> stmt -> Tot (option (heap * stmt))
let rec step h s = match s with
| Skip -> None
| Assign x t -> (match t with
  | Val v -> Some (update h x v, Skip)
  | e -> (match step_exp h e with
    | Some e' -> Some (h, Assign x e')
    | None -> None))
| Seq s1 s2 -> if Skip? s1 then Some (h, s2) else
  (match step h s1 with
  | Some (h', s') -> Some (h', Seq s' s2)
  | None -> None)
| Cond ec st se -> (match ec with
  | Val (VBool true) -> Some (h, st)
  | Val (VBool false) -> Some (h, se)
  | Val _ -> None
  | _ -> (match step_exp h ec with
    | Some e -> Some (h, Cond e st se)
    | None -> None))
| While ec sb  -> (match ec with
  | Val (VBool true) ->  Some  (h, Seq sb s)
  | Val (VBool false) -> Some (h, Skip)
  | Val _ -> None
  | _ -> (match step_exp h ec with
    | Some e -> Some (h, While e sb)
    | None -> None))


(* mapping from operators to (input_type1 * input_type2 * output_type) *)
val op_type : binop -> Tot (typ * typ * typ)
let op_type op = match op with
| Plus
| Minus
| Times -> (TInt , TInt , TInt )
| Lt
| Gt
| Eq    -> (TInt , TInt , TBool)
| Or
| And   -> (TBool, TBool, TBool)

(* Typing constants *)
val typing_val : value -> Tot typ
let typing_val v =
  match v with
  | VInt  _ -> TInt
  | VBool _ -> TBool

(* Type environments *)
type env  = id -> Tot typ

(* Type checker for arithmetic expressions *)
val typing_exp : env ->  exp -> Tot (option typ)
let rec typing_exp g e = match e with
| Val v -> Some (typing_val v)
| Var x -> Some (g x)
| If c t e -> (match typing_exp g c, typing_exp g t, typing_exp g e with
  | Some TBool, Some t1, Some t2 -> if t1 = t2 then Some t1 else None
  | _ -> None)
| Op op op1 op2 -> (match op_type op, typing_exp g op1, typing_exp g op2 with
  | (t1, t2, tr), Some t1', Some t2' -> if t1 = t1' && t2 = t2'
                                        then Some tr else None
  | _ -> None)

(* Type-checker for stmts *)
val typing : env -> stmt -> Tot bool
let rec typing g s = match s with
| Skip -> true
| Assign x t -> (match typing_exp g t with
  | Some ty -> g x = ty
  | None -> false)
| Seq s1 s2 -> typing g s1 && typing g s2
| Cond c t e -> (match typing_exp g c, typing g t, typing g e with
  | Some TBool, true, true-> true
  | _ -> false)
| While c b -> (match typing_exp g c, typing g b with
  | Some TBool, true -> true
  | _ -> false)

(* ensures that type and value environment match *)
type typed_heap (g : env) (h : heap) = (forall x. typing_val (h x) = g x)

(* progress for well-typed expressions *)
val progress_exp : g:env -> h:heap{typed_heap g h} ->
                   e:exp{Some? (typing_exp g e)} -> Lemma
                   (Val? e \/ Some? (step_exp h e))
let rec progress_exp g h e = match e with
| Val _ -> ()
| Var _ -> ()
| If c tb eb -> progress_exp g h c
| Op op op1 op2 -> progress_exp g h op1; progress_exp g h op2


(* progress for well typed statements *)
val progress : g : env -> h : heap {typed_heap g h} -> s : stmt{typing g s} ->
               Lemma (Skip? s \/ Some? (step h s))
let rec progress g h s = match s with
| Skip -> ()
| Assign x t -> if not (Val? t) then progress_exp g h t
| Seq s1 s2 -> if not (Skip? s1) then progress g h s1
| Cond c t e -> if not (Val? c) then progress_exp g h c
| While c b -> if not (Val? c) then progress_exp g h c

(* type preservation for expressions *)
val preservation_exp : g:env -> h:heap{typed_heap g h} ->
                       e:exp{Some? (typing_exp g e) /\ Some? (step_exp h e)} ->
                       Lemma (typing_exp g (Some?.v (step_exp h e)) = typing_exp g e)
let rec preservation_exp g h e = match e with
| Val _ -> ()
| Var _ -> ()
| If c tb eb -> if not (Val? c) then preservation_exp g h c
| Op op op1 op2 -> match (op1, op2) with
  | (Val _, Val _) -> ()
  | (Val _, _) -> preservation_exp g h op2
  | _ -> preservation_exp g h op1

(* type preservation for statments -- working variant *)
val preservation : g:env -> h:heap{typed_heap g h} ->
                   s:stmt{typing g s /\ Some? (step h s)} -> Lemma
                   (typing g (Mktuple2?._2 (Some?.v (step h s))) /\
                     typed_heap g (Mktuple2?._1 (Some?.v (step h s))))
let rec preservation g h s = match s with
| Skip -> ()
| Assign x t -> if not (Val? t) then preservation_exp g h t
| Seq s1 s2 -> if not (Skip? s1) then preservation g h s1
| Cond c t e -> if not (Val? c) then preservation_exp g h c
| While c b -> if not (Val? c) then preservation_exp g h c

(* type preservation for statments -- failing variant *)
val preservation' : g:env -> h:heap{typed_heap g h} ->
                   s:stmt{typing g s /\ Some? (step h s)} -> Lemma
                   (typing g (snd (Some?.v (step h s))) /\
                     typed_heap g (fst (Some?.v (step h s))))
let rec preservation' g h s = match s with
| Skip -> ()
| Assign x t -> if not (Val? t) then preservation_exp g h t
| Seq s1 s2 -> if not (Skip? s1) then preservation' g h s1
| Cond c t e -> if not (Val? c) then preservation_exp g h c
| While c b -> if not (Val? c) then preservation_exp g h c
