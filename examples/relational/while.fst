(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:set.fsi heap.fst st.fst all.fst
--*)

module While

open FStar.Heap

type id = ref int

type binop =
| Plus
| Minus
| Times
| Max

val interpret_binop : o:binop -> a:int -> b:int -> Tot int
let interpret_binop o a b =
  match o with 
  | Plus  -> a + b
  | Minus -> a - b
  | Times -> a * b
  | Max   -> if a <= b then b else a

type exp =
| AInt : int -> exp
| AVar : id -> exp 
| AOp  : binop -> exp -> exp -> exp 

val interpret_exp : h:heap -> e:exp -> Tot int
let rec interpret_exp h e = 
  match e with
  | AInt i -> i
  | AVar x -> sel h x
  | AOp o e1 e2 -> 
    let a = interpret_exp h e1 in 
    let b = interpret_exp h e2 in 
    interpret_binop o a b

type variant = e:exp{forall h. 0 <= interpret_exp h e}

(* Commands -- loops are annotated with variants *)
type com =
| Skip   : com
| Assign : var:id -> term:exp -> com
| Seq    : first:com -> second:com -> com
| If     : cond:exp -> then_branch:com -> else_branch:com -> com
| While  : cond:exp -> body:com -> variant:variant -> com


(* Couldn't find a way of making F* accept a mutually recursive version of this *)
(* Returns Some heap if the variant is correct *)
val interpret_while : h:heap -> e:exp -> (body:heap -> Tot (option heap)) -> v:variant 
  -> Tot (option heap) (decreases (interpret_exp h v))
let rec interpret_while h e body v =
  if interpret_exp h e = 0 then
    Some h
  else
    match body h with
    | Some h' ->
      if interpret_exp h' v < interpret_exp h v then 
        interpret_while h' e body v
      else
        None
    | None -> None

val interpret_com : h:heap -> c:com -> Tot (option heap) (decreases c)
let rec interpret_com h c = 
  match c with
  | Skip -> Some h
  | Assign x e -> 
    let v = interpret_exp h e in 
    Some (upd h x v)
  | Seq c1 c2 -> (
    match interpret_com h c1 with
    | Some h' -> interpret_com h' c2
    | None -> None)    
  | If e ct cf -> 
    if interpret_exp h e = 0 then
      interpret_com h cf
    else
      interpret_com h ct
  | While e body v -> interpret_while h e (fun h -> interpret_com h body) v


val interpret_exp_st : e:exp -> ST int 
  (requires (fun _ -> True))
  (ensures  (fun h r h' -> equal h h' /\ r = interpret_exp h e))
let rec interpret_exp_st e =
  match e with
  | AInt i -> i
  | AVar x -> !x
  | AOp o e1 e2 -> 
    let a = interpret_exp_st e1 in 
    let b = interpret_exp_st e2 in 
    interpret_binop o a b

val interpret_com_st : c:com -> ST unit 
  (requires (fun _ -> True))
  (ensures  (fun h _ h' -> 
    Let (interpret_com h c) (fun o ->
     is_Some o ==> equal h' (Some.v o))))
let rec interpret_com_st c = 
  match c with
  | Skip -> ()
  | Assign x e -> x := interpret_exp_st e
  | Seq c1 c2 -> 
    begin
      interpret_com_st c1;
      interpret_com_st c2
    end
  | If e ct cf -> 
    if interpret_exp_st e = 0 then
      interpret_com_st cf
    else
      interpret_com_st ct
  | While e body v ->
    if interpret_exp_st e = 0 then
      ()
    else
      begin
        interpret_com_st body;
        interpret_com_st c
      end
