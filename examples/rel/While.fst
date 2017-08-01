module While
open FStar.Heap
open FStar.ST

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
  | Times -> op_Multiply a b
  | Max   -> if a <= b then b else a

noeq type exp =
| AInt : int -> exp
| AVar : id -> exp
| AOp  : binop -> exp -> exp -> exp

val interpret_exp : h:heap -> e:exp -> GTot int
let rec interpret_exp h e =
  match e with
  | AInt i -> i
  | AVar x -> sel h x
  | AOp o e1 e2 ->
    let a = interpret_exp h e1 in
    let b = interpret_exp h e2 in
    interpret_binop o a b

(* CH: This is a termination metric (natural number expression) for
       showing termination of while.  (Why not call it that?)
       Decreasingness and positivity of this termination metric
       _dynamically_ checked. *)
type variant = exp
(* type variant = e:exp{forall h. 0 <= interpret_exp h e} *)

(* Commands -- loops are annotated with variants *)
noeq type com =
| Skip   : com
| Assign : var:id -> term:exp -> com
| Seq    : first:com -> second:com -> com
| If     : cond:exp -> then_branch:com -> else_branch:com -> com
| While  : cond:exp -> body:com -> variant:variant -> com

(* function used for the decreases clause *)
val decr_while : heap -> com -> GTot int
let decr_while h c =
  match c with
  | While c b v ->
    let tmp = interpret_exp h v in
    if tmp < 0 then 0 else tmp
  | _ -> 0

(* Returns Some heap if the variant is correct *)

(* CH: This is ghost because it uses functions like upd to work on heaps *)

val interpret_while : h:heap -> c:com{While? c}
  -> GTot (option heap) (decreases %[c; decr_while h c; 0])

val interpret_com : h:heap -> c:com -> GTot (option heap) (decreases %[c; decr_while h c; 1])

let rec interpret_while h (While e body v) =
  if interpret_exp h e = 0 then
    Some h
  else
    match interpret_com h body with
    | Some h' ->
      if interpret_exp h' v < interpret_exp h v && interpret_exp h' v >= 0 then
        interpret_while h' (While e body v)
      else
        None
    | None -> None

and interpret_com h c =
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
  | While e body v ->
    interpret_while h c

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
  (ensures  (fun h _ h' -> True))
let rec interpret_com_st c =
  match c with
  | Skip -> ()
  | Assign x e -> x := interpret_exp_st e
  | _ -> admit ()

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

(* CH: If interpret_com_st were made+proved terminating, then
       interpret_com would simply be its reification.

   (Our reification will anyway be forced to be ghost because state
   implemented primitively, so things like sel being ghost shouldn't
   make a difference.)
*)
