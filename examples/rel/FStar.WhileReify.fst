module FStar.WhileReify

open FStar.Seq
open FStar.DM4F.IntStore

type id = nat

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

type exp =
| AInt : int -> exp
| AVar : id -> exp
| AOp  : binop -> exp -> exp -> exp

(*
val interpret_exp : h:heap -> e:exp -> GTot int
let rec interpret_exp h e =
  match e with
  | AInt i -> i
  | AVar x -> sel h x
  | AOp o e1 e2 ->
    let a = interpret_exp h e1 in
    let b = interpret_exp h e2 in
    interpret_binop o a b
*)

(* CH: This is a termination metric (natural number expression) for
       showing termination of while.  (Why not call it that?)
       Decreasingness and positivity of this termination metric
       _dynamically_ checked. *)
type variant = exp
//type variant = e:exp{forall h. 0 <= interpret_exp h e}

(* Commands -- loops are annotated with variants *)
type com =
| Skip   : com
| Assign : var:id -> term:exp -> com
| Seq    : first:com -> second:com -> com
| If     : cond:exp -> then_branch:com -> else_branch:com -> com
| While  : cond:exp -> body:com -> variant:variant -> com


reifiable val interpret_exp_st : e:exp -> INT_STORE int (fun s0 p -> forall opt. p (opt, s0))
reifiable let rec interpret_exp_st e =
  match e with
  | AInt i -> i
  | AVar x -> read x
  | AOp o e1 e2 ->
    let a = interpret_exp_st e1 in
    let b = interpret_exp_st e2 in
    interpret_binop o a b

let interpret_exp h e = normalize_term (reify (interpret_exp_st e) h)

(* function used for the decreases clause *)
val decr_while : seq int -> com -> GTot int
let decr_while h c =
  match c with
  | While c b v ->
    let tmp, _h' = reify (interpret_exp_st v) h in
    begin match tmp with
    | Some tmp -> if tmp < 0 then 0 else tmp
    | _ -> 0
    end
  | _ -> 0

exception OutOfFuel

reifiable val interpret_com_st : c:com -> h0:seq int -> IntStore unit
  (requires (fun h -> h == h0))
  (ensures (fun _ _ _ -> True))
  (decreases %[c; decr_while h0 c])
reifiable let rec interpret_com_st c h0 =
  match c with
  | Skip -> ()
  | Assign x e ->
    let v = interpret_exp_st e in
    write x v
  | Seq c1 c2 ->
    begin
      let h1 = (IS?.get()) in
      interpret_com_st c1 h1;
      let h2 = (IS?.get()) in
      interpret_com_st c2 h2
    end
  | If e ct cf ->
      let c = if interpret_exp_st e = 0 then cf else ct in
      let h = (IS?.get()) in
      interpret_com_st c h
  | While e body v ->
    if interpret_exp_st e <> 0 then
      begin
      (*   let m0 = interpret_exp_st v in *)
      (*   interpret_com_st body (IS?.get()); *)
      (*   let m1 = interpret_exp_st v in *)
      (* proving recursive terminating relies of interpret_exp not
         changing the state? somehow F* can't prove this although
         interpret_exp_st has that in the spec! *)
      (* working around by using reify *)
        let m0, _ = reify (interpret_exp_st v) h0 in
        interpret_com_st body h0;
        let h1 = IS?.get() in
        let m1, _ = reify (interpret_exp_st v) h1 in
        if m0 > m1 && m1 >= 0 then
          let h2 = (IS?.get()) in
          interpret_com_st c h2
        else
          raise_ () (* raise OutOfFuel -- XXX: no exceptions yet *)
      end

let interpret_com h c = normalize_term (reify (interpret_com_st c h) h)
