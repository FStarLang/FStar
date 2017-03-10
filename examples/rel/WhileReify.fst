module WhileReify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreExcFixed

module ISFR = FStar.DM4F.IntStoreFixedReader

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

(* CH: This is a termination metric (natural number expression) for
       showing termination of while.
       Decreasingness and positivity of this termination metric
       _dynamically_ checked. *)
type metric = exp

(* Commands -- loops are annotated with metrics *)
type com =
| Skip   : com
| Assign : var:id -> term:exp -> com
| Seq    : first:com -> second:com -> com
| If     : cond:exp -> then_branch:com -> else_branch:com -> com
| While  : cond:exp -> body:com -> metric:metric -> com


(* TODO : This function is total and does not use exceptions *)
(* as such it wouldn't be that surprising that writing it in a *)
(* exception free effect helps proving properties about it *)
(* The problem is that we then need refiable lifts from the *)
(* exceptionless effect to the exceptionfull one and this not covered yet *)
(* by the F* implementation. *)

(*  val interpret_exp_st : e:exp -> INT_STORE_EXC int (fun s0 p -> forall opt. p (opt, s0)) *)

let rec interpret_exp_st (e:exp)
  (* : INT_STORE_EXC int (fun s0 p -> forall x. p (Some x, s0)) *)
  : ISFR.ISRNull int
=
  match e with
  | AInt i -> i
  | AVar x -> ISFR.read x
  | AOp o e1 e2 ->
    let a = interpret_exp_st e1 in
    let b = interpret_exp_st e2 in
    interpret_binop o a b


(* unfold *)
let interpret_exp (h:heap) (e:exp) : Tot int = reify (interpret_exp_st e) h


let interpret_exp' (h:heap) (e:exp) : Tot nat =
  let n = interpret_exp h e in
  if 0 > n then 0 else n

(* function used for the decreases clause *)
val decr_while : heap -> com -> GTot nat
let decr_while h c =
  match c with
  | While c b v -> interpret_exp' h v
  | _ -> 0

exception OutOfFuel

 val interpret_com_st : c:com -> h0:heap -> IntStoreExc unit
  (requires (fun h -> h == h0))
  (ensures (fun h _ ho -> h == h0))
  (decreases %[c; decr_while h0 c])
 let rec interpret_com_st c h0 =
  match c with
  | Skip -> ()
  | Assign x e ->
    let v = interpret_exp_st e in
    write x v
  | Seq c1 c2 ->
    begin
      let h1 = (ISE?.get()) in
      interpret_com_st c1 h1;
      let h2 = (ISE?.get()) in
      interpret_com_st c2 h2
    end
  | If e ct cf ->
      let v = interpret_exp_st e in
      let c = if v = 0 then cf else ct in
      let h = (ISE?.get()) in
      interpret_com_st c h
  | While e body v ->
    let v0 = interpret_exp_st e in
    if v0 <> 0 then
      begin
        (* let m0 = interpret_exp_st v in *)
        (* let h = ISE?.get () in *)
        (* interpret_com_st body h; *)
        (* let m1 = interpret_exp_st v in *)
        (* proving recursive terminating relies of interpret_exp not *)
        (* changing the state? somehow F* can't prove this although *)
        (* interpret_exp_st has that in the spec! *)
        let m0 = interpret_exp' h0 v in
        let h1 = ISE?.get () in
        interpret_com_st body h1;
        let h2 = ISE?.get() in
        let m1 = interpret_exp' h2 v in
        if m0 > m1 then
          interpret_com_st c h2
        else
          raise_ () (* OutOfFuel *)
      end


(* TODO : Normalization does not play very well with ensures clauses... *)
(* But there is no problem when replacing normalize_term by foobar where *)
(* abstract let foobar (#a:Type) (x:a) : a = x *)
(* unfold *)
let interpret_com (h0:heap) (c:com) : Tot (option heap)
=
  match (* normalize_term *) (reify (interpret_com_st c h0) h0) with
  | Some (), h -> Some h
  | None, _ -> None


let bidule = assert (reify (interpret_exp_st (AOp Plus (AVar (to_id 7)) (AInt 5))) (create 3) = 8)
let bidule2 = assert (interpret_exp (create 3) (AOp Plus (AVar (to_id 7)) (AInt 5)) = 8)
