module DynamicIFC2

open Rel
open Label
open FStar.DM4F.Heap.LabeledIntStoreFixed
open FStar.DM4F.LabeledIntStoreExcFixed

module ISFR = FStar.DM4F.LabeledIntStoreFixedReader

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
  | Max   -> if b >= a then b else a

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


type label_fun = id -> Tot label
irreducible let trigger_leq (h:rel heap) (x:id) = True 

type env_eq (h : rel heap) = (forall (x:id). {:pattern (trigger_leq h x)} snd (sel (R?.l h) x) = snd (sel (R?.r h) x))

type low_equiv (h:rel heap) =
  (forall (x:id). {:pattern (trigger_leq h x)} (fun (vl,ll) (vr,lr) -> ll = Low ==> vl = vr)
      (index (R?.l h) x)  (index (R?.r h) x))

type low_equiv_env (env:label_fun) (h1:rel heap) =
  (forall (x:id). (* {:pattern (env x)} *) env x = Low ==> index (R?.l h1) x = index (R?.r h1) x)


type no_sensitive_upd (h:heap) (pc:label) (h':heap) =
  forall (x:id). (* {:pattern (trigger_nsu x)} *) (fun (v,l) (v',l') -> 
    (l' <= l /\
    (l < pc ==> v = v') /\
    (l <= pc ==> l = l')))
      (index h x)  (index h' x)


(* TODO : This function is total and does not use exceptions *)
(* as such it wouldn't be that surprising that writing it in a *)
(* exception free effect helps proving properties about it *)
(* The problem is that we then need refiable lifts from the *)
(* exceptionless effect to the exceptionfull one and this not covered yet *)
(* by the F* implementation. *)

(*  val interpret_exp_st : e:exp -> INT_STORE_EXC int (fun s0 p -> forall opt. p (opt, s0)) *)


let rec interpret_exp_st (e:exp) 
  (* : INT_STORE_EXC int (fun s0 p -> forall x. p (Some x, s0)) *)
  : ISFR.ISRNull (int * label)
=
  match e with
  | AInt i -> i, Low
  | AVar x -> ISFR.read x
  | AOp o e1 e2 ->
    let a,l1 = interpret_exp_st e1 in
    let b,l2 = interpret_exp_st e2 in
    interpret_binop o a b, join l1 l2


(* unfold *)
let interpret_exp (h:heap) (e:exp)  : Tot (int * label) = reify (interpret_exp_st e) h

let interpret_exp' (h:heap) (e:exp) : Tot nat =
  let n,_ = interpret_exp h e in
  if 0 > n then 0 else n

(* function used for the decreases clause *)
val decr_while : heap -> com -> GTot nat
let decr_while h c =
  match c with
  | While c b v -> interpret_exp' h v
  | _ -> 0

exception OutOfFuel
exception IfcViolation

 val interpret_com_st : c:com -> h0:heap -> pc:label -> IntStoreExc unit
  (requires (fun h -> h == h0))
  (ensures (fun h _ ho -> h == h0))
  (decreases %[c; decr_while h0 c])
 let rec interpret_com_st c h0 pc =
  match c with
  | Skip -> ()
  | Assign x e ->
    let v, le = interpret_exp_st e in
    let _, lx = ISFR.read x in 
    if join le pc <= lx then
    begin
      write x (v, (join le pc))
    end
    else
      raise_  () (* IfcViolation *)
  | Seq c1 c2 ->
    begin
      let h1 = (ISE?.get()) in
      interpret_com_st c1 h1 pc;
      let h2 = (ISE?.get()) in
      interpret_com_st c2 h2 pc
    end
  | If e ct cf ->
      let v,l  = interpret_exp_st e in
      let c = if v = 0 then cf else ct in
      let h = (ISE?.get()) in
      interpret_com_st c h (join l pc)
  | While e body v ->
    let v0, l = interpret_exp_st e in
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
        interpret_com_st body h1 (join l pc);
        let h2 = ISE?.get() in
        let m1 = interpret_exp' h2 v in
        if m0 > m1 then
          interpret_com_st c h2 pc
        else
          raise_ () (* OutOfFuel *)
      end

(* TODO : Normalization does not play very well with ensures clauses... *)
(* But there is no problem when replacing normalize_term by foobar where *)
(* abstract let foobar (#a:Type) (x:a) : a = x *)
(* unfold *)
let interpret_com (h0:heap) (c:com) (pc:label) : Tot (option heap)
=
  match (* normalize_term *) (reify (interpret_com_st c h0 pc) h0) with
  | Some (), h -> Some h
  | None, _ -> None


(* Some test cases *)

  (*
let h0 = upd (upd (create (5,Low)) (to_id 3) (5, High)) (to_id 4) (5, High)

#set-options "--z3rlimit 30"
(* l1 := h1 *)
let p1 = Assign (to_id 1) (AVar (to_id 3))
let test1 = assert_norm (None? (interpret_com h0 p1 Low))

(* l1 := l2 *)
let p2 = Assign (to_id 1) (AVar (to_id 2))
let test2 = assert_norm (Some? (interpret_com h0 p2 Low))

(* If (h1 + 2 <> 0 then {l1 := 9}   [env0(h1) = 5] *)
let p3 = If (AOp Plus (AVar (to_id 3)) (AInt 2)) (Assign (to_id 1) (AInt 0)) Skip
let test3 = assert_norm (None? (interpret_com h0 p3 Low))

(* This is example shows the weak semantic of the monitor's security *)
(* If (h1 - 5  <> 0 then {l1 := 9}  [env0(h1) = 5] *)
let p4 = If (AOp Plus (AVar (to_id 3)) (AInt (- 5))) (Assign (to_id 1) (AInt 0)) Skip
let test4 = assert_norm (Some? (interpret_com h0 p4 Low))

(* h1 := h2; l2 := h1 *)
let p5 = Seq (Assign (to_id 3) (AVar (to_id 4))) (Assign (to_id 2) (AVar (to_id 3)))
let test5 = assert_norm (None? (interpret_com h0 p5 Low))

(* h1 := l1; l2 := h1 *)
let p6 = Seq (Assign (to_id 3) (AVar (to_id 1))) (Assign (to_id 2) (AVar (to_id 3)))
let test6 = assert_norm (Some? ((interpret_com h0 p6 Low)))
#reset-options
*)


(* Proofs *)
val no_sens_trans : (pc:label) -> (pc2:label) -> (h1:heap) -> (h2:heap) -> (h3:heap) ->
  Lemma
    (requires (no_sensitive_upd h1 pc h2 /\ no_sensitive_upd h2 pc2 h3))
    (ensures (no_sensitive_upd h1 (meet pc pc2) h3))
let no_sens_trans pc pc2 h1 h2 h3 = ()

val no_sens_upd_pc : unit -> 
  Lemma (forall h h'. no_sensitive_upd h High h' ==> no_sensitive_upd h Low h')
let no_sens_upd_pc () = () 


#set-options "--z3rlimit 10"
val high_pc_assign : (x:id) -> (e:exp) -> (h:heap) -> (pc:label) ->
  Lemma (
      (let o = (interpret_com h (Assign x e) pc) in 
      (Some? o ==> no_sensitive_upd h pc (Some?.v o))))
let high_pc_assign x e h pc = ()

#set-options "--z3rlimit 60 --initial_fuel 1 --max_fuel 1 "
val high_pc : (c:com) -> (h:heap) -> (pc:label) ->
  Lemma
    (requires True)
    (ensures 
      (let o = (interpret_com h c pc) in 
      (Some? o ==> no_sensitive_upd h pc (Some?.v o))))
  (decreases %[c; decr_while h c])
let rec high_pc c h pc =
  match c with
  | Skip -> ()
  | Assign x e -> high_pc_assign x e h pc
  | If e ct cf ->
      let v0, l = interpret_exp h e in
      if v0 <> 0 then
        high_pc ct h (join l pc)
      else
        high_pc cf h (join l pc);
      if (Low? pc && High? l) then
        no_sens_upd_pc ()
  | Seq c1 c2 -> 
    let o = interpret_com h c1 pc in
    if Some? o then
    begin
      let h' = Some?.v o in
      high_pc c1 h pc;
      let o2 = interpret_com h' c2 pc in
      if Some? o2 then
      begin
        high_pc c2 h' pc;
        let h'' = Some?.v o2 in
        no_sens_trans pc pc h h' h''
      end
    end
        (*
    *)
  | _ -> admit ()
  (*
  | While e body v -> 
    let v0,l  = interpret_exp h e in
    if v0 <> 0 then
    begin
      let o = interpret_com h body (join pc l)in
      if Some? o then
      begin
        let h' = Some?.v o in
        high_pc body h (join pc l);
        let m0 = interpret_exp' h v in
        let m1 = interpret_exp' h' v in
        if m0 > m1 then
        begin
          let o2 = interpret_com h' c pc in
          if Some? o2 then
          begin
            let h'' = Some?.v o2 in
            high_pc c h' pc;
            no_sens_trans (join pc l) pc h h' h''
          end
        end
      end
    end
    *)

#reset-options

#set-options "--z3rlimit 15"
val dyn_ifc_exp : (e:exp) -> (h:(rel heap)) ->
    Lemma 
      (requires (low_equiv h /\ env_eq h))
      (ensures ((fun (vl,ll)  (vr,lr) ->
        lr = ll /\ (Low? lr ==> vl = vr))
        (interpret_exp (R?.l h) e)
        (interpret_exp (R?.r h) e)))
let rec dyn_ifc_exp e h  =
  match e with
  | AInt _ -> ()
  | AVar _ -> ()
  | AOp _ e1 e2 -> dyn_ifc_exp e1 h; dyn_ifc_exp e2 h


#reset-options
#set-options "--z3rlimit 2000 --initial_fuel 1 --max_fuel 1"
val dyn_ifc' : (c:com) -> (pc:label) -> (h:(rel heap)) ->
    Lemma
      (requires (low_equiv h /\ env_eq h))
      (ensures ((fun r1 r2 -> (Some? r1 /\ Some? r2) ==>
        (fun hl hr ->
          (low_equiv (R hl hr) /\
           env_eq (R hl hr)))
        (Some?.v r1) (Some?.v r2))
      (interpret_com (R?.l h) c pc)
      (interpret_com (R?.r h) c pc)))
      (decreases %[c; decr_while (R?.l h) c; decr_while (R?.r h) c])
let rec dyn_ifc' c pc h  =
  let (R hl hr) = h in
  if Low? pc then
  begin
    match c with
    | Skip -> ()
    | Assign x e -> admit () //dyn_ifc_exp e h
    | If e ct cf ->
        dyn_ifc_exp e h;
        (match interpret_exp hl e, interpret_exp hr e with
        | (0, ll) , (0, lr) ->
            dyn_ifc' cf (join pc ll) h
        | (0, ll) , (_, lr) ->
            cut (High? ll);
            high_pc cf hl High;
            high_pc ct hr High; ()
        | (_, ll) , (0, lr) ->
            cut (High? ll);
            high_pc ct hl High;
            high_pc cf hr High; ()
        | (_, ll) , (_, lr) ->
            dyn_ifc' ct (join pc ll) h)
    | Seq c1 c2 -> 
        let ol = interpret_com hl c1 pc in
        let or = interpret_com hr c1 pc in
        if (Some? ol && Some? or) then
        begin
          dyn_ifc' c1 pc h;
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          dyn_ifc' c2 pc (R hl' hr')
        end
    | While e body v -> 
      dyn_ifc_exp e h;
      let v0l,ll  = interpret_exp hl e in
      let v0r,lr  = interpret_exp hr e in
      (match v0l <> 0, v0r <> 0 with
      | true, true ->
        let ol = interpret_com hl body (join pc ll)in
        let or = interpret_com hr body (join pc lr)in
        if (Some? ol && Some? or) then
        begin
          dyn_ifc' body (join ll pc) h;
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          high_pc body hl(join ll pc) ;
          high_pc body hr(join lr pc) ;
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0l > m1l && m0r > m1r then
            dyn_ifc' c pc (R hl' hr')
        end
      | true, false  ->
        cut (High? ll);
        let ol = interpret_com hl body High in
        if (Some? ol) then
        begin
          let hl' = Some?.v ol in
          high_pc body hl High;
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          if m0l > m1l then
            dyn_ifc' c  pc (R hl' hr)
        end
      | false, true ->
        cut (High? lr);
        let or = interpret_com hr body High in
        if (Some? or) then
        begin
          let hr' = Some?.v or in
          high_pc body hr High;
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0r > m1r then
            dyn_ifc' c  pc (R hl hr')
        end
      | false, false -> ())
  end
  else
  begin
    high_pc c hl pc;
    high_pc c hr pc
  end
  
(*
#reset-options    
val dyn_ifc : (c:com) -> (env:label_fun) -> (pc:label) ->
    (h:(rel heap)) ->
    Lemma
      (requires (low_equiv h /\
        (forall (x:id). snd (sel (R?.l h) x) = env x /\ 
                        snd (sel (R?.r h) x) = env x)))
      (ensures ((fun r1 r2 -> (Some? r1 /\ Some? r2) ==>
        (fun hl hr -> (low_equiv_env env (R hl hr)))
        (Some?.v r1) (Some?.v r2))
      (interpret_com (R?.l h) c pc)
      (interpret_com (R?.r h) c pc)))
let dyn_ifc c env pc h = dyn_ifc' c  pc h; high_pc c (R?.l h) pc
*)
