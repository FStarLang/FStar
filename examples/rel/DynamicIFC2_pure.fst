module DynamicIFC2_pure

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

let trigger_eq (h:rel heap) (x:id) = True

type env_eq (h : rel heap) = (forall (x:id).  (* {:pattern (trigger_eq h x)} *) snd (sel (R?.l h) x) = snd (sel (R?.r h) x))

type low_equiv (h:rel heap) =
  (forall (x:id). (* {:pattern (trigger_eq h x)} *) (fun (vl,ll) (vr,lr) -> ll = Low ==> vl = vr)
      (index (R?.l h) x)  (index (R?.r h) x))

type low_equiv_env (env:label_fun) (h1:rel heap) =
  (forall (x:id). env x = Low ==> index (R?.l h1) x = index (R?.r h1) x)


type no_sensitive_upd (h:heap) (pc:label) (h':heap) =
  forall (x:id). (fun (v,l) (v',l') -> 
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

val interpret_exp_pure : (h:heap) -> (e:exp) -> Tot (int * label)
let rec interpret_exp_pure h e = 
  match e with
  | AInt i -> i, Low
  | AVar x -> sel h x 
  | AOp o e1 e2 ->
    let a,l1 = interpret_exp_pure h e1 in
    let b,l2 = interpret_exp_pure h e2 in
    interpret_binop o a b, join l1 l2



(* unfold *)
(* let interpret_exp (h:heap) (e:exp)  : Tot (int * label) = reify (interpret_exp_st e) h *)
let interpret_exp (h:heap) (e:exp)  : Tot (int * label) = interpret_exp_pure h e

let interpret_exp' (h:heap) (e:exp) : Tot nat =
  let n,_ = interpret_exp h e in
  if 0 > n then 0 else n

(* function used for the decreases clause *)
val decr_while : heap -> com -> GTot nat
let decr_while h c =
  match c with
  | While c b v -> interpret_exp' h v
  | _ -> 0

let interpret_exp_pure' (h:heap) (e:exp) : Tot nat =
  let n,_ = interpret_exp_pure h e in
  if 0 > n then 0 else n

(* function used for the decreases clause *)
val decr_while_pure : heap -> com -> GTot nat
let decr_while_pure h c =
  match c with
  | While c b v -> interpret_exp_pure' h v
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

 val interpret_com_pure : h:heap -> c:com ->  pc:label -> Tot (option heap)
  (decreases %[c; decr_while_pure h c])
 let rec interpret_com_pure h c pc =
  match c with
  | Skip -> Some h
  | Assign x e ->
    let v, le = interpret_exp_pure h e in
    let _, lx = sel h x in 
    if join le pc <= lx then
    begin
      Some (upd h x (v, (join le pc)))
    end
    else
      None (* IfcViolation *)
  | Seq c1 c2 ->
    let o = interpret_com_pure h c1 pc in
    if Some? o then 
    begin
      let h' = Some?.v o in 
      interpret_com_pure h' c2 pc
    end
    else 
      None
  | If e ct cf ->
      let v,l  = interpret_exp_pure h e in
      let c = if v = 0 then cf else ct in
      interpret_com_pure h c (join l pc)
  | While e body v ->
    let v0, l = interpret_exp_pure h e in
    if v0 <> 0 then
      begin
        (* let m0 = interpret_exp_st v in *)
        (* let h = ISE?.get () in *)
        (* interpret_com_st body h; *)
        (* let m1 = interpret_exp_st v in *)
        (* proving recursive terminating relies of interpret_exp not *)
        (* changing the state? somehow F* can't prove this although *)
        (* interpret_exp_st has that in the spec! *)
        let m0 = interpret_exp_pure' h v in
        let o = interpret_com_pure h body (join l pc) in 
        if Some? o then 
        begin
          let h' = Some?.v o in 
          let m1 = interpret_exp_pure' h' v in
          if m0 > m1 then
            interpret_com_pure h' c pc
          else
            None
        end
        else
          None
      end
    else
      Some h


(* TODO : Normalization does not play very well with ensures clauses... *)
(* But there is no problem when replacing normalize_term by foobar where *)
(* abstract let foobar (#a:Type) (x:a) : a = x *)
(* unfold *)
let interpret_com (h0:heap) (c:com) (pc:label) : Tot (option heap)
=
  interpret_com_pure h0 c pc
(*
  match (* normalize_term *) (reify (interpret_com_st c h0 pc) h0) with
  | Some (), h -> Some h
  | None, _ -> None
*)


(* Some test cases *)

let h0 = upd (upd (create (5,Low)) (to_id 3) (5, High)) (to_id 4) (5, High)

#set-options "--z3rlimit 60 --max_fuel 16 --max_ifuel 16"
(* l1 := h1 *)
let p1 = Assign (to_id 1) (AVar (to_id 3))
let test1 = assert_norm (None? (interpret_com h0 p1 Low))

(* l1 := l2 *)
let p2 = Assign (to_id 1) (AVar (to_id 2))
let test2 = assert_norm (Some? (interpret_com h0 p2 Low))

(* If (h1 + 2 <> 0 then {l1 := 9}   [env0(h1) = 5] *)
let p3 = If (AOp Plus (AVar (to_id 3)) (AInt 2)) (Assign (to_id 1) (AInt 0)) Skip
let test3 = assert_norm (None? (interpret_com h0 p3 Low))

(* This is example shows the "weak" semantic of the monitor's security *)
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

(* Proofs *)
val no_sens_trans : (pc:label) -> (pc2:label) -> (h1:heap) -> (h2:heap) -> (h3:heap) ->
  Lemma
    (requires (no_sensitive_upd h1 pc h2 /\ no_sensitive_upd h2 pc2 h3))
    (ensures (no_sensitive_upd h1 (meet pc pc2) h3))
let no_sens_trans pc pc2 h1 h2 h3 = ()

val no_sens_upd_pc : unit -> 
  Lemma (forall h h'. no_sensitive_upd h High h' ==> no_sensitive_upd h Low h')
let no_sens_upd_pc () = () 

type high_pc_type (c:com) (h:heap) (pc:label) = 
  begin
    let o = (interpret_com h c pc) in 
    (Some? o ==> no_sensitive_upd h pc (Some?.v o))
  end

#set-options "--z3rlimit 30 "
val high_pc_assign : (x:id) -> (e:exp) -> (h:heap) -> (pc:label) ->
  Lemma (high_pc_type (Assign x e) h pc)
let high_pc_assign x e h pc = ()
#reset-options


#set-options "--z3rlimit 500 --initial_fuel 1 --max_fuel 1"
val high_pc_while : (e:exp) -> (body:com) -> (v:exp) -> (h:heap) -> (pc:label) -> 
  Lemma 
    (requires 
      (
      let c = While e body v in 
      let v0,l  = interpret_exp h e in
      if v0 <> 0 then
      begin
        let o = interpret_com h body (join l pc)in
        if Some? o then
        begin
          let h' = Some?.v o in
          high_pc_type body h (join l pc) /\
          begin
            let m0 = interpret_exp' h v in
            let m1 = interpret_exp' h' v in
            if m0 > m1 then
            begin
              let o2 = interpret_com h' c pc in
              if Some? o2 then
              begin
                let h'' = Some?.v o2 in
                high_pc_type c h' pc
              end
              else True
            end
            else True
          end
        end
        else True
      end
      else True))
    (ensures (high_pc_type (While e body v) h pc))
let high_pc_while e body v h pc = 
  let c = While e body v in
  let r = interpret_com h c pc in
  let v0,l  = interpret_exp h e in
  if v0 <> 0 then
  begin
    let o = interpret_com h body (join l pc) in
    if Some? o then
    begin
      let h' = Some?.v o in
      cut (high_pc_type body h (join l pc));
      let m0 = interpret_exp' h v in
      let m1 = interpret_exp' h' v in
      if m0 > m1 then
      begin
        let o2 = interpret_com h' c pc in
        if Some? o2 then
        begin
          let h'' = Some?.v o2 in
          cut (high_pc_type c h' pc);
          cut (Some? r /\ Some?.v r = h'');
          no_sens_trans (join l pc) pc h h' h''
        end
        else
          cut(None? r)
      end
      else
        cut(None? r)
    end
    else
      cut(None? r)
  end
  else
    cut (Some? r /\ Some?.v r = h)

#reset-options
    
#set-options "--z3rlimit 1000 --initial_fuel 1 --max_fuel 1"
val high_pc : (c:com) -> (h:heap) -> (pc:label) ->
  Lemma
    (requires True)
    (ensures high_pc_type c h pc)
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
  | While e body v -> 
    let v0,l  = interpret_exp h e in
    if v0 <> 0 then
    begin
      let o = interpret_com h body (join l pc)in
      if Some? o then
      begin
        let h' = Some?.v o in
        high_pc body h (join l pc);
        let m0 = interpret_exp' h v in
        let m1 = interpret_exp' h' v in
        if m0 > m1 then
        begin
          let o2 = interpret_com h' c pc in
          if Some? o2 then
          begin
            high_pc c h' pc
          end
        end
      end
    end;
    high_pc_while e body v h pc


#reset-options

#set-options "--z3rlimit 15 "
val dyn_ifc_exp : (e:exp) -> (h:(rel heap)) ->
    Lemma 
      (requires (low_equiv h /\ env_eq h))
      (ensures (
        let vl,ll = interpret_exp (R?.l h) e in 
        let vr,lr = interpret_exp (R?.r h) e in 
          lr = ll /\ (Low? lr ==> vl = vr)))
let rec dyn_ifc_exp e h  =
  match e with
  | AInt _ -> ()
  | AVar _ -> ()
  | AOp _ e1 e2 -> dyn_ifc_exp e1 h; dyn_ifc_exp e2 h



type ifc_type (c:com) (pc:label) (h:rel heap) = 
  begin
    let ol = (interpret_com (R?.l h) c pc) in 
     let or = (interpret_com (R?.r h) c pc) in 
     if (Some? ol && Some? or) then
     begin
       let h' = R (Some?.v ol) (Some?.v or) in 
       low_equiv h' /\ env_eq h'
     end
     else True
  end


#set-options "--z3rlimit 10 "
val dyn_ifc_assign : (x:id) -> (e:exp) -> (pc:label) -> (h:rel heap) -> 
  Lemma
      (requires (low_equiv h /\ env_eq h))
      (ensures (ifc_type (Assign x e) pc h))
let dyn_ifc_assign x e pc h = dyn_ifc_exp e h 
#reset-options


#set-options "--z3rlimit 1000 --initial_fuel 1 --max_fuel 2 "
val dyn_ifc_while : (e:exp) -> (body:com) -> (v:exp) -> (pc:label) -> (h:rel heap) -> 
   Lemma
      (requires (low_equiv h /\ env_eq h /\ 
        begin
          let R hl hr = h in 
          let c = While e body v in 
          let v0l,ll  = interpret_exp hl e in
          let v0r,lr  = interpret_exp hr e in
          match v0l <> 0, v0r <> 0 with
          | true, true ->  
            let ol = interpret_com hl body (join ll pc)in
            let or = interpret_com hr body (join lr pc)in
            if (Some? ol && Some? or) then
            begin
              ifc_type body (join ll pc) h /\ 
              begin
                let hl' = Some?.v ol in
                let hr' = Some?.v or in
                let m0l = interpret_exp' hl v in
                let m1l = interpret_exp' hl' v in
                let m0r = interpret_exp' hr v in
                let m1r = interpret_exp' hr' v in
                if m0l > m1l && m0r > m1r then
                  ifc_type c pc (R hl' hr')
                else True
              end
            end
            else True
          | true, false  ->
            let ol = interpret_com hl body High in
            if (Some? ol) then
            begin
              let hl' = Some?.v ol in
              let m0l = interpret_exp' hl v in
              let m1l = interpret_exp' hl' v in
              if m0l > m1l then
                ifc_type c pc (R hl' hr)
              else True
            end
            else True
          | false, true -> 
            let or = interpret_com hr body High in
            if (Some? or) then
            begin
              let hr' = Some?.v or in
              let m0r = interpret_exp' hr v in
              let m1r = interpret_exp' hr' v in
              if m0r > m1r then
                ifc_type c pc (R hl hr')
              else True
            end
            else True
          | false, false -> True
        end))
      (ensures (ifc_type (While e body v) pc h))
let dyn_ifc_while e body v pc h =  
  let R hl hr = h in 
  let c = While e body v in 
  let rl = interpret_com hl c pc in 
  let rr = interpret_com hr c pc in 
  let v0l,ll  = interpret_exp hl e in
  let v0r,lr  = interpret_exp hr e in
  dyn_ifc_exp e h;
  match v0l <> 0, v0r <> 0 with
  | true, true -> 
      let ol = interpret_com hl body (join ll pc) in
      let or = interpret_com hr body (join lr pc) in
      if (Some? ol && Some? or) then
      begin
        begin
          cut (ifc_type body (join ll pc) h);
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0l > m1l && m0r > m1r then
          begin
            cut (ifc_type c pc (R hl' hr'));
            cut (rl = interpret_com hl' c pc);
            cut (rr = interpret_com hr' c pc)
          end
        end
      end
  | true, false ->
      cut (High? ll);
      let ol = interpret_com hl body High in
      if (Some? ol) then
      begin
        let hl' = Some?.v ol in
        high_pc body hl High;
        let m0l = interpret_exp' hl v in
        let m1l = interpret_exp' hl' v in
        if m0l > m1l then
        begin 
          cut (ifc_type c  pc (R hl' hr));
          cut (rl = interpret_com hl' c pc)
        end
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
        begin
          cut (ifc_type c  pc (R hl hr'));
          cut (rr = interpret_com hr' c pc)
        end
      end
 | false, false -> ()

#reset-options


#set-options "--z3rlimit 1000 --initial_fuel 1 --max_fuel 1" 
val dyn_ifc' : (c:com) -> (pc:label) -> (h:(rel heap)) ->
    Lemma
      (requires (low_equiv h /\ env_eq h))
      (ensures (ifc_type c pc h))
      (decreases %[c; decr_while (R?.l h) c + decr_while (R?.r h) c])
let rec dyn_ifc' c pc h  =
  let (R hl hr) = h in
  if Low? pc then
  begin
    match c with
    | Skip -> ()
    | Assign x e -> dyn_ifc_assign x e pc h
    | If e ct cf ->
        dyn_ifc_exp e h;
        (match interpret_exp hl e, interpret_exp hr e with
        | (0, ll) , (0, lr) ->
            dyn_ifc' cf (join ll pc) h
        | (0, ll) , (_, lr) ->
            cut (High? ll);
            high_pc cf hl High;
            high_pc ct hr High 
        | (_, ll) , (0, lr) ->
            cut (High? ll);
            high_pc ct hl High;
            high_pc cf hr High
        | (_, ll) , (_, lr) ->
            dyn_ifc' ct (join ll pc) h)
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
        let ol = interpret_com hl body (join ll pc)in
        let or = interpret_com hr body (join lr pc)in
        if (Some? ol && Some? or) then
        begin
          dyn_ifc' body (join ll pc) h;
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0l > m1l && m0r > m1r then
            dyn_ifc' c pc (R hl' hr')
        end
      | true, false  ->
        let ol = interpret_com hl body High in
        if (Some? ol) then
        begin
          let hl' = Some?.v ol in
          high_pc body hl High;
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          if m0l > m1l then
          begin 
            dyn_ifc' c  pc (R hl' hr)
          end

        end
      | false, true -> 
        let or = interpret_com hr body High in
        if (Some? or) then
        begin
          let hr' = Some?.v or in
          high_pc body hr High;
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0r > m1r then
          begin
            dyn_ifc' c  pc (R hl hr')
          end
        end
      | false, false -> ());
      dyn_ifc_while e body v pc h
  end
  else
  begin
    high_pc c hl pc;
    high_pc c hr pc
  end

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
let dyn_ifc c env pc h = 
  dyn_ifc' c pc h; 
  high_pc c (R?.l h) pc
