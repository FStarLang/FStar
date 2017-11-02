module IfcMonitor

open Rel
open Label
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

type low_equiv (env:label_fun) (h1:rel heap) =
  (forall (x:id). env x = Low ==> index (R?.l h1) x = index (R?.r h1) x)

type no_sensitive_upd (h:heap) (env:label_fun) (pc:label) (h':heap) =
  forall (x:id). env x < pc ==> (index h x) = (index h' x)


(* TODO : This function is total and does not use exceptions *)
(* as such it wouldn't be that surprising that writing it in a *)
(* exception free effect helps proving properties about it *)
(* The problem is that we then need refiable lifts from the *)
(* exceptionless effect to the exceptionfull one and this not covered yet *)
(* by the F* implementation. *)

(*  val interpret_exp_st : e:exp -> INT_STORE_EXC int (fun s0 p -> forall opt. p (opt, s0)) *)


let rec interpret_exp_st (env:label_fun) (e:exp) 
  (* : INT_STORE_EXC int (fun s0 p -> forall x. p (Some x, s0)) *)
  : ISFR.ISRNull (int * label)
=
  match e with
  | AInt i -> i, Low
  | AVar x -> ISFR.read x, env x 
  | AOp o e1 e2 ->
    let a,l1 = interpret_exp_st env e1 in
    let b,l2 = interpret_exp_st env e2 in
    interpret_binop o a b, join l1 l2


(* unfold *)
let interpret_exp (h:heap) (env:label_fun) (e:exp)  : Tot (int * label) = reify (interpret_exp_st env e) h

let interpret_exp' (h:heap) (e:exp) : Tot nat =
  let n,_ = interpret_exp h (fun _ -> Low)  e in
  if 0 > n then 0 else n

(* function used for the decreases clause *)
val decr_while : heap -> com -> GTot nat
let decr_while h c =
  match c with
  | While c b v -> interpret_exp' h v
  | _ -> 0

exception OutOfFuel
exception IfcViolation

 val interpret_com_st : c:com -> h0:heap -> env:label_fun -> pc:label -> IntStoreExc unit
  (requires (fun h -> h == h0))
  (ensures (fun h _ ho -> h == h0))
  (decreases %[c; decr_while h0 c])
 let rec interpret_com_st c h0 env pc =
  match c with
  | Skip -> ()
  | Assign x e ->
    let v, le = interpret_exp_st env e in
    let lx = env x in
    if join le pc <= lx then
    begin
      write x v
    end
    else
      raise_  () (* IfcViolation *)
  | Seq c1 c2 ->
    begin
      let h1 = (ISE?.get()) in
      interpret_com_st c1 h1 env pc;
      let h2 = (ISE?.get()) in
      interpret_com_st c2 h2 env pc
    end
  | If e ct cf ->
      let v,l  = interpret_exp_st env e in
      let c = if v = 0 then cf else ct in
      let h = (ISE?.get()) in
      interpret_com_st c h env (join l pc)
  | While e body v ->
    let v0, l = interpret_exp_st env e in
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
        interpret_com_st body h1 env (join l pc);
        let h2 = ISE?.get() in
        let m1 = interpret_exp' h2 v in
        if m0 > m1 then
          interpret_com_st c h2 env pc
        else
          raise_ () (* OutOfFuel *)
      end

(* TODO : Normalization does not play very well with ensures clauses... *)
(* But there is no problem when replacing normalize_term by foobar where *)
(* abstract let foobar (#a:Type) (x:a) : a = x *)
(* unfold *)
let interpret_com (h0:heap) (c:com) (env:label_fun) (pc:label) : Tot (option heap)
=
  match (* normalize_term *) (reify (interpret_com_st c h0 env pc) h0) with
  | Some (), h -> Some h
  | None, _ -> None

(* Proofs *)
val no_sens_trans : (env:label_fun) -> (pc:label) -> (pc2:label) -> (h1:heap) -> (h2:heap) -> (h3:heap) ->
  Lemma
    (requires (no_sensitive_upd h1 env pc h2 /\ no_sensitive_upd h2 env pc2 h3))
    (ensures (no_sensitive_upd h1 env (meet pc pc2) h3))
let no_sens_trans env pc pc2 h1 h2 h3 = ()

val no_sens_upd_pc : unit -> 
  Lemma (forall env h h'. no_sensitive_upd h env High h' ==> no_sensitive_upd h env Low h')
let no_sens_upd_pc () = () 

type high_pc_type (c:com) (h:heap) (env:label_fun) (pc:label) = 
  begin
    let o = (interpret_com h c env pc) in 
    (Some? o ==> no_sensitive_upd h env pc (Some?.v o))
  end

#set-options "--z3rlimit 10 "
val high_pc_assign : (x:id) -> (e:exp) -> (h:heap) -> (env:label_fun) -> (pc:label) ->
  Lemma (high_pc_type (Assign x e) h env pc)
let high_pc_assign x e h env pc = ()
#reset-options


#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"
val high_pc_while : (e:exp) -> (body:com) -> (v:exp) -> (h:heap) -> (env:label_fun) -> (pc:label) -> 
  Lemma 
    (requires 
      (
      let c = While e body v in 
      let v0,l  = interpret_exp h env e in
      if v0 <> 0 then
      begin
        let o = interpret_com h body env (join l pc)in
        if Some? o then
        begin
          let h' = Some?.v o in
          high_pc_type body h env (join l pc) /\
          begin
            let m0 = interpret_exp' h v in
            let m1 = interpret_exp' h' v in
            if m0 > m1 then
            begin
              let o2 = interpret_com h' c env pc in
              if Some? o2 then
              begin
                let h'' = Some?.v o2 in
                high_pc_type c h' env pc
              end
              else True
            end
            else True
          end
        end
        else True
      end
      else True))
    (ensures (high_pc_type (While e body v) h env pc))
let high_pc_while e body v h env pc = 
  let c = While e body v in
  let r = interpret_com h c env pc in
  let v0,l  = interpret_exp h env e in
  if v0 <> 0 then
  begin
    let o = interpret_com h body env (join l pc) in
    if Some? o then
    begin
      let h' = Some?.v o in
      cut (high_pc_type body h env (join l pc));
      let m0 = interpret_exp' h v in
      let m1 = interpret_exp' h' v in
      if m0 > m1 then
      begin
        let o2 = interpret_com h' c env pc in
        if Some? o2 then
        begin
          let h'' = Some?.v o2 in
          cut (high_pc_type c h' env pc);
          cut (Some? r /\ Some?.v r = h'');
          no_sens_trans env (join l pc) pc h h' h''
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
    
#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1"
val high_pc : (c:com) -> (h:heap) -> (env:label_fun) -> (pc:label) ->
  Lemma
    (requires True)
    (ensures high_pc_type c h env pc)
  (decreases %[c; decr_while h c])
let rec high_pc c h env pc =
  match c with
  | Skip -> ()
  | Assign x e -> high_pc_assign x e h env pc
  | If e ct cf ->
      let v0, l = interpret_exp h env e in
      if v0 <> 0 then
        high_pc ct h env (join l pc)
      else
        high_pc cf h env (join l pc);
      if (Low? pc && High? l) then
        no_sens_upd_pc ()
  | Seq c1 c2 -> 
    let o = interpret_com h c1 env pc in
    if Some? o then
    begin
      let h' = Some?.v o in
      high_pc c1 h env pc;
      let o2 = interpret_com h' c2 env pc in
      if Some? o2 then
      begin
        high_pc c2 h' env pc;
        let h'' = Some?.v o2 in
        no_sens_trans env pc pc h h' h''
      end
    end
  | While e body v -> 
    let v0,l  = interpret_exp h env e in
    if v0 <> 0 then
    begin
      let o = interpret_com h body env (join l pc)in
      if Some? o then
      begin
        let h' = Some?.v o in
        high_pc body h env (join l pc);
        let m0 = interpret_exp' h v in
        let m1 = interpret_exp' h' v in
        if m0 > m1 then
        begin
          let o2 = interpret_com h' c env pc in
          if Some? o2 then
          begin
            high_pc c h' env pc
          end
        end
      end
    end;
    high_pc_while e body v h env pc


#reset-options

#set-options "--z3rlimit 15 "
val dyn_ifc_exp : (e:exp) -> (h:(rel heap)) -> (env:label_fun) ->
    Lemma 
      (requires (low_equiv env h))
      (ensures (
        let vl,ll = interpret_exp (R?.l h) env e in 
        let vr,lr = interpret_exp (R?.r h) env e in 
          lr = ll /\ (Low? lr ==> vl = vr)))
let rec dyn_ifc_exp e h env =
  match e with
  | AInt _ -> ()
  | AVar _ -> ()
  | AOp _ e1 e2 -> dyn_ifc_exp e1 h env; dyn_ifc_exp e2 h env



type ifc_type (c:com) (env:label_fun) (pc:label) (h:rel heap) = 
  begin
    let ol = (interpret_com (R?.l h) c env pc) in 
     let or = (interpret_com (R?.r h) c env pc) in 
     if (Some? ol && Some? or) then
     begin
       let h' = R (Some?.v ol) (Some?.v or) in 
       low_equiv env h'
     end
     else True
  end


#set-options "--z3rlimit 30 "
val dyn_ifc_assign : (x:id) -> (e:exp) -> (env:label_fun) -> (pc:label) -> (h:rel heap) -> 
  Lemma
      (requires (low_equiv env h))
      (ensures (ifc_type (Assign x e) env pc h))
let dyn_ifc_assign x e env pc h = dyn_ifc_exp e h env
#reset-options


#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 2 "
val dyn_ifc_while : (e:exp) -> (body:com) -> (v:exp) -> (env:label_fun) -> (pc:label) -> (h:rel heap) -> 
   Lemma
      (requires (low_equiv env h /\
        begin
          let R hl hr = h in 
          let c = While e body v in 
          let v0l,ll  = interpret_exp hl env e in
          let v0r,lr  = interpret_exp hr env e in
          match v0l <> 0, v0r <> 0 with
          | true, true ->  
            let ol = interpret_com hl body env (join ll pc)in
            let or = interpret_com hr body env (join lr pc)in
            if (Some? ol && Some? or) then
            begin
              ifc_type body env (join ll pc) h /\ 
              begin
                let hl' = Some?.v ol in
                let hr' = Some?.v or in
                let m0l = interpret_exp' hl v in
                let m1l = interpret_exp' hl' v in
                let m0r = interpret_exp' hr v in
                let m1r = interpret_exp' hr' v in
                if m0l > m1l && m0r > m1r then
                  ifc_type c env pc (R hl' hr')
                else True
              end
            end
            else True
          | true, false  ->
            let ol = interpret_com hl body env High in
            if (Some? ol) then
            begin
              let hl' = Some?.v ol in
              let m0l = interpret_exp' hl v in
              let m1l = interpret_exp' hl' v in
              if m0l > m1l then
                ifc_type c env pc (R hl' hr)
              else True
            end
            else True
          | false, true -> 
            let or = interpret_com hr body env High in
            if (Some? or) then
            begin
              let hr' = Some?.v or in
              let m0r = interpret_exp' hr v in
              let m1r = interpret_exp' hr' v in
              if m0r > m1r then
                ifc_type c env pc (R hl hr')
              else True
            end
            else True
          | false, false -> True
        end))
      (ensures (ifc_type (While e body v) env pc h))
let dyn_ifc_while e body v env pc h =  
  let R hl hr = h in 
  let c = While e body v in 
  let rl = interpret_com hl c env pc in 
  let rr = interpret_com hr c env pc in 
  let v0l,ll  = interpret_exp hl env e in
  let v0r,lr  = interpret_exp hr env e in
  dyn_ifc_exp e h env;
  match v0l <> 0, v0r <> 0 with
  | true, true -> 
      let ol = interpret_com hl body env (join ll pc) in
      let or = interpret_com hr body env (join lr pc) in
      if (Some? ol && Some? or) then
      begin
        begin
          cut (ifc_type body env (join ll pc) h);
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0l > m1l && m0r > m1r then
          begin
            cut (ifc_type c env pc (R hl' hr'));
            cut (rl = interpret_com hl' c env pc);
            cut (rr = interpret_com hr' c env pc)
          end
        end
      end
  | true, false ->
      cut (High? ll);
      let ol = interpret_com hl body env High in
      if (Some? ol) then
      begin
        let hl' = Some?.v ol in
        high_pc body hl env High;
        let m0l = interpret_exp' hl v in
        let m1l = interpret_exp' hl' v in
        if m0l > m1l then
        begin 
          cut (ifc_type c env pc (R hl' hr));
          cut (rl = interpret_com hl' c env pc)
        end
      end
  | false, true -> 
      cut (High? lr);
      let or = interpret_com hr body env High in
      if (Some? or) then
      begin
        let hr' = Some?.v or in
        high_pc body hr env High;
        let m0r = interpret_exp' hr v in
        let m1r = interpret_exp' hr' v in
        if m0r > m1r then
        begin
          cut (ifc_type c env pc (R hl hr'));
          cut (rr = interpret_com hr' c env pc)
        end
      end
 | false, false -> ()

#reset-options

#set-options "--z3rlimit 50 --initial_fuel 1 --max_fuel 1" 
val dyn_ifc' : (c:com) -> (env:label_fun) -> (pc:label) -> (h:(rel heap)) ->
    Lemma
      (requires (low_equiv env h))
      (ensures (ifc_type c env pc h))
      (decreases %[c; decr_while (R?.l h) c + decr_while (R?.r h) c])
let rec dyn_ifc' c env pc h  =
  let (R hl hr) = h in
  if Low? pc then
  begin
    match c with
    | Skip -> ()
    | Assign x e -> dyn_ifc_assign x e env pc h
    | If e ct cf ->
        dyn_ifc_exp e h env;
        (match interpret_exp hl env e, interpret_exp hr env e with
        | (0, ll) , (0, lr) ->
            dyn_ifc' cf env (join ll pc) h
        | (0, ll) , (_, lr) ->
            cut (High? ll);
            high_pc cf hl env High;
            high_pc ct hr env High 
        | (_, ll) , (0, lr) ->
            cut (High? ll);
            high_pc ct hl env High;
            high_pc cf hr env High
        | (_, ll) , (_, lr) ->
            dyn_ifc' ct env (join ll pc) h)
    | Seq c1 c2 -> 
        let ol = interpret_com hl c1 env pc in
        let or = interpret_com hr c1 env pc in
        if (Some? ol && Some? or) then
        begin
          dyn_ifc' c1 env pc h;
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          dyn_ifc' c2 env pc (R hl' hr')
        end
    | While e body v -> 
      dyn_ifc_exp e h env;
      let v0l,ll  = interpret_exp hl env e in
      let v0r,lr  = interpret_exp hr env e in
      (match v0l <> 0, v0r <> 0 with
      | true, true ->  
        let ol = interpret_com hl body env (join ll pc)in
        let or = interpret_com hr body env (join lr pc)in
        if (Some? ol && Some? or) then
        begin
          dyn_ifc' body env (join ll pc) h;
          let hl' = Some?.v ol in
          let hr' = Some?.v or in
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0l > m1l && m0r > m1r then
            dyn_ifc' c env pc (R hl' hr')
        end
      | true, false  ->
        let ol = interpret_com hl body env High in
        if (Some? ol) then
        begin
          let hl' = Some?.v ol in
          high_pc body hl env High;
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          if m0l > m1l then
          begin 
            dyn_ifc' c  env pc (R hl' hr)
          end

        end
      | false, true -> 
        let or = interpret_com hr body env High in
        if (Some? or) then
        begin
          let hr' = Some?.v or in
          high_pc body hr env High;
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0r > m1r then
          begin
            dyn_ifc' c  env pc (R hl hr')
          end
        end
      | false, false -> ());
      dyn_ifc_while e body v env pc h
  end
  else
  begin
    high_pc c hl env pc;
    high_pc c hr env pc
  end

#reset-options    


val dyn_ifc : (c:com) -> (env:label_fun) -> (pc:label) ->
    (h:(rel heap)) ->
    Lemma
      (requires (low_equiv env h))
      (ensures ((fun r1 r2 -> (Some? r1 /\ Some? r2) ==>
        (fun hl hr -> (low_equiv env (R hl hr)))
        (Some?.v r1) (Some?.v r2))
      (interpret_com (R?.l h) c env pc)
      (interpret_com (R?.r h) c env pc)))
let dyn_ifc c env pc h = 
  dyn_ifc' c env pc h; 
  high_pc c (R?.l h) env pc
