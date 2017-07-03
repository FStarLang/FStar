module DynamicIFC

open Rel
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


(****************************** Preliminaries ******************************)

(* CH: Everything specialized to 2-point lattice *)
type label =
| Low
| High

val op_Less : label -> label -> Tot bool
let op_Less l1 l2 =
  match l1, l2 with
  | Low,High -> true
  | _, _ -> false

val op_Less_Equals : label -> label -> Tot bool
let op_Less_Equals l1 l2 =
  match l1, l2 with
  | High,Low -> false
  | _, _ -> true

val join : label -> label -> Tot label
let join l1 l2 =
  match l1, l2 with
  | Low,Low -> Low
  | _, _ -> High

val meet : label -> label -> Tot label
let meet l1 l2 =
  match l1, l2 with
  | High, High -> High
  | _, _ -> Low

let universal_property_meet l l1 l2
  : Lemma (requires (l <= l1 /\ l <= l2)) (ensures (l <= meet l1 l2))
= ()

type label_fun = id -> Tot label

val update : label_fun -> id -> label -> Tot label_fun
let update env k v x = if x = k then v else env x

type env_eq (env : rel label_fun) = (forall (x:id). (* {:pattern (env x)} *) (R?.l env) x = (R?.r env) x)

type low_equiv (env:label_fun) (h1:rel heap) =
  (forall (x:id). (* {:pattern (env x)} *) env x = Low ==> index (R?.l h1) x = index (R?.r h1) x)

type no_sens_up (env:label_fun) (h:heap) (pc:label) (env':label_fun) (h':heap) =
  forall (x:id). 
    (env' x <= env x /\
    (env x < pc ==> sel h x = sel h' x) /\ 
    (env x <= pc ==> env x = env' x))

(* TODO : This function is total and does not use exceptions *)
(* as such it wouldn't be that surprising that writing it in a *)
(* exception free effect helps proving properties about it *)
(* The problem is that we then need refiable lifts from the *)
(* exceptionless effect to the exceptionfull one and this not covered yet *)
(* by the F* implementation. *)

(*  val interpret_exp_st : e:exp -> INT_STORE_EXC int (fun s0 p -> forall opt. p (opt, s0)) *)

let rec interpret_exp_st (e:exp) (env:label_fun) 
  (* : INT_STORE_EXC int (fun s0 p -> forall x. p (Some x, s0)) *)
  : ISFR.ISRNull (int * label)
=
  match e with
  | AInt i -> i, Low
  | AVar x -> ISFR.read x, env x 
  | AOp o e1 e2 ->
    let a,l1 = interpret_exp_st e1 env in
    let b,l2 = interpret_exp_st e2 env in
    interpret_binop o a b, join l1 l2


(* unfold *)
let interpret_exp (h:heap) (e:exp) (env:label_fun) : Tot (int * label) = reify (interpret_exp_st e env) h

let interpret_exp' (h:heap) (e:exp) : Tot nat =
  let n,_ = interpret_exp h e (fun _ -> Low) in 
  if 0 > n then 0 else n

(* function used for the decreases clause *)
val decr_while : heap -> com -> GTot nat 
let decr_while h c =
  match c with
  | While c b v -> interpret_exp' h v 
  | _ -> 0

exception OutOfFuel
exception IfcViolation

 val interpret_com_st : c:com -> h0:heap -> env:label_fun -> pc:label -> IntStoreExc label_fun
  (requires (fun h -> h == h0))
  (ensures (fun h _ ho -> h == h0))
  (decreases %[c; decr_while h0 c])
 let rec interpret_com_st c h0 env pc =
  match c with
  | Skip -> env
  | Assign x e ->
    let v, l = interpret_exp_st e env in
    if  join l pc <= env x then
    begin
      write x v; 
      update env x (join l pc)
    end
    else
      raise_  () (* IfcViolation *)
  | Seq c1 c2 ->
    begin
      let h1 = (ISE?.get()) in
      let env'=  interpret_com_st c1 h1 env pc in 
      let h2 = (ISE?.get()) in
      interpret_com_st c2 h2 env' pc
    end
  | If e ct cf ->
      let v,l  = interpret_exp_st e env in
      let c = if v = 0 then cf else ct in
      let h = (ISE?.get()) in
      interpret_com_st c h env (join l pc)
  | While e body v ->
    let v0, l = interpret_exp_st e env in
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
        let env' = interpret_com_st body h1 env (join l pc) in
        let h2 = ISE?.get() in
        let m1 = interpret_exp' h2 v in
        if m0 > m1 then
          interpret_com_st c h2 env' pc
        else
          raise_ () (* OutOfFuel *)
      end
    else
      env

(* TODO : Normalization does not play very well with ensures clauses... *)
(* But there is no problem when replacing normalize_term by foobar where *)
(* abstract let foobar (#a:Type) (x:a) : a = x *)
(* unfold *)
let interpret_com (h0:heap) (c:com) (env:label_fun) (pc:label) : Tot (option (label_fun * heap)) 
=
  match (* normalize_term *) (reify (interpret_com_st c h0 env pc) h0) with
  | Some env', h -> Some (env', h)
  | None, _ -> None

(*
let bidule = assert (reify (interpret_exp_st (AOp Plus (AVar (to_id 7)) (AInt 5))) (create 3) = 8)
let bidule2 = assert ((interpret_exp (create 3) (AOp Plus (AVar (to_id 7)) (AInt 5))) = 8)
*)

val dyn_ifc_exp : (e:exp) -> (env:(rel label_fun){env_eq env}) ->
    (h:(rel heap){low_equiv (R?.l env) h}) -> 
    Lemma ((fun (vl,ll)  (vr,lr) -> 
      lr = ll /\ (Low? lr ==> vl = vr)) 
      (interpret_exp (R?.l h) e (R?.l env))
      (interpret_exp (R?.r h) e (R?.r env)))
let rec dyn_ifc_exp e env h  = 
  match e with 
  | AInt _ -> ()
  | AVar _ -> ()
  | AOp _ e1 e2 -> dyn_ifc_exp e1 env h; dyn_ifc_exp e2 env h


val no_sens_trans : (pc:label) -> (pc2:label) -> (env1:label_fun) -> (h1:heap) -> (env2:label_fun) -> (h2:heap) -> (env3:label_fun) -> (h3:heap) ->
  Lemma
    (requires (no_sens_up env1 h1 pc env2 h2 /\ no_sens_up env2 h2 pc2 env3 h3))
    (ensures (no_sens_up env1 h1 (meet pc pc2) env3 h3))
let no_sens_trans pc pc2 evn1 h1 env2 h2 env3 h3 = ()


#set-options "--z3rlimit 500"
val high_pc : (c:com) -> (env:label_fun) -> (h:heap) -> (pc:label) -> 
  Lemma 
    (requires True)
    (ensures (fun o -> Some? o ==> (fun (env', h') -> 
        no_sens_up env h pc env' h'
      )
      (Some?.v o))
      (interpret_com h c env pc))
  (decreases %[c; decr_while h c])
let rec high_pc c env h pc = 
  match c with 
  | Skip -> () 
  | Assign x e -> ()
  | If e ct cf -> 
      let v0, l = interpret_exp h e env in 
      if v0 <> 0 then
        high_pc ct env h (join pc l)
      else
        high_pc cf env h (join pc l)
  | Seq c1 c2 -> 
    let o = interpret_com h c1 env pc in 
    if Some? o then 
    begin
      let env', h' = Some?.v o in 
      high_pc c1 env h pc;
      let o2 = interpret_com h' c2 env' pc in 
      if Some? o2 then 
      begin
        high_pc c2 env' h' pc;
        let env'', h'' = Some?.v o2 in 
        no_sens_trans pc pc env h env' h' env'' h''
      end
    end
  | While e body v -> 
    let v0,l  = interpret_exp h e env in 
    if v0 <> 0 then
    begin
      let m0 = interpret_exp' h v in
      let o = interpret_com h body env (join pc l)in
      if Some? o then 
      begin
        let env', h' = Some?.v o in 
        high_pc body env h (join pc l); 
        let m1 = interpret_exp' h' v in
        if m0 > m1 then
        begin
          let o2 = interpret_com h' c env' pc in
          if Some? o2 then 
          begin
            let env'', h'' = Some?.v o2 in 
            high_pc c env' h' pc;
            no_sens_trans (join pc l) pc env h env' h' env'' h''
          end
        end
      end
    end

#set-options "--z3rlimit 200"

val dyn_ifc : (c:com) -> (env:rel label_fun) -> (pc:label) -> 
    (h:(rel heap)) -> 
    Lemma 
      (requires (low_equiv (R?.l env) h /\ env_eq env))
      (ensures ((fun r1 r2 -> (Some? r1 /\ Some? r2) ==>  
        (fun (el,hl) (er,hr) -> 
          (low_equiv el (R hl hr) /\ 
           env_eq (R el er) /\
           no_sens_up  (R?.l env) (R?.l h) pc el hl /\ 
           no_sens_up  (R?.r env) (R?.r h) pc er hr ))
        (Some?.v r1) (Some?.v r2))
      (interpret_com (R?.l h) c (R?.l env) pc)
      (interpret_com (R?.r h) c (R?.r env) pc)))
      (decreases %[c; decr_while (R?.l h) c; decr_while (R?.r h) c])
let rec dyn_ifc c env pc h  = 
  let (R hl hr) = h in 
  let (R el er) = env in 
  high_pc c el hl pc;
  high_pc c er hr pc;
  if Low? pc then 
  begin
    match c with 
    | Skip -> ()
    | Assign x e -> dyn_ifc_exp e env h
    | If e ct cf ->  
        dyn_ifc_exp e env h;
        (match interpret_exp hl e el, interpret_exp hr e er with
        | (0, ll) , (0, lr) -> 
            dyn_ifc cf env (join pc ll) h
        | (0, ll) , (_, lr) -> 
            cut (High? ll); 
            high_pc cf el hl High;
            high_pc ct er hr High; ()
        | (_, ll) , (0, lr) -> 
            cut (High? ll); 
            high_pc ct el hl High;
            high_pc cf er hr High; ()
        | (_, ll) , (_, lr) -> 
            dyn_ifc ct env (join pc ll) h)
    | Seq c1 c2 -> 
        let rl = interpret_com hl c1 el pc in 
        let rr = interpret_com hr c1 er pc in 
        if (Some? rl && Some? rr) then
        begin
          dyn_ifc c1 env pc h; 
          let el', hl' = Some?.v rl in 
          let er', hr' = Some?.v rr in 
          dyn_ifc c2 (R el' er') pc (R hl' hr')
        end
    | While e body v -> 
      dyn_ifc_exp e env h;
      let v0l,ll  = interpret_exp hl e el in 
      let v0r,lr  = interpret_exp hr e er in 
      (match v0l <> 0, v0r <> 0 with
      | true, true -> 
        let ol = interpret_com hl body el (join pc ll)in
        let or = interpret_com hr body er (join pc lr)in
        if (Some? ol && Some? or) then
        begin
          dyn_ifc body env (join ll pc) h; 
          let el', hl' = Some?.v ol in 
          let er', hr' = Some?.v or in 
          high_pc body el hl(join ll pc) ;
          high_pc body er hr(join lr pc) ;
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0l > m1l && m0r > m1r then
            dyn_ifc c (R el' er') pc (R hl' hr')
        end
      | true, false  ->
        cut (High? ll);
        let ol = interpret_com hl body el High in
        if (Some? ol) then
        begin
          let el', hl' = Some?.v ol in 
          high_pc body el hl High;
          let m0l = interpret_exp' hl v in
          let m1l = interpret_exp' hl' v in
          if m0l > m1l then
            dyn_ifc c (R el' er) pc (R hl' hr)
        end
      | false, true -> 
        cut (High? lr);
        let or = interpret_com hr body er High in
        if (Some? or) then
        begin
          let er', hr' = Some?.v or in 
          high_pc body er hr High;
          let m0r = interpret_exp' hr v in
          let m1r = interpret_exp' hr' v in
          if m0r > m1r then
            dyn_ifc c (R el er') pc (R hl hr')
        end
      | false, false -> ())
  end
  else
    ()

val dyn_ifc' : (c:com) -> (env:label_fun) -> (pc:label) -> 
    (h:(rel heap)) -> 
    Lemma 
      (requires (low_equiv env h))
      (ensures ((fun r1 r2 -> (Some? r1 /\ Some? r2) ==>  
        (fun (el,hl) (er,hr) -> (low_equiv env (R hl hr)))
        (Some?.v r1) (Some?.v r2))
      (interpret_com (R?.l h) c env pc)
      (interpret_com (R?.r h) c env pc)))
let dyn_ifc' c env pc h = dyn_ifc c (R env env) pc h 
