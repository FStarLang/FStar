(*--build-config
    options:--admit_fsi FStar.Set;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst st2.fst while.fst
--*)

module IFC

open FStar.Comp
open FStar.Heap
open FStar.Relational

open While

(****************************** Preliminaries ******************************)

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

type label_fun = ref int -> Tot label

type low_equiv (env:label_fun) (h1:double heap) = 
  forall (x:ref int). env x = Low ==> sel (R.l h1) x = sel (R.r h1) x


(**************************** Typing Judgements ****************************)

(* env |- e : l
   - Expressions do not modify the heap
   - Correctness
   - Low equivalent input heaps + Low label ==> same result 
*)
type ni_exp (env:label_fun) (e:exp) (l:label) = double unit -> ST2 (double int)
  (requires (fun _ -> True))
  (ensures  (fun h0 r h1 -> 
               equal (R.l h0) (R.l h1) 
             /\ equal (R.r h0) (R.r h1)
             /\ R.l r = interpret_exp (R.l h0) e
             /\ R.r r = interpret_exp (R.r h0) e
             /\ (low_equiv env h0 /\ is_Low l ==> R.l r = R.r r)))


(* env,pc:l |- c
   - References with a label below l are not modified
   - Total correctness
   - Low equivalent input heaps ==> Low equivalet output heaps 
*)
type ni_com (env:label_fun) (c:com) (l:label) = double unit -> ST2 (double unit)
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 -> 
              (forall r.
                 env r < l
                  ==>   sel (R.l h0) r = sel (R.l h1) r
                    /\ sel (R.r h0) r = sel (R.r h1) r)
                /\ Let (interpret_com (R.l h0) c) (fun o -> 
                    is_Some o ==> equal (Some.v o) (R.l h1))
                /\ Let (interpret_com (R.r h0) c) (fun o -> 
                    is_Some o ==> equal (Some.v o) (R.r h1))
                /\ (low_equiv env h0 ==> low_equiv env h1)))


(* We define noninterference for a command as typability in a low pc *)
type ni (env:label_fun) (c:com) = ni_com env c Low


(*********************** Typing Rules for Expressions **********************)

(* Subtyping rule for expression labels

         E |- e : l1   l1 <= l2
         ----------------------
              E |- e : l2
*)


val sub_exp : env:label_fun -> e:exp -> l1:label -> l2:label{l1 <= l2}
  -> =e_ni:(ni_exp env e l1) -> Tot (ni_exp env e l2)
let sub_exp _ _ _ _ e_ni _ = e_ni tu


(* Typing rule for dereferencing

         label_fun(r) = l
         ----------------
             r : l
*)
val avar_exp : env:label_fun -> r:id -> Tot (ni_exp env (AVar r) (env r)) 
let avar_exp _ r _ = compose2_self read (twice r)


(* Typing rule for Int constants

         i : int
         -------
         i : Low
*)
val aint_exp : env:label_fun -> i:int -> Tot (ni_exp env (AInt i) Low)
let aint_exp _ i _ = twice i


(* Typing rule for binary operators

          e1 : l   e2 : l
          ----------------
          e1 `op` e2  : l
*)

val uncurry : #a:Type -> #b:Type -> #c:Type -> (a -> b -> Tot c) -> Tot ((a * b) -> Tot c)
let uncurry f (a,b) = f a b

val binop_exp : env:label_fun -> op:binop -> e1:exp -> e2:exp -> l:label 
  -> e1_ni:(ni_exp env e1 l) -> e2_ni:(ni_exp env e2 l) 
  -> Tot (ni_exp env (AOp op e1 e2) l)
let binop_exp env op e1 e2 l e1_ni e2_ni tu =
  // dummy eta-expansion
  (fun tu -> compose2_self (fun (a,b) -> interpret_binop op a b) 
                        (pair_rel (e1_ni tu) (e2_ni tu))) tu


(************************ Typing Rules for Commands ************************)

(* Subtyping rule for commands

         env,pc:l1 |- c   l2 <= l1
        ---------------------------
               env,pc:l2 |- c
*)
val sub_com : env:label_fun -> c:com -> l1:label -> l2:label{l2 <= l1} 
  -> =c_ni:(ni_com env c l1) -> Tot (ni_com env c l2)
let sub_com _ _ _ l2 c_ni _ = c_ni tu

(* Typing rule for assignment

         env |- e : env(r)    l <= env(r)
         --------------------------------
                  l |- r := e
*)
val assign_com : env:label_fun -> e:exp -> r:id
  -> =e_ni:ni_exp env e (env r) -> Tot (ni_com env (Assign r e) (env r))
let assign_com _ _ r e_ni _ = compose2_self (write r) (e_ni tu)

(* Sequencing rule for commands

         env,pc:l |- c1  env,pc:l |- c2
         ------------------------------
               env,pc:l |- c1; c2
*)
val seq_com : env:label_fun -> c1:com -> c2:com -> l:label 
  -> =c1_ni:(ni_com env c1 l) -> =c2_ni:(ni_com env c2 l) 
  -> Tot(ni_com env (Seq c1 c2) l) 
let seq_com _ _ _ _ c1_ni c2_ni tu = let _ = c1_ni tu in c2_ni tu

(* Conditional rule for commands

         env |- e : l   env,pc:l |- ct   env,pc:l |- cf
         ----------------------------------------------
             env,pc:l |- if e <> 0 then ct else cf
*)
val cond_com : env:label_fun -> e:exp -> ct:com -> cf:com -> l:label 
  -> =e_ni:(ni_exp env e l) -> =ct_ni:(ni_com env ct l) -> =cf_ni:(ni_com env cf l) 
  -> Tot (ni_com env (If e ct cf) l)
let cond_com _ _ _ _ _ e ct cf tu =
  match e tu with
  | R 0 0 -> cf tu
  | R 0 _ -> cross cf ct
  | R _ 0 -> cross ct cf
  | R _ _ -> ct tu


(* Typing rule for Skip

         -------------------
         env,pc:High |- skip
*)

val skip_com : env:label_fun -> Tot (ni_com env Skip High)
let skip_com _ tu = tu


(* Loop case of a while loop *)
val loop_loop : env:label_fun -> e:exp -> c:com -> v:variant -> l:label 
  -> =e_ni:(ni_exp env e l) -> =c_ni:(ni_com env c l) -> 
  // Tot (ni_com env (While e c v) l) (* This fails because of bug #379 *)
  double unit -> ST2 (double unit)
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
              (forall r.
                 env r < l
                  ==>   sel (R.l h0) r = sel (R.l h1) r
                    /\ sel (R.r h0) r = sel (R.r h1) r)
                /\ Let (interpret_com (R.l h0) c) (fun o -> 
                    is_Some o ==> 
                    Let (interpret_com (Some.v o) (While e c v)) (fun o -> 
                      is_Some o ==> equal (Some.v o) (R.l h1)))
                /\ Let (interpret_com (R.r h0) c) (fun o -> 
                    is_Some o ==> 
                    Let (interpret_com (Some.v o) (While e c v)) (fun o -> 
                      is_Some o ==> equal (Some.v o) (R.r h1)))
                /\ (low_equiv env h0 ==> low_equiv env h1)))

(* While rule for commands

         env |- e : l          env,pc:l |- c
         -----------------------------------
          env,pc:l |- while (e <> 0) do c
*)
val loop_com : env:label_fun -> e:exp -> c:com -> v:variant -> l:label 
  -> =e_ni:ni_exp env e l -> =c_ni:ni_com env c l -> 
  // Tot (ni_com env (While e c v) l) (* This fails because of bug #379 *)
  double unit -> ST2 (double unit)
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 ->
              (forall r.
                 env r < l
                  ==>   sel (R.l h0) r = sel (R.l h1) r
                    /\ sel (R.r h0) r = sel (R.r h1) r)
                /\ Let (interpret_com (R.l h0) (While e c v)) (fun o -> 
                    is_Some o ==> equal (Some.v o) (R.l h1))
                /\ Let (interpret_com (R.r h0) (While e c v)) (fun o -> 
                    is_Some o ==> equal (Some.v o) (R.r h1))
                /\ (low_equiv env h0 ==> low_equiv env h1)))

let rec loop_com env e c v l e_ni c_ni tu = 
  match e_ni tu with
  | R 0 0 -> skip_com env tu
  | R 0 _ -> cross (skip_com env) (loop_loop env e c v l e_ni c_ni)
  | R _ 0 -> cross (loop_loop env e c v l e_ni c_ni) (skip_com env)
  | R _ _ -> loop_loop env e c v l e_ni c_ni tu
and loop_loop env e c v l e_ni c_ni tu = 
  (let _ = c_ni tu in loop_com env e c v l e_ni c_ni) tu


(* Typechecking expressions: we infer the label *)
val tc_exp : env:label_fun -> e:exp -> Tot (l:label & ni_exp env e l)
let rec tc_exp env e = 
  match e with 
  | AInt i -> (| Low, (aint_exp env i) |)
  | AVar r -> (| env r, (avar_exp env r) |) 
  | AOp op e1 e2 -> 
    (* This style triggers a lot of weird bugs... *)
    (* let r1, r2 = tc_exp e1, tc_exp e2 in  *)
    let r1 = tc_exp env e1 in
    let r2 = tc_exp env e2 in 
    let (| l1, p1 |) = r1 in 
    let (| l2, p2 |) = r2 in 
    let l = if l1 <= l2 then l2 else l1 in
    let s1 = sub_exp env e1 l1 l p1 in 
    let s2 = sub_exp env e2 l2 l p2 in 
    (| l, binop_exp env op e1 e2 l s1 s2 |)



(* Typechecking commands: we typecheck in a given context *)
val tc_com : env:label_fun -> l:label -> c:com -> Tot (option (ni_com env c l)) (decreases c)
let rec tc_com env l c = 
  match c with 

  | Skip -> Some (sub_com env c High l (skip_com env))

  | Assign x e -> 
    let lx = env x in 
    if l <= lx then
      let (| l', ni_e |) = tc_exp env e in 
      if l' <= lx then 
        let ni_e' = sub_exp env e l' lx ni_e in 
        let ni_as = assign_com env e x ni_e' in 
        Some (sub_com env c lx l ni_as)
      else
        None
    else
      None

  | Seq c1 c2 ->
    let r1 = tc_com env l c1 in   
    let r2 = tc_com env l c2 in 
    if is_None r1 || is_None r2 then
      None
    else
      Some (seq_com env c1 c2 l (Some.v r1) (Some.v r2))

  | If e ct cf -> 
    let (| l1', r1' |) = tc_exp env e in
    let l1 = if l1' <= l then l else l1' in 
    let r1 = sub_exp env e l1' l1 r1' in
    let r2 = tc_com env l1 ct in 
    let r3 = tc_com env l1 cf in 
    if is_None r2 || is_None r3 then
      None
    else
      let s = cond_com env e ct cf l1 r1 (Some.v r2) (Some.v r3) in 
      Some (sub_com env c l1 l s)

  | While e cb v -> 
    let (| l1', r1' |) = tc_exp env e in
    let l1 = if l1' <= l then l else l1' in 
    let r1 = sub_exp env e l1' l1 r1' in
    let r2 = tc_com env l1 cb in 
    if is_None r2 then 
      None
    else
      let s = loop_com env e cb v l1 r1 (Some.v r2) in
      Some (sub_com env (While e cb v) l1 l s)
      

val tc : env:label_fun -> c:com -> option (ni env c)
let tc env c = tc_com env Low c
