module ProgramOptimizations

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed

(*
 * language and examples from:
 * "Simple Relational Correctness Proofs for Static Analyses and Program Transformations"
 * https://research.microsoft.com/en-us/um/people/nick/correctnesspopl2004.pdf
 *)

type var = id

type i_op =
  | Add
  | Sub

type i_exp =
  | Const : int -> i_exp
  | Var   : id -> i_exp
  | IOp   : i_op -> i_exp -> i_exp -> i_exp
  | UMinus: i_exp -> i_exp

type r_op =
  | Lt
  | Gt
  | Eq

type b_op =
  | And
  | Or

type b_exp =
  | CTrue : b_exp
  | CFalse: b_exp
  | ROp   : r_op -> i_exp -> i_exp -> b_exp
  | BOp   : b_op -> b_exp -> b_exp -> b_exp
  | Not   : b_exp -> b_exp

type com =
  | Skip  : com
  | Assign: var -> i_exp -> com
  | Seq   : com -> com -> com
  | If    : b_exp -> com -> com -> com

 let rec i_exp_denotation (e:i_exp) :ISNull int =
  match e with
  | Const n      -> n
  | Var r        -> !r
  | IOp op e1 e2 ->
    (let n1 = i_exp_denotation e1 in
     let n2 = i_exp_denotation e2 in
     match op with
     | Add -> n1 + n2
     | Sub -> n1 - n2)
  | UMinus e     -> - (i_exp_denotation e)

 let rec b_exp_denotation (b:b_exp) :ISNull bool =
  match b with
  | CTrue        -> true
  | CFalse       -> false
  | ROp op e1 e2 ->
    let n1 = i_exp_denotation e1 in
    let n2 = i_exp_denotation e2 in
    (match op with
     | Lt -> n1 < n2
     | Gt -> n1 > n2
     | Eq -> n1 = n2)
  | BOp op b1 b2 ->
    let bc1 = b_exp_denotation b1 in
    let bc2 = b_exp_denotation b2 in
    (match op with
     | And -> bc1 && bc2
     | Or  -> bc1 || bc2)
  | Not b -> not (b_exp_denotation b)

 let rec com_denotation (c:com) :ISNull unit =
  match c with
  | Skip       -> ()
  | Assign r e ->
    let n = i_exp_denotation e in
    write r n  (* r := n does not work, as it goes to FStar.ST *)
  | Seq c1 c2  -> com_denotation c1; com_denotation c2
  | If b c1 c2 ->
    if b_exp_denotation b then com_denotation c1 else com_denotation c2

type g_exp =
  | GConst: int -> g_exp
  | Left  : id -> g_exp
  | Right : id -> g_exp
  | GIOp  : i_op -> g_exp -> g_exp -> g_exp

type rel_exp =
  | RTrue : rel_exp
  | RFalse: rel_exp
  | RROp  : r_op -> g_exp -> g_exp -> rel_exp
  | RBOp  : b_op -> rel_exp -> rel_exp -> rel_exp
  | RNot  : rel_exp -> rel_exp

let rec g_exp_denotation (g:g_exp) (h_left:heap) (h_right:heap) :int =
  match g with
  | GConst n      -> n
  | Left r        -> sel h_left r
  | Right r       -> sel h_right r
  | GIOp op g1 g2 ->
    match op with
    | Add -> g_exp_denotation g1 h_left h_right + g_exp_denotation g2 h_left h_right
    | Sub -> g_exp_denotation g1 h_left h_right - g_exp_denotation g2 h_left h_right

let rec rel_exp_denotation (re:rel_exp) (h_left:heap) (h_right:heap) :bool =
  match re with
  | RTrue         -> true
  | RFalse        -> false
  | RROp op g1 g2 ->
    let n1 = g_exp_denotation g1 h_left h_right in
    let n2 = g_exp_denotation g2 h_left h_right in
    (match op with
     | Lt -> n1 < n2
     | Gt -> n1 > n2
     | Eq -> n1 = n2)
  | RBOp op re1 re2 ->
    let bc1 = rel_exp_denotation re1 h_left h_right in
    let bc2 = rel_exp_denotation re2 h_left h_right in
    (match op with
     | And -> bc1 && bc2
     | Or  -> bc1 || bc2)
  | RNot re1 -> not (rel_exp_denotation re1 h_left h_right)

assume val x:id
assume val y:id
assume val z:id

assume Distinct_vars: x <> y /\ y <> z /\ x <> z

(*
 * removing redundant computation
 * proving com1 = x := y + 1; z := y + 1
 *     and com2 = x := y + 1; z := x
 *
 * relate two states with equal values of y to two states with equal values of x and z
 *)
let com11 = Seq (Assign x (IOp Add (Var y) (Const 1)))  //x := y + 1;
                (Assign z (IOp Add (Var y) (Const 1)))  //z := y + 1
let com12 = Seq (Assign x (IOp Add (Var y) (Const 1)))  //x := y + 1;
                (Assign z (Var x))                      //z := x

let rel11 = RROp Eq (Left y) (Right y)  //Left y = Right y
let rel12 = RBOp And (RROp Eq (Left x) (Right x))  //Left x = Right x /\
                     (RROp Eq (Left z) (Right z))  //Left z = Right z

let lemma_sound_optimization1 (h_left:heap) (h_right:heap)
  :Lemma (requires (rel_exp_denotation rel11 h_left h_right))  //h_left, h_right are related by rel1
         (ensures  (let _, h_left'  = reify (com_denotation com11) h_left in
	            let _, h_right' = reify (com_denotation com12) h_right in
		    rel_exp_denotation rel12 h_left' h_right'))  //[|com1|](h_left), [|com2|](h_right) are related by rel2
  = ()

(*
 * dead code elimination
 * proving com1 = if x > 3 then y := x else y := 7
 *     and com2 = skip
 * are equivalent if all that the rest of the computation cares for is y > 2
 *)
let com21 = If (ROp Gt (Var x) (Const 3))
               (Assign y (Var x))
               (Assign y (Const 7))  //if x > 3 then y := x else y := 7
let com22 = Skip

let rel21 = RBOp And (RBOp And (RROp Eq (Left x) (Right x))  //Left x = Right x
                               (RROp Gt (Left y) (GConst 2)))  //Left y > 2
                     (RROp Gt (Right y) (GConst 2))  //Right y > 2
let rel22 = RBOp And (RROp Gt (Left y) (GConst 2))  //Left y > 2
                     (RROp Gt (Right y) (GConst 2))  //Right y > 2

let lemma_sound_optimization2 (h_left:heap) (h_right:heap)
  :Lemma (requires (rel_exp_denotation rel21 h_left h_right))
         (ensures  (let _, h_left' = reify (com_denotation com21) h_left in
	            let _, h_right' = reify (com_denotation com22) h_right in
		    rel_exp_denotation rel22 h_left' h_right'))
  = ()

(*
 * optimization
 * proving com1 = if x = 3 then y := x else y := 3
 *     and com2 = y := 3
 * are equivalent
 *)
let com31 = If (ROp Eq (Var x) (Const 3))
               (Assign y (Var x))
	       (Assign y (Const 3))  //if x = 3 then y := x else y := 3
let com32 = Assign y (Const 3)  //y := 3

let rel31 = RTrue
let rel32 = RBOp And (RROp Eq (Left y) (GConst 3))  //Left y = 3
                     (RROp Eq (Right y) (GConst 3))  //Right y = 3

let lemma_sound_optimization3 (h_left:heap) (h_right:heap)
  :Lemma (requires (rel_exp_denotation rel31 h_left h_right))
         (ensures  (let _, h_left' = reify (com_denotation com31) h_left in
	            let _, h_right' = reify (com_denotation com32) h_right in
		    rel_exp_denotation rel32 h_left' h_right'))
  = ()

(*
 * optimization
 * proving com1 = x := -y; z := z - x; x := -x
       and com2 = x := y; z := z + x
 * are equivalent
 *)
let com41 = Seq (Assign x (UMinus (Var y)))  //x := -y;
                (Seq (Assign z (IOp Sub (Var z) (Var x)))  //z := z - x;
		     (Assign x (UMinus (Var x))))  //x := -x
let com42 = Seq (Assign x (Var y))  //x := y;
                (Assign z (IOp Add (Var z) (Var x)))  //z := z + x

let rel4 = RBOp And (RROp Eq (Left x) (Right x))
                    (RBOp And (RROp Eq (Left y) (Right y))
    	                      (RROp Eq (Left z) (Right z)))

#set-options "--z3rlimit 20"
let lemma_sound_optimization4 (h_left:heap) (h_right:heap)
  :Lemma (requires (rel_exp_denotation rel4 h_left h_right))
         (ensures  (let _, h_left' = reify (com_denotation com41) h_left in
	            let _, h_right' = reify (com_denotation com42) h_right in
		    rel_exp_denotation rel4 h_left' h_right'))
  = ()
#reset-options

let rhl (c1:com) (c2:com) (re1:rel_exp) (re2:rel_exp) =
  forall (h_left:heap) (h_right:heap). rel_exp_denotation re1 h_left h_right ==>
                                  (let _, h_left' = reify (com_denotation c1) h_left in
				   let _, h_right' = reify (com_denotation c2) h_right in
				   rel_exp_denotation re2 h_left' h_right')

let lemma_r_cbl
  (c:com)
  (c':com)
  (d:com)
  (phi:rel_exp)
  (phi':rel_exp)
  : Lemma (requires (rhl c d phi phi'))
	  (ensures  (rhl (If CTrue c c') d phi phi'))	  
  = ()
