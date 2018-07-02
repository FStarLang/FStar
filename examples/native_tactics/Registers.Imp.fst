module Registers.Imp
//#set-options "--debug Imp --debug_level SMTQuery"
open FStar.Mul
module R = Registers.List

type rval   = int
type reg_t  = x:nat{x<=10}
type regmap = R.regmap rval

noeq
type inst =
    | Add : reg_t -> reg_t -> reg_t -> inst
    | Sub : reg_t -> reg_t -> reg_t -> inst
    | Mul : reg_t -> reg_t -> reg_t -> inst
    | Const : rval -> reg_t -> inst
    | If0 : reg_t -> prog -> prog -> inst
    | Seq : prog -> inst
and prog = list inst

module L = FStar.List.Tot

let rec size : inst -> pos = function
  | Add _ _ _
  | Sub _ _ _
  | Mul _ _ _
  | Const _ _  -> 1
  | If0 _ i j -> 1 + size_l i + size_l j
  | Seq i -> 1 + size_l i
and size_l : prog -> pos = function
  | [] -> 1
  | hd::tl -> size hd + size_l tl
  
let rec eval' (i:inst) (rm:regmap)
    : Tot regmap (decreases (size i))
    = match i with
      | Add r1 r2 r3 -> R.upd rm r3 (R.sel rm r1 + R.sel rm r2)
      | Sub r1 r2 r3 -> R.upd rm r3 (R.sel rm r1 - R.sel rm r2)
      | Mul r1 r2 r3 -> R.upd rm r3 (R.sel rm r1 * R.sel rm r2)
      | Const v r    -> R.upd rm r v
      | Seq []       -> rm
      | Seq (p::ps)   -> eval' (Seq ps) (eval' p rm)
      | If0 r p0 p1  ->
          if R.sel rm r = 0 
          then eval' (Seq p0) rm
          else eval' (Seq p1) rm

(* Run in all zeros and get the 0th reg *)
val eval : prog -> rval
let eval p = let rm = eval' (Seq p) (R.create 0) in R.sel rm 0

irreducible
let unfold_defs = ()

unfold
let normal #a (e:a) =
  FStar.Pervasives.norm 
           [zeta;
            iota;
            delta_only [`%eval; `%eval'; `%R.upd; `%R.sel; `%R.eta_map; `%L.append; `%FStar.Mul.op_Star]; 
            delta_attr unfold_defs; 
            primops// ;
            // nbe
  ] e

let norm_assert (p:Type) : Lemma (requires (normal p)) (ensures p) = ()

[@unfold_defs]
let reg x = x

let equiv p1 p2 =
  (forall rm. 
     let rm = R.eta_map 10 rm in
     forall (r:reg_t). R.sel (eval' (Seq p1) rm) r 
               == R.sel (eval' (Seq p2) rm) r)

[@unfold_defs]
let all_equiv (rm1 rm2:regmap) =
    let rec aux (r:reg_t) =
      R.sel rm1 r == R.sel rm2 r /\
      (if r = 0 then True
       else aux (r - 1))
    in
    aux 10

[@unfold_defs]
let equiv_norm p1 p2 =
    (forall rm. 
     let rm = R.eta_map 10 rm in
     all_equiv (eval' (Seq p1) rm)
               (eval' (Seq p2) rm))

////////////////////////////////////////////////////////////////////////////////
// Sample programs
////////////////////////////////////////////////////////////////////////////////
[@unfold_defs]
let add1 x y : prog = [
    Const x (reg 0);
    Const y (reg 1);
    Add (reg 0) (reg 1) (reg 0);
]

[@unfold_defs]
let add2 x y : prog = [
    Const y (reg 1);
    Const x (reg 0);
    Add (reg 0) (reg 1) (reg 0);
]
    
[@unfold_defs]
let add3 x y : prog = [
    Const x (reg 0);
    Const y (reg 1);
    Add (reg 1) (reg 0) (reg 0);
]
    
[@unfold_defs]
let add4 x y : prog = [
    Const y (reg 1);
    Const x (reg 0);
    Add (reg 1) (reg 0) (reg 0);
]

[@unfold_defs]
let x_times_42 x : prog = [
    Const x (reg 0);
    Add (reg 0) (reg 0) (reg 1); //2x
    Add (reg 1) (reg 1) (reg 0); //4x
    Add (reg 0) (reg 0) (reg 1); //8x
    Add (reg 1) (reg 1) (reg 0); //16x
    Add (reg 0) (reg 0) (reg 1); //32x
    Add (reg 1) (reg 0) (reg 0); //48x
    Const 6 (reg 1);
    Const x (reg 2);             
    Mul (reg 1) (reg 2) (reg 1); //6x
    Sub (reg 0) (reg 1) (reg 0); //42x
]

[@unfold_defs]
let long_zero x : prog =
    let l = x_times_42 x in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in
    let l = l `L.append` l in    
    l `L.append` 
    [Const 0 (reg 0); Const 0 (reg 1); Const 0 (reg 2)]

#set-options "--debug Registers.Imp --debug_level print_normalized_terms"
let _ = norm_assert (forall x y. equiv_norm (long_zero x) (long_zero y))
#reset-options "--max_fuel 0"
let _ = norm_assert (forall x. eval (x_times_42 x) == 42 * x)


(* All of these identies are quite easy by normalization. *)
let _ = norm_assert (forall x y. equiv_norm (add1 x y) (add2 x y))
let _ = norm_assert (forall x y. equiv_norm (add1 x y) (add3 x y))
let _ = norm_assert (forall x y. equiv_norm (add1 x y) (add4 x y))
let _ = norm_assert (forall x y. equiv_norm (add2 x y) (add3 x y))
let _ = norm_assert (forall x y. equiv_norm (add2 x y) (add4 x y))
let _ = norm_assert (forall x y. equiv_norm (add3 x y) (add4 x y))


(* Without normalizing, they require fuel, or else fail *)
[@Pervasives.fail] let _ = assert (forall x y. equiv (add1 x y) (add2 x y))
[@Pervasives.fail] let _ = assert (forall x y. equiv (add1 x y) (add3 x y))
[@Pervasives.fail] let _ = assert (forall x y. equiv (add1 x y) (add4 x y))
[@Pervasives.fail] let _ = assert (forall x y. equiv (add2 x y) (add3 x y))
[@Pervasives.fail] let _ = assert (forall x y. equiv (add2 x y) (add4 x y))
[@Pervasives.fail] let _ = assert (forall x y. equiv (add3 x y) (add4 x y))

(* poly5 x = x^5 + x^4 + x^3 + x^2 + x^1 + 1 *)

[@unfold_defs]
let poly5 x : prog = [
    Const 1 (reg 0);
    Const x (reg 1);
    Mul (reg 1) (reg 1) (reg 2);
    Mul (reg 1) (reg 2) (reg 3);
    Mul (reg 1) (reg 3) (reg 4);
    Mul (reg 1) (reg 4) (reg 5);
    Add (reg 0) (reg 1) (reg 0);
    Add (reg 0) (reg 2) (reg 0);
    Add (reg 0) (reg 3) (reg 0);
    Add (reg 0) (reg 4) (reg 0);
    Add (reg 0) (reg 5) (reg 0);
]

let _ = norm_assert (eval (poly5 1) == 6)
let _ = norm_assert (eval (poly5 2) == 63)
let _ = norm_assert (eval (poly5 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)

(* Bunch of fuel to even prove ground facts *)
#reset-options "--initial_fuel 20 --max_fuel 20"
let _ = assert (eval (poly5 1) == 6)
let _ = assert (eval (poly5 2) == 63)
let _ = assert (eval (poly5 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
#reset-options "--max_fuel 0"

(* A different way of computing it *)
[@unfold_defs]
let poly5' x : prog = [
    Const 1 (reg 0);
    Const x (reg 1);
    Const 1 (reg 2);
    Mul (reg 0) (reg 1) (reg 0);
    Add (reg 0) (reg 2) (reg 0);
    Mul (reg 0) (reg 1) (reg 0);
    Add (reg 0) (reg 2) (reg 0);
    Mul (reg 0) (reg 1) (reg 0);
    Add (reg 0) (reg 2) (reg 0);
    Mul (reg 0) (reg 1) (reg 0);
    Add (reg 0) (reg 2) (reg 0);
    Mul (reg 0) (reg 1) (reg 0);
    Add (reg 0) (reg 2) (reg 0);
]

(* Seems to do the same *)
let _ = norm_assert (eval (poly5' 1) == 6)
let _ = norm_assert (eval (poly5' 2) == 63)
let _ = norm_assert (eval (poly5' 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
let _ = norm_assert (forall x. eval (poly5 x) == eval (poly5' x))

(* Same *)
#reset-options "--initial_fuel 20 --max_fuel 20"
let _ = assert (eval (poly5' 1) == 6)
let _ = assert (eval (poly5' 2) == 63)
let _ = assert (eval (poly5' 3) == 3*3*3*3*3 + 3*3*3*3 + 3*3*3 + 3*3 + 3 + 1)
let _ = assert (forall x. (eval (poly5 x) == eval (poly5' x)))
#reset-options "--max_fuel 0"

//--------------------------------------------------------------------------------

// open FStar.Tactics
// open CanonCommSemiring
// open FStar.Algebra.CommMonoid

// [@Pervasives.fail]
// let _ = assert (forall x. poly5 x `equiv` poly5' x)

// #set-options "--z3rlimit 10"
// let _ = assert_norm (forall x. (poly5 (eval (poly5 x)) `equiv` poly5' (eval (poly5' x))))

// #set-options "--max_fuel 0"
// // --tactic_trace"
// let _ = assert (forall x. poly5 x `equiv` poly5' x)
//           by (fun () -> let _ = forall_intros () in
// 		     compute ();
// 		     dump "after norm";
// 		     canon_semiring int_cr;
// 		     dump "final")

// Takes long.. try again later
//let _ = assert (forall x. (poly5 (eval (poly5 x)) `equiv` poly5' (eval (poly5' x))))
//          by (fun () -> let _ = forall_intros () in
//		     compute ();
//		     dump "after norm";
//		     canon_semiring int_cr;
//		     dump "final")
//    
