module FStar.Tactics.BV

open FStar.Tactics
open FStar.Reflection.Syntax
open FStar.Reflection.Arith
open FStar.BV
open FStar.UInt
// using uint_t' instead of uint_t breaks the tactic (goes to inl).

(* Congruence lemmas *)
val cong_bvand : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (bvand #n w x == bvand #n y z)
let cong_bvand #n #w #x #y #z pf1 pf2 = ()

val cong_bvxor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (bvxor w x == bvxor y z)
let cong_bvxor #n #w #x #y #z pf1 pf2 = ()

val cong_bvor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (bvor w x == bvor y z)
let cong_bvor #n #w #x #y #z pf1 pf2 = ()

val cong_bvshl : #n:pos -> (#w:bv_t n) -> (#x:uint_t n) -> 
				 (#y:bv_t n) -> squash (w == y) ->
				 Lemma (bvshl w x == bvshl y x)
let cong_bvshl #n #w #x #y pf = ()

val cong_bvshr : #n:pos -> #w:bv_t n -> (#x:uint_t n) -> 
			   #y:bv_t n -> squash (w == y) ->
			   Lemma (bvshr #n w x == bvshr #n y x)
let cong_bvshr #n #w #x #y pf = ()

val cong_bvdiv : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) -> 
			  #y:bv_t n -> squash (w == y) ->
			   Lemma (bvdiv #n w x == bvdiv #n y x)
let cong_bvdiv #n #w #x #y pf = ()

val cong_bvmod : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) -> 
			  #y:bv_t n -> squash (w == y) ->
			   Lemma (bvmod #n w x == bvmod #n y x)
let cong_bvmod #n #w #x #y pf = ()

val cong_bvmul : #n:pos -> #w:bv_t n -> (#x:uint_t n) -> 
			  #y:bv_t n -> squash (w == y) ->
			   Lemma (bvmul #n w x == bvmul #n y x)
let cong_bvmul #n #w #x #y pf = ()

(* Used to reduce the initial equation to an equation on bitvectors*)
val eq_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              squash (int2bv #n x == int2bv #n y) -> Lemma (x == y)
let eq_to_bv #n #x #y pf = int2bv_lemma_2 #n x y

val lt_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              (b2t (bvult #n (int2bv #n x) (int2bv #n y))) -> Lemma (x < y)
let lt_to_bv #n #x #y pf = int2bv_lemma_ult_2 #n x y

(* Creates two fresh variables and two equations of the form int2bv
   x = z /\ int2bv y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *) 
val trans: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) -> 
		  squash (x == z) -> squash (y == w) -> squash (z == w) -> 
		  Lemma (x == y)
let trans #n #x #y #z #w pf1 pf2 pf3 = ()

val trans_lt: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) -> 
		  (eq2 #(bv_t n) x z) -> (eq2 #(bv_t n) y w) -> squash (bvult #n z w) -> 
		  Lemma (bvult #n x y)
let trans_lt #n #x #y #z #w pf1 pf2 pf3 = ()

assume val trans_lt2: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) -> (#w:bv_t n) -> 
		  squash (int2bv #n x == z) -> squash (int2bv #n y == w) -> (b2t (bvult #n z w)) -> 
		  Lemma (x < y)
// let trans_lt2 #n #x #y #z #w pf1 pf2 pf3 = ()

(*
 * This is being proven terminating.
 * If that's not desirable, unfold `tactic` to go into a non-total effect
 *)
let rec arith_expr_to_bv e : tactic unit =
    match e with
    | NatToBv (MulMod e1 _) | MulMod e1 _ ->
        apply_lemma (quote int2bv_mul);;
        apply_lemma (quote cong_bvmul);;
        arith_expr_to_bv e1
    | NatToBv (Umod e1 _) | Umod e1 _ ->
        apply_lemma (quote int2bv_mod);;
        apply_lemma (quote cong_bvmod);;
        arith_expr_to_bv e1
    | NatToBv (Udiv e1 _) | Udiv e1 _ ->
        apply_lemma (quote int2bv_div);;
        apply_lemma (quote cong_bvdiv);;
        arith_expr_to_bv e1
    | NatToBv (Shl e1 _) | Shl e1 _ ->
        apply_lemma (quote int2bv_shl);;
        apply_lemma (quote cong_bvshl);;
        arith_expr_to_bv e1
    | NatToBv (Shr e1 _) | Shr e1 _ ->
        apply_lemma (quote int2bv_shr);;
        apply_lemma (quote cong_bvshr);;
        arith_expr_to_bv e1
    | NatToBv (Land e1 e2) | (Land e1 e2) ->
        apply_lemma (quote int2bv_logand);;
        apply_lemma (quote cong_bvand);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2
    | NatToBv (Lxor e1 e2) | (Lxor e1 e2) ->
        apply_lemma (quote int2bv_logxor);;
        apply_lemma (quote cong_bvxor);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2
    | NatToBv (Lor e1 e2) | (Lor e1 e2) ->
        apply_lemma (quote int2bv_logor);;
        apply_lemma (quote cong_bvor);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2	
    | _ ->
        trefl

let arith_to_bv_tac : tactic unit =
    // norm [simpl];;
    g <-- cur_goal;
    let f = term_as_formula g in
    match f with
    | Comp Eq t l r ->
     begin match run_tm (is_arith_expr l) with
      | Inl s ->
    	  dump s;;
          trefl
      | Inr e ->
    	    // dump "inr arith_to_bv";;
            seq (arith_expr_to_bv e) trefl
        end
    | _ ->
        fail ("impossible: ")

// let get_field_size_prop () : tactic int =
//   g <-- cur_goal;
//   let f = term_as_formula g in
//   match f with
//   | Comp Eq t l r | Comp Lt t l r ->
//   begin match run_tm (get_field_size l) with
//     | Inl s -> 
//       begin
//       match run_tm (get_field_size r) with
//       | Inl s' -> fail ("could not infer field size")
//       | Inr n -> n
//       end
//     | Inr n -> n
//   end
//   | _ -> fail ("impossible: ")

(* As things are right now, we need to be able to parse NatToBv
too. This can be useful, if we have mixed expressions so I'll leave it
as is for now *)
let bv_tac ()  =
  apply_lemma (quote eq_to_bv);;
  apply_lemma (quote trans);;
  arith_to_bv_tac;;
  arith_to_bv_tac;;
  set_options "--smtencoding.elim_box true";;
  smt

let bv_tac_lt n =
  // apply_lemma (quote (lt_to_bv #n));;
  // dump "after lt_to_bv";;
  apply_lemma (quote (trans_lt2 #n));;  
  arith_to_bv_tac;;
  arith_to_bv_tac;;
  set_options "--smtencoding.elim_box true";;
  smt

let to_bv_tac ()  =
  apply_lemma (quote eq_to_bv);;
  apply_lemma (quote trans);;
  arith_to_bv_tac;;
  arith_to_bv_tac
