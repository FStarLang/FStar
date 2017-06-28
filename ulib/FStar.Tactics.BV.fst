module FStar.Tactics.BV

open FStar.Tactics
open FStar.Reflection.Syntax
open FStar.Reflection.Arith
open FStar.UInt
open FStar.BV

(* Lemmas transforming integer arithmetic to bitvector arithmetic *)
val to_vec_logand : (#n:pos) -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (logand_vec #n (to_vec #n x) (to_vec #n y) == z) ->
			    Lemma (to_vec #n (logand #n x y) == z)
let to_vec_logand #n #x #y #z pf =
  inverse_vec_lemma #n (logand_vec #n (to_vec x) (to_vec y));
  ()
  

val to_vec_logxor : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
		     squash (logxor_vec (to_vec x) (to_vec y) == z) ->
		     Lemma (to_vec (logxor x y) == z)
let to_vec_logxor #n #x #y #z pf =
  inverse_vec_lemma #n (logxor_vec #n (to_vec x) (to_vec y));
  ()

val to_vec_logor : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
		     squash (logor_vec (to_vec x) (to_vec y) == z) ->
		     Lemma (to_vec (logor x y) == z)
let to_vec_logor #n #x #y #z pf =
  inverse_vec_lemma #n (logor_vec #n (to_vec x) (to_vec y));
  ()

val to_vec_shl : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (shift_left_vec (to_vec x) y == z) ->
			    Lemma (to_vec (shift_left x y) == z)
let to_vec_shl #n #x #y #z pf =
  inverse_vec_lemma #n (shift_left_vec #n (to_vec x) y);			    
  ()
  
val to_vec_shr : #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) ->
			    squash (shift_right_vec (to_vec x) y == z) ->
			    Lemma (to_vec (shift_right x y) == z)
let to_vec_shr #n #x #y #z pf =
  inverse_vec_lemma #n (shift_right_vec #n (to_vec x) y);
  ()

(* Congruence lemmas used to push integer to bitvector transformations through arguments of expressions *)
val cong_logand_vec : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (logand_vec w x == logand_vec y z)
let cong_logand_vec #n #w #x #y #z pf1 pf2 = ()

val cong_logxor_vec : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (logxor_vec w x == logxor_vec y z)
let cong_logxor_vec #n #w #x #y #z pf1 pf2 = ()

val cong_logor_vec : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (logor_vec w x == logor_vec y z)
let cong_logor_vec #n #w #x #y #z pf1 pf2 = ()

val cong_shift_left_vec : #n:pos -> (#w:bv_t n) -> (#x:uint_t n) -> 
				 (#y:bv_t n) -> squash (w == y) ->
				 Lemma (shift_left_vec w x == shift_left_vec y x)
let cong_shift_left_vec #n #w #x #y pf = ()

val cong_shift_right_vec : #n:pos -> #w:bv_t n -> (#x:uint_t n) -> 
			   #y:bv_t n -> squash (w == y) ->
			   Lemma (shift_right_vec w x == shift_right_vec y x)
let cong_shift_right_vec #n #w #x #y pf = ()

(* Used to reduce the initial equation to an equation on bitvectors*)
val eq_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              squash (to_vec #n x == to_vec #n y) -> Lemma (x == y)
let eq_to_bv #n #x #y pf = to_vec_lemma_2 #n x y

(* Creates two fresh variables and two equations of the form to_vec
   x = z /\ to_vec y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *) 
val trans: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) -> 
		  squash (x == z) -> squash (y == w) -> squash (z == w) -> 
		  Lemma (x == y)
let trans #n #x #y #z #w pf1 pf2 pf3 = ()

(*
 * This is being proven terminating.
 * If that's not desirable, unfold `tactic` to go into a non-total effect
 *)
let rec arith_expr_to_bv e : tactic unit =
    match e with
    | NatToBv _ (Shl _ e1 _) | Shl _ e1 _ ->
        apply_lemma (quote to_vec_shl);;
        apply_lemma (quote cong_shift_left_vec);;
        arith_expr_to_bv e1
    | NatToBv _ (Shr _ e1 _) | Shr _ e1 _ ->
        apply_lemma (quote to_vec_shr);;
        apply_lemma (quote cong_shift_right_vec);;
        arith_expr_to_bv e1
    | NatToBv _ (Land _ e1 e2) | (Land _ e1 e2) ->
        apply_lemma (quote to_vec_logand);;
        apply_lemma (quote cong_logand_vec);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2
    | NatToBv _ (Lxor _ e1 e2) | (Lxor _ e1 e2) ->
        apply_lemma (quote to_vec_logxor);;
        apply_lemma (quote cong_logxor_vec);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2
    | NatToBv _ (Lor _ e1 e2) | (Lor _ e1 e2) ->
        apply_lemma (quote to_vec_logor);;
        apply_lemma (quote cong_logor_vec);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2	
    | _ ->
        trefl

let arith_to_bv_tac : tactic unit =
    // norm [Simpl];;
    g <-- cur_goal;
    let f = term_as_formula g in
    match f with
    | Comp Eq t l r ->
     begin match run_tm (is_arith_expr l) with
      | Inl s ->
        trefl
      | Inr e ->
            seq (arith_expr_to_bv e) trefl
	   //  arith_expr_to_bv e
        end
    | _ ->
        fail ("impossible: ")

(* As things are right now, we need to be able to parse NatToBv
too. This can be useful, if we have mixed expressions so I'll leave it
as is for now *)
let bv_tac ()  =
  apply_lemma (quote eq_to_bv);;
  apply_lemma (quote trans);;
  arith_to_bv_tac;;
  arith_to_bv_tac;;
  set_options "--smtencoding.elim_box true";;
  smt ()

