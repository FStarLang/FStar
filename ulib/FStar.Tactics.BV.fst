module FStar.Tactics.BV

open FStar.Tactics
open FStar.Reflection.Syntax
open FStar.Reflection.Arith
open FStar.BV

(* Congruence lemmas *)
val cong_bvand : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) -> 
			       (#y:bv_t n) -> (#z:bv_t n) ->
			       squash (w == y) -> squash (x == z) ->
			       Lemma (bvand w x == bvand y z)
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

val cong_bvshl : #n:pos -> (#w:bv_t n) -> (#x:uint_t' n) -> 
				 (#y:bv_t n) -> squash (w == y) ->
				 Lemma (bvshl w x == bvshl y x)
let cong_bvshl #n #w #x #y pf = ()

val cong_bvshr : #n:pos -> #w:bv_t n -> (#x:uint_t' n) -> 
			   #y:bv_t n -> squash (w == y) ->
			   Lemma (bvshr #n w x == bvshr #n y x)
let cong_bvshr #n #w #x #y pf = ()

val cong_bvdiv : #n:pos -> #w:bv_t n -> (#x:uint_t' n{x <> 0}) -> 
			  #y:bv_t n -> squash (w == y) ->
			   Lemma (bvdiv #n w x == bvdiv #n y x)
let cong_bvdiv #n #w #x #y pf = ()

(* Used to reduce the initial equation to an equation on bitvectors*)
val eq_to_bv: #n:pos -> (#x:uint_t' n) -> (#y:uint_t' n) ->
              squash (int2bv #n x == int2bv #n y) -> Lemma (x == y)
let eq_to_bv #n #x #y pf = int2bv_lemma_2 #n x y

(* Creates two fresh variables and two equations of the form int2bv
   x = z /\ int2bv y = w. The above lemmas transform these two
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
    | NatToBv _ (Udiv _ e1 _) | Udiv _ e1 _ ->
        apply_lemma (quote int2bv_div);;
        apply_lemma (quote cong_bvdiv);;
        arith_expr_to_bv e1
    | NatToBv _ (Shl _ e1 _) | Shl _ e1 _ ->
        apply_lemma (quote int2bv_shl);;
        apply_lemma (quote cong_bvshl);;
        arith_expr_to_bv e1
    | NatToBv _ (Shr _ e1 _) | Shr _ e1 _ ->
        apply_lemma (quote int2bv_shr);;
	dump "after int2bv_Shr";;
        apply_lemma (quote cong_bvshr);;
	dump "after cong_bvshr";;
        arith_expr_to_bv e1
    | NatToBv _ (Land _ e1 e2) | (Land _ e1 e2) ->
        apply_lemma (quote int2bv_logand);;
        apply_lemma (quote cong_bvand);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2
    | NatToBv _ (Lxor _ e1 e2) | (Lxor _ e1 e2) ->
        apply_lemma (quote int2bv_logxor);;
        apply_lemma (quote cong_bvxor);;
        arith_expr_to_bv e1;;
        arith_expr_to_bv e2
    | NatToBv _ (Lor _ e1 e2) | (Lor _ e1 e2) ->
        apply_lemma (quote int2bv_logor);;
        apply_lemma (quote cong_bvor);;
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
      dump "inl";;
        trefl
      | Inr e ->
      dump "before seq";;
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
  dump "after trans";;
  arith_to_bv_tac;;
  arith_to_bv_tac;;
  set_options "--smtencoding.elim_box true";;
  smt ()

