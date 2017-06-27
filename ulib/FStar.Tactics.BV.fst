module FStar.Tactics.BV

open FStar.Tactics
open FStar.Reflection.Syntax
open FStar.Reflection.Int

(* Lemmas transforming integer arithmetic to bitvector arithmetic *)
val nat_to_bv_land : (#n:pos) -> (#x:int) -> (#y:int) -> (#z:bv_t n) ->
			    squash (logand_vec (nat_to_bv x) (nat_to_bv y) == z) ->
			    Lemma (nat_to_bv (logand #n x y) == z)
let nat_to_bv_land #n #x #y #z = ()

(*
assume val nat_to_bv_lxor : (#x:Machine.nat64) -> (#y:Machine.nat64) -> (#z:bv64) ->
			    squash (logxor_vec (nat_to_bv x) (nat_to_bv y) == z) ->
			    Lemma (nat_to_bv (logxor64 x y) == z)

assume val nat_to_bv_shl : (#x:Machine.nat64) -> (#y:Machine.nat64) -> (#z:bv64) ->
			    squash (shift_left_vec (nat_to_bv x) y == z) ->
			    Lemma (nat_to_bv (shift_left64 x y) == z)

assume val nat_to_bv_shr : (#x:Machine.nat64) -> (#y:Machine.nat64) -> (#z:bv64) ->
			    squash (shift_right_vec (nat_to_bv x) y == z) ->
			    Lemma (nat_to_bv (shift_right64 x y) == z)

(* Congruence lemmas used to push integer to bitvector transformations through arguments of expressions *)
assume val cong_logand_vec : (#w:bv64) -> (#x:bv64) -> 
			     (#y:bv64) -> (#z:bv64) ->
			     squash (w == y) -> squash (x == z) ->
			     Lemma (logand_vec w x == logand_vec y z)

assume val cong_logxor_vec : (#w:bv64) -> (#x:bv64) -> 
			     (#y:bv64) -> (#z:bv64) ->
			     squash (w == y) -> squash (x == z) ->
			     Lemma (logxor_vec w x == logxor_vec y z)

assume val cong_shift_left_vec : (#w:bv64) -> (#x:nat) -> 
				 (#y:bv64) -> squash (w == y) ->
				 Lemma (shift_left_vec w x == shift_left_vec y x)

assume val cong_shift_right_vec : (#w:bv64) -> (#x:nat) -> 
				  (#y:bv64) -> squash (w == y) ->
				  Lemma (shift_right_vec w x == shift_right_vec y x)


(* Used to reduce the initial equation to an equation on bitvectors*)
assume val eq_to_bv: (#x:Machine.nat64) -> (#y:Machine.nat64) ->
                    squash (nat_to_bv x == nat_to_bv y) -> Lemma (x == y)

(* Creates two fresh variables and two equations of the form nat_to_bv
   x = z /\ nat_to_bv y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *) 
assume val trans: (#x:bv64) -> (#y:bv64) -> (#z:bv64) -> (#w:bv64) -> 
		  squash (x == z) -> squash (y == w) -> squash (z == w) -> 
		  Lemma (x == y)


let rec arith_to_bv_tac : unit -> Tac unit = fun () -> (

    let rec arith_expr_to_bv e =
      match e with
      // // | Land (Atom _ _) (Atom _ _)
      // | Land (Lit _) (Lit _) ->
      // 	apply_lemma (quote nat_to_bv_land) 

      | NatToBv (Shl e1 _) | Shl e1 _ ->
	apply_lemma (quote nat_to_bv_shl);;
	apply_lemma (quote cong_shift_left_vec);;
	arith_expr_to_bv e1
      | NatToBv (Shr e1 _) | Shr e1 _ ->
	apply_lemma (quote nat_to_bv_shr);;
	apply_lemma (quote cong_shift_right_vec);;
	arith_expr_to_bv e1
      | NatToBv (Land e1 e2) | (Land e1 e2) ->
	apply_lemma (quote nat_to_bv_land);;
	apply_lemma (quote cong_logand_vec);;
	arith_expr_to_bv e1;;
	arith_expr_to_bv e2
      | NatToBv (Lxor e1 e2) | (Lxor e1 e2) ->
	apply_lemma (quote nat_to_bv_lxor);;
	apply_lemma (quote cong_logxor_vec);;
	arith_expr_to_bv e1;;
	arith_expr_to_bv e2
      | _ -> trefl
    in

    norm [Simpl];;
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
    ) ()

(* As things are right now, we need to be able to parse NatToBv
too. This can be useful, if we have mixed expressions so I'll leave it
as is for now *)
let bv_tac ()  =
	   apply_lemma (quote eq_to_bv);;
	   apply_lemma (quote trans);;
	   arith_to_bv_tac;;
	   arith_to_bv_tac;;
	   // norm [Delta; Simpl; Primops];; dump "final";;
	   smt ()
*)
