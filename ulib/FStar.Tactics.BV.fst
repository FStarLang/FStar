module FStar.Tactics.BV

open FStar.Tactics
open FStar.Reflection.Formula
open FStar.Reflection.Arith
open FStar.BV
open FStar.UInt

// using uint_t' instead of uint_t breaks the tactic (goes to inl).

(* Congruence lemmas *)
val cong_bvand: 
  #n: pos ->
  #w: bv_t n ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  squash (w == y) ->
  squash (x == z) ->
  Lemma (bvand #n w x == bvand #n y z)
let cong_bvand #n #w #x #y #z pf1 pf2 = ()

val cong_bvxor: 
  #n: pos ->
  #w: bv_t n ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  squash (w == y) ->
  squash (x == z) ->
  Lemma (bvxor w x == bvxor y z)
let cong_bvxor #n #w #x #y #z pf1 pf2 = ()

val cong_bvor: 
  #n: pos ->
  #w: bv_t n ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  squash (w == y) ->
  squash (x == z) ->
  Lemma (bvor w x == bvor y z)
let cong_bvor #n #w #x #y #z pf1 pf2 = ()

val cong_bvshl: #n: pos -> #w: bv_t n -> #x: uint_t n -> #y: bv_t n -> squash (w == y) ->
  Lemma (bvshl w x == bvshl y x)
let cong_bvshl #n #w #x #y pf = ()

val cong_bvshr: #n: pos -> #w: bv_t n -> #x: uint_t n -> #y: bv_t n -> squash (w == y) ->
  Lemma (bvshr #n w x == bvshr #n y x)
let cong_bvshr #n #w #x #y pf = ()

val cong_bvdiv: #n: pos -> #w: bv_t n -> #x: uint_t n {x <> 0} -> #y: bv_t n -> squash (w == y) ->
  Lemma (bvdiv #n w x == bvdiv #n y x)
let cong_bvdiv #n #w #x #y pf = ()

val cong_bvmod: #n: pos -> #w: bv_t n -> #x: uint_t n {x <> 0} -> #y: bv_t n -> squash (w == y) ->
  Lemma (bvmod #n w x == bvmod #n y x)
let cong_bvmod #n #w #x #y pf = ()

val cong_bvmul: #n: pos -> #w: bv_t n -> #x: uint_t n -> #y: bv_t n -> squash (w == y) ->
  Lemma (bvmul #n w x == bvmul #n y x)
let cong_bvmul #n #w #x #y pf = ()

val cong_bvadd: 
  #n: pos ->
  #w: bv_t n ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  squash (w == y) ->
  squash (x == z) ->
  Lemma (bvadd w x == bvadd y z)
let cong_bvadd #n #w #x #y #z pf1 pf2 = ()

val cong_bvsub: 
  #n: pos ->
  #w: bv_t n ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  squash (w == y) ->
  squash (x == z) ->
  Lemma (bvsub w x == bvsub y z)
let cong_bvsub #n #w #x #y #z pf1 pf2 = ()

(* Used to reduce the initial equation to an equation on bitvectors*)
val eq_to_bv: #n: pos -> #x: uint_t n -> #y: uint_t n -> squash (int2bv #n x == int2bv #n y) ->
  Lemma (x == y)
let eq_to_bv #n #x #y pf = int2bv_lemma_2 #n x y

val lt_to_bv: 
  #n: pos ->
  #x: uint_t n ->
  #y: uint_t n ->
  (b2t (bvult #n (int2bv #n x) (int2bv #n y))) ->
  Lemma (x < y)
let lt_to_bv #n #x #y pf = int2bv_lemma_ult_2 #n x y

(* Creates two fresh variables and two equations of the form int2bv
   x = z /\ int2bv y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *)
val trans: 
  #n: pos ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  #w: bv_t n ->
  squash (x == z) ->
  squash (y == w) ->
  squash (z == w) ->
  Lemma (x == y)
let trans #n #x #y #z #w pf1 pf2 pf3 = ()

val trans_lt: 
  #n: pos ->
  #x: bv_t n ->
  #y: bv_t n ->
  #z: bv_t n ->
  #w: bv_t n ->
  (eq2 #(bv_t n) x z) ->
  (eq2 #(bv_t n) y w) ->
  squash (bvult #n z w) ->
  Lemma (bvult #n x y)
let trans_lt #n #x #y #z #w pf1 pf2 pf3 = ()

val trans_lt2: 
  #n: pos ->
  #x: uint_t n ->
  #y: uint_t n ->
  #z: bv_t n ->
  #w: bv_t n ->
  squash (int2bv #n x == z) ->
  squash (int2bv #n y == w) ->
  (b2t (bvult #n z w)) ->
  Lemma (x < y)
let trans_lt2 #n #x #y #z #w pf1 pf2 pf3 = int2bv_lemma_ult_2 x y

let rec arith_expr_to_bv (e: expr) : Tac unit =
  match e with
  | NatToBv (MulMod e1 _)
  | MulMod e1 _ ->
    apply_lemma (`int2bv_mul);
    apply_lemma (`cong_bvmul);
    arith_expr_to_bv e1
  | NatToBv (Umod e1 _)
  | Umod e1 _ ->
    apply_lemma (`int2bv_mod);
    apply_lemma (`cong_bvmod);
    arith_expr_to_bv e1
  | NatToBv (Udiv e1 _)
  | Udiv e1 _ ->
    apply_lemma (`int2bv_div);
    apply_lemma (`cong_bvdiv);
    arith_expr_to_bv e1
  | NatToBv (Shl e1 _)
  | Shl e1 _ ->
    apply_lemma (`int2bv_shl);
    apply_lemma (`cong_bvshl);
    arith_expr_to_bv e1
  | NatToBv (Shr e1 _)
  | Shr e1 _ ->
    apply_lemma (`int2bv_shr);
    apply_lemma (`cong_bvshr);
    arith_expr_to_bv e1
  | NatToBv (Land e1 e2)
  | Land e1 e2 ->
    apply_lemma (`int2bv_logand);
    apply_lemma (`cong_bvand);
    arith_expr_to_bv e1;
    arith_expr_to_bv e2
  | NatToBv (Lxor e1 e2)
  | Lxor e1 e2 ->
    apply_lemma (`int2bv_logxor);
    apply_lemma (`cong_bvxor);
    arith_expr_to_bv e1;
    arith_expr_to_bv e2
  | NatToBv (Lor e1 e2)
  | Lor e1 e2 ->
    apply_lemma (`int2bv_logor);
    apply_lemma (`cong_bvor);
    arith_expr_to_bv e1;
    arith_expr_to_bv e2
  | NatToBv (Ladd e1 e2)
  | Ladd e1 e2 ->
    apply_lemma (`int2bv_add);
    apply_lemma (`cong_bvadd);
    arith_expr_to_bv e1;
    arith_expr_to_bv e2
  | NatToBv (Lsub e1 e2)
  | Lsub e1 e2 ->
    apply_lemma (`int2bv_sub);
    apply_lemma (`cong_bvsub);
    arith_expr_to_bv e1;
    arith_expr_to_bv e2
  | _ -> trefl ()

let arith_to_bv_tac () : Tac unit =
  focus (fun () ->
        norm [delta_only ["FStar.BV.bvult"]];
        let g = cur_goal () in
        let f = term_as_formula g in
        match f with
        | Comp (Eq _) l r ->
          (match run_tm (as_arith_expr l) with
            | Inl s ->
              dump s;
              trefl ()
            | Inr e ->
              // dump "inr arith_to_bv";
              seq (fun () -> arith_expr_to_bv e) trefl)
        | _ -> fail ("arith_to_bv_tac: unexpected: " ^ term_to_string g))

(* As things are right now, we need to be able to parse NatToBv
too. This can be useful, if we have mixed expressions so I'll leave it
as is for now *)
let bv_tac () =
  focus (fun () ->
        mapply (`eq_to_bv);
        mapply (`trans);
        arith_to_bv_tac ();
        arith_to_bv_tac ();
        set_options "--smtencoding.elim_box true";
        norm [delta];
        smt ())

let bv_tac_lt n =
  focus (fun () ->
        let nn = pack_ln (Tv_Const (C_Int n)) in
        let t = mk_app (`trans_lt2) [(nn, Q_Implicit)] in
        apply_lemma t;
        arith_to_bv_tac ();
        arith_to_bv_tac ();
        set_options "--smtencoding.elim_box true";
        smt ())

let to_bv_tac () =
  focus (fun () ->
        apply_lemma (`eq_to_bv);
        apply_lemma (`trans);
        arith_to_bv_tac ();
        arith_to_bv_tac ())

