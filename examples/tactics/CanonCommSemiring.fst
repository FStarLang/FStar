module CanonCommSemiring

(*
Commutative semiring (a ring with commutative multiplication and without an additive inverse)
This requires the following properties:
- addition is commutative and associative, where zero is the additive identity
- multiplication is commutative and associative, where one is the multiplicative identity
- multiplication distributes over addition
Currently, this module performs the following actions to canonize a term:
- apply distributivity until the term is in sum-of-products form, where each product may have
  multiplications but no additions
- apply CanonCommMonoid to canonize each product, with constants on the outside of each product
  (example: ((((x * y) * z) * 3) * 2)
This module does not yet canonize the sum itself.  For integer arithmetic, Z3's nonlinear
reasoning can handle this.
*)

open FStar.List
open FStar.Tactics
open FStar.Reflection
open FStar.Classical
open FStar.Algebra.CommMonoid
module CCM = CanonCommMonoid

irreducible let canon_attr = ()

[@canon_attr]
unfold let cm_op = CM?.mult

(***** Commutative semirings *)

let distribute_left_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let (+) = cm_op cm_add in
  let ( * ) = cm_op cm_mult in
  x:a -> y:a -> z:a -> Lemma (x * (y + z) == x * y + x * z)

let distribute_right_lemma (a:Type) (cm_add:cm a) (cm_mult:cm a) =
  let (+) = cm_op cm_add in
  let ( * ) = cm_op cm_mult in
  x:a -> y:a -> z:a -> Lemma ((x + y) * z == x * z + y * z)

[@canon_attr]
unopteq
type cr (a:Type) =
  | CR :
    cm_add:cm a ->
    cm_mult:cm a ->
    distribute:distribute_left_lemma a cm_add cm_mult ->
    cr a

let distribute_right (#a:Type) (r:cr a) : distribute_right_lemma a r.cm_add r.cm_mult =
  fun x y z ->
    CM?.commutativity r.cm_mult (cm_op r.cm_add x y) z;
    r.distribute z x y;
    CM?.commutativity r.cm_mult x z;
    CM?.commutativity r.cm_mult y z

[@canon_attr]
let int_cr : cr int =
  CR int_plus_cm int_multiply_cm (fun x y z -> ())

(***** Expression syntax *)

unfold let var = CCM.var

type exp : Type =
  | Var : var -> exp
  | Add : exp -> exp -> exp
  | Mult : exp -> exp -> exp

let rec exp_to_string (e:exp) : string =
  match e with
  | Var x -> "Var " ^ string_of_int (x <: var)
  | Add e1 e2 -> "Add (" ^ exp_to_string e1 ^ ") (" ^ exp_to_string e2 ^ ")"
  | Mult e1 e2 -> "Mult (" ^ exp_to_string e1 ^ ") (" ^ exp_to_string e2 ^ ")"

let rec quote_exp (e:exp) : Tac term =
  match e with
  | Var x -> mk_e_app (`Var) [pack (Tv_Const (C_Int x))]
  | Add e1 e2 -> mk_e_app (`Add) [quote_exp e1; quote_exp e2]
  | Mult e1 e2 -> mk_e_app (`Mult) [quote_exp e1; quote_exp e2]


(***** Expression denotation *)

unfold let vmap = CCM.vmap

[@canon_attr]
unfold let select = CCM.select

[@canon_attr]
let rec rdenote (#a #b:Type) (r:cr a) (vm:vmap a b) (e:exp) : a =
  match e with
  | Var x -> select x vm
  | Add e1 e2 -> cm_op r.cm_add (rdenote r vm e1) (rdenote r vm e2)
  | Mult e1 e2 -> cm_op r.cm_mult (rdenote r vm e1) (rdenote r vm e2)

(***** Distributing expressions to sum-of-products *)

type sum_of_products : Type =
  | Product : CCM.exp -> sum_of_products
  | Sum : sum_of_products -> sum_of_products -> sum_of_products

[@canon_attr]
let rec sum_denote (#a #b:Type) (r:cr a) (vm:vmap a b) (e:sum_of_products) : a =
  match e with
  | Product ce -> CCM.mdenote r.cm_mult vm ce
  | Sum e1 e2 -> cm_op r.cm_add (sum_denote r vm e1) (sum_denote r vm e2)

// turn x * y into sum of products
[@canon_attr]
let rec multiply_sums (x y:sum_of_products) : sum_of_products =
  match (x, y) with
  | (Product px, Product py) -> Product (CCM.Mult px py)
  | (Sum s1 s2, _) -> Sum (multiply_sums s1 y) (multiply_sums s2 y)
  | (_, Sum s1 s2) -> Sum (multiply_sums x s1) (multiply_sums x s2)

[@canon_attr]
let rec exp_to_sum (e:exp) : sum_of_products =
  match e with
  | Var x -> Product (CCM.Var x)
  | Add e1 e2 -> Sum (exp_to_sum e1) (exp_to_sum e2)
  | Mult e1 e2 -> multiply_sums (exp_to_sum e1) (exp_to_sum e2)

let rec multiply_sums_correct (#a #b:Type) (r:cr a) (vm:vmap a b) (x y:sum_of_products) :
  Lemma
    (ensures (
      let ( * ) = cm_op r.cm_mult in
      sum_denote r vm (multiply_sums x y) == sum_denote r vm x * sum_denote r vm y
    ))
  =
  match (x, y) with
  | (Product _, Product _) -> ()
  | (Sum s1 s2, _) ->
    (
      multiply_sums_correct r vm s1 y;
      multiply_sums_correct r vm s2 y;
      distribute_right r (sum_denote r vm s1) (sum_denote r vm s2) (sum_denote r vm y)
    )
  | (_, Sum s1 s2) ->
    (
      multiply_sums_correct r vm x s1;
      multiply_sums_correct r vm x s2;
      r.distribute (sum_denote r vm x) (sum_denote r vm s1) (sum_denote r vm s2)
    )

let rec exp_to_sum_correct (#a #b:Type) (r:cr a) (vm:vmap a b) (e:exp) : Lemma
  (sum_denote r vm (exp_to_sum e) == rdenote r vm e)
  =
  match e with
  | Var x -> ()
  | Add e1 e2 ->
    (
      exp_to_sum_correct r vm e1;
      exp_to_sum_correct r vm e2;
      ()
    )
  | Mult e1 e2 ->
    (
      exp_to_sum_correct r vm e1;
      exp_to_sum_correct r vm e2;
      multiply_sums_correct r vm (exp_to_sum e1) (exp_to_sum e2)
    )

(***** Canonicalization tactics *)

unfold let permute = CCM.permute
unfold let permute_correct = CCM.permute_correct
unfold let sort = CCM.sort
unfold let sort_correct = CCM.sort_correct
unfold let is_const = CCM.is_const
unfold let const_last = CCM.const_last
unfold let where = CCM.where
unfold let const = CCM.const
unfold let update = CCM.update

[@canon_attr]
let rec cdenote (#a #b:Type) (p:permute b) (r:cr a) (vm:vmap a b) (s:sum_of_products) : a
  =
  match s with
  | Product ce -> CCM.xsdenote (r.cm_mult) vm (CCM.canon vm p ce)
  | Sum s1 s2 -> cm_op r.cm_add (cdenote p r vm s1) (cdenote p r vm s2)

let rec cdenote_correct (#a #b:Type) (p:permute b) (pc:permute_correct p)
    (r:cr a) (vm:vmap a b) (s:sum_of_products) :
  Lemma (cdenote p r vm s == sum_denote r vm s)
  =
  match s with
  | Product ce -> CCM.canon_correct p pc r.cm_mult vm ce
  | Sum s1 s2 ->
    (
      cdenote_correct p pc r vm s1;
      cdenote_correct p pc r vm s2;
      ()
    )

let canon_correct (#a #b:Type) (p:permute b) (pc:permute_correct p)
    (r:cr a) (vm:vmap a b) (e:exp) :
  Lemma (cdenote p r vm (exp_to_sum e) == rdenote r vm e)
  =
  exp_to_sum_correct r vm e;
  cdenote_correct p pc r vm (exp_to_sum e)

let semiring_reflect (#a #b:Type) (p:permute b) (pc:permute_correct p)
    (r:cr a) (vm:vmap a b) (e1 e2:exp) (a1 a2:a)
    (_ : squash (
      cdenote p r vm (exp_to_sum e1) ==
      cdenote p r vm (exp_to_sum e2)))
    (_ : squash (a1 == rdenote r vm e1))
    (_ : squash (a2 == rdenote r vm e2)) :
    squash (a1 == a2)
  =
  canon_correct p pc r vm e1;
  canon_correct p pc r vm e2;
  ()

let make_fvar (#a #b:Type) (f:term -> Tac b) (t:term) (unquotea:term->Tac a) (ts:list term) (vm:vmap a b) : Tac
    (exp * list term * vmap a b) =
  match where t ts with
  | Some v -> (Var v, ts, vm)
  | None ->
    let vfresh = length ts in
    let z = unquotea t in
    (Var vfresh, ts @ [t], update vfresh z (f t) vm)

// This expects that add, mult, and t have already been normalized
let rec reification_aux (#a #b:Type) (unquotea:term->Tac a) (ts:list term) (vm:vmap a b) (f:term -> Tac b)
    (add mult t: term) : Tac (exp * list term * vmap a b) =
  let hd, tl = collect_app_ref t in
  match inspect hd, list_unref tl with
  | (Tv_FVar fv, [(t1, Q_Explicit) ; (t2, Q_Explicit)]) ->
    let binop (op:exp -> exp -> exp) : Tac (exp * list term * vmap a b) =
      let (e1, ts, vm) = reification_aux unquotea ts vm f add mult t1 in
      let (e2, ts, vm) = reification_aux unquotea ts vm f add mult t2 in
      (op e1 e2, ts, vm)
      in
    if term_eq (pack (Tv_FVar fv)) add then binop Add else
    if term_eq (pack (Tv_FVar fv)) mult then binop Mult else
    make_fvar f t unquotea ts vm
  | (_, _) -> make_fvar f t unquotea ts vm

let reification (b:Type) (f:term -> Tac b) (def:b) (#a:Type)
    (unquotea:term->Tac a) (quotea:a -> Tac term) (tadd tmult:term) (munit:a) (ts:list term) :
    Tac (list exp * vmap a b) =
  let add = norm_term [delta] tadd in
  let mult = norm_term [delta] tmult in
  let ts = Tactics.Util.map (norm_term [delta]) ts in
  //dump ("add = " ^ term_to_string add ^ "; mult = " ^ term_to_string mult);
  let (es, _, vm) =
    Tactics.Util.fold_left
      (fun (es,vs,vm) t ->
        let (e,vs,vm) = reification_aux unquotea vs vm f add mult t
        in (e::es,vs,vm))
      ([],[], const munit def) ts
  in (List.rev es,vm)


let canon_norm () : Tac unit =
  norm [
    primops;
    iota;
    zeta;
    delta_attr canon_attr;
    delta_only [
      "FStar.Algebra.CommMonoid.int_plus_cm";
      "FStar.Algebra.CommMonoid.int_multiply_cm";
      "FStar.Algebra.CommMonoid.__proj__CM__item__mult";
      "CanonCommSemiring.__proj__CR__item__cm_add";
      "CanonCommSemiring.__proj__CR__item__cm_mult";
      "CanonCommMonoid.canon";
      "CanonCommMonoid.xsdenote";
      "CanonCommMonoid.flatten";
      "CanonCommMonoid.select";
      "CanonCommMonoid.select_extra";
      "CanonCommMonoid.const_last";
      "CanonCommMonoid.const_compare";
      "CanonCommMonoid.special_compare";
      "CanonCommMonoid.sortWith_correct";
      "FStar.List.Tot.Base.assoc";
      "FStar.Pervasives.Native.fst";
      "FStar.Pervasives.Native.snd";
      "FStar.Pervasives.Native.__proj__Mktuple2__item___1";
      "FStar.Pervasives.Native.__proj__Mktuple2__item___2";
      "FStar.List.Tot.Base.op_At";
      "FStar.List.Tot.Base.append";
      "FStar.List.Tot.Base.sortWith";
      "FStar.List.Tot.Base.partition";
      "FStar.List.Tot.Base.bool_of_compare";
      "FStar.List.Tot.Base.compare_of_bool";
    ]
  ]

[@plugin]
let canon_semiring_aux
    (a b: Type) (ta: term) (unquotea: term -> Tac a) (quotea: a -> Tac term)
    (tr tadd tmult: term) (munit: a) (tb: term) (quoteb:b->Tac term)
    (f:term->Tac b) (def:b) (tp:term) (tpc:term): Tac unit =
  focus (fun () ->
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) t1 t2 ->
    (
      //dump ("t1 = " ^ term_to_string t1 ^ "; t2 = " ^ term_to_string t2);
      if term_eq t ta then
      (
        match reification b f def unquotea quotea tadd tmult munit [t1; t2] with
        | ([e1; e2], vm) ->
          (
            (*
            dump (
              "e1 = " ^ exp_to_string e1 ^
              "; e2 = " ^ exp_to_string e2);
            dump ("vm = " ^ term_to_string (quote vm));
            dump ("before = " ^ term_to_string (norm_term [delta; primops]
              (quote (rdenote r vm e1 == rdenote r vm e2))));
            dump ("expected after = " ^ term_to_string (norm_term [delta; primops]
              (quote (
                cdenote p r vm (exp_to_sum e1) ==
                cdenote p r vm (exp_to_sum e2)))));
            *)
            // let q_app0 = quote (semiring_reflect #a #b p pc r vm e1 e2) in
            // dump (term_to_string t1);
            let tvm = CCM.quote_vm ta tb quotea quoteb vm in
            let te1 = quote_exp e1 in
            // dump (exp_to_string e1);
            // dump (term_to_string te1);
            let te2 = quote_exp e2 in
            // dump (term_to_string te2);
            mapply
              (mk_app (`semiring_reflect)
                [(ta, Q_Implicit); (tb, Q_Implicit); (tp, Q_Explicit); (tpc, Q_Explicit);
                 (tr, Q_Explicit); (tvm, Q_Explicit); (te1, Q_Explicit); (te2, Q_Explicit); (t1, Q_Explicit); (t2, Q_Explicit)]);
            unfold_def tp;
            canon_norm ();
            later ();
            canon_norm ();
            //dump ("after norm-left");
            trefl ();
            canon_norm ();
            //dump ("after norm-right");
            trefl ();
            dump "done"
          )
        | _ -> fail "Unexpected"
      )
      else fail "Found equality, but terms do not have the expected type"
    )
  | _ -> fail "Goal should be an equality")


let canon_semiring_with
    (b:Type) (f:term -> Tac b) (def:b) (p:permute b) (pc:permute_correct p)
    (#a:Type) (r:cr a) : Tac unit =
  canon_semiring_aux a b
    (quote a) (unquote #a) (fun (x:a) -> quote x)
    (quote r) (quote (cm_op (r.cm_add))) (quote (cm_op (r.cm_mult))) (CM?.unit (r.cm_add))
    (quote b) (fun (x:b) -> quote x) f def (quote p) (quote pc)

let is_not_const (t:term) : Tac bool =
  let (hd, tl) = collect_app_ref t in
  match (inspect hd, list_unref tl) with
  | (Tv_Const _, []) -> false
  | (Tv_FVar fv, [(t1, _)]) ->
    (
      match (inspect_fv fv, inspect t1) with
      | (x, Tv_Const _) -> not (x = neg_qn)
      | _ -> true
    )
  | _ -> true

let canon_semiring (#a:Type) (r:cr a) : Tac unit =
  canon_semiring_with bool is_not_const true const_last
    (fun #a m vm xs -> CCM.sortWith_correct #bool (CCM.const_compare vm) #a m vm xs)
    r

#reset-options "--z3cliopt smt.arith.nl=false"

let lem0 (a b c d : int) =
  let open FStar.Mul in
  //assert ((a + b) * (c + d) == a * d + c * b + b * d + a * c);
  assert_by_tactic ((a + b + b) * (c + d) == a * d + 2 * c * b + b * 2 * d + a * c)
    (fun _ -> canon_semiring int_cr)

open FStar.Mul

val lemma_poly_multiply : n:int -> p:int -> r:int -> h:int -> r0:int -> r1:int -> h0:int -> h1:int -> h2:int -> s1:int -> d0:int -> d1:int -> d2:int -> hh:int -> Lemma
  (requires
    p > 0 /\
    r1 >= 0 /\
    n > 0 /\
    4 * (n * n) == p + 5 /\
    r == r1 * n + r0 /\
    h == h2 * (n * n) + h1 * n + h0 /\
    s1 == r1 + (r1 / 4) /\
    r1 % 4 == 0 /\
    d0 == h0 * r0 + h1 * s1 /\
    d1 == h0 * r1 + h1 * r0 + h2 * s1 /\
    d2 == h2 * r0 /\
    hh == d2 * (n * n) + d1 * n + d0
  )
  (ensures (h * r) % p == hh % p)

// These assumptions are proven in https://github.com/project-everest/vale/blob/fstar/src/lib/math/Math.Lemmas.Int_i.fsti
assume val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)
assume val lemma_div_mod (a:int) (n:pos) : Lemma (a == (a / n) * n + a % n)

let lemma_poly_multiply n p r h r0 r1 h0 h1 h2 s1 d0 d1 d2 hh =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  //assert (h * r == h_r_expand);
  //assert (hh == hh_expand);
  let b = ((h2 * n + h1) * r1_4) in
  modulo_addition_lemma hh_expand p b;
  assert_by_tactic (h_r_expand == hh_expand + b * (n * n * 4 + (-5)))
    (fun _ -> canon_semiring int_cr);
  ()

val lemma_poly_reduce : n:int -> p:int -> h:int -> h2:int -> h10:int -> c:int -> hh:int -> Lemma
  (requires
    p > 0 /\
    4 * (n * n) == p + 5 /\
    h2 == h / (n * n) /\
    h10 == h % (n * n) /\
    c == (h2 / 4) + (h2 / 4) * 4 /\
    hh == h10 + c + (h2 % 4) * (n * n))
  (ensures h % p == hh % p)

let lemma_poly_reduce n p h h2 h10 c hh =
  let h2_4 = h2 / 4 in
  let h2_m = h2 % 4 in
  let h_expand = h10 + (h2_4 * 4 + h2_m) * (n * n) in
  let hh_expand = h10 + (h2_m) * (n * n) + h2_4 * 5 in
  lemma_div_mod h (n * n);
  modulo_addition_lemma hh_expand p h2_4;
  assert_by_tactic (h_expand == hh_expand + h2_4 * (n * n * 4 + (-5)))
    (fun _ -> canon_semiring int_cr);
  ()
