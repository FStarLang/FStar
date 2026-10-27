module FStarC.TypeChecker.Primops.BV

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings
open FStarC.TypeChecker.Primops.Base

module BV = FStar.BV
module EMB = FStarC.Syntax.Embeddings
module NBE = FStarC.TypeChecker.NBETerm
module PC = FStarC.Parser.Const
module S = FStarC.Syntax.Syntax
module U = FStarC.Syntax.Util
module UInt = FStar.UInt

type bv_literal = {
  width: int;
  value: int;
}

let as_bv (width:Prims.pos) (x:bv_literal) : BV.bv_t width =
  BV.int2bv #width (UInt.to_uint_t width x.value)

let bv_term (width value:int) : ML term =
  U.mk_app (S.fvar PC.nat_to_bv_lid None)
    [S.iarg (U.exp_int width); S.as_arg (U.exp_int value)]

instance e_bv_literal : EMB.embedding bv_literal =
  let em x _rng _shadow _norm = bv_term x.width x.value in
  let un t _norm =
    let head, args = U.head_and_args_full t in
    match (U.un_uinst head).n, args with
    | Tm_fvar fv, [(width, Some _); (value, None)]
      when fv_eq_lid fv PC.nat_to_bv_lid ->
      begin match try_unembed_simple width, try_unembed_simple value with
      | Some width, Some value -> Some {width; value}
      | _ -> None
      end
    | _ -> None
  in
  EMB.mk_emb_full em un (fun () -> magic()) (fun _ -> "<bit-vector>")
    (fun () -> ET_abstract)

instance nbe_e_bv_literal : NBE.embedding bv_literal =
  let em cbs x =
    // NBE stores fully applied fvar arguments in reverse order.
    NBE.mkFV (S.lid_as_fv PC.nat_to_bv_lid None) []
      [NBE.as_arg (NBE.embed NBE.e_int cbs x.value);
       NBE.as_iarg (NBE.embed NBE.e_int cbs x.width)]
  in
  let un cbs t =
    match NBE.nbe_t_of_t t with
    | NBE.FV (fv, [], [(value, _); (width, _)])
      when fv_eq_lid fv PC.nat_to_bv_lid ->
      begin match NBE.unembed NBE.e_int cbs width,
                  NBE.unembed NBE.e_int cbs value with
      | Some width, Some value -> Some {width; value}
      | _ -> None
      end
    | _ -> None
  in
  NBE.mk_emb em un (fun () -> magic()) (fun () -> ET_abstract)

let register #f (make:f -> f -> primitive_step) (eval:f) : primitive_step =
  make eval eval

let valid (width:int) (x:bv_literal) : bool =
  width > 0 && x.width = width

let eval_unary
  (op:(#n:Prims.pos -> BV.bv_t n -> Tot (BV.bv_t n)))
  (width:int)
  (x:bv_literal)
  : ML (option bv_literal) =
  if valid width x
  then Some {width; value=BV.bv2int #width (op #width (as_bv width x))}
  else None

let eval_binary
  (op:(#n:Prims.pos -> BV.bv_t n -> BV.bv_t n -> Tot (BV.bv_t n)))
  (width:int)
  (x y:bv_literal)
  : ML (option bv_literal) =
  if valid width x && valid width y
  then
    let value =
      BV.bv2int #width (op #width (as_bv width x) (as_bv width y)) in
    Some {width; value}
  else None

let eval_comp
  (width:int)
  (x y:bv_literal)
  : ML (option bv_literal) =
  if valid width x && valid width y
  then
    Some {width=1;
          value=BV.bv2int #1
            (BV.bvcomp #width (as_bv width x) (as_bv width y))}
  else None

let eval_predicate1
  (op:(#n:Prims.pos -> BV.bv_t n -> Tot bool))
  (width:int)
  (x:bv_literal)
  : ML (option bool) =
  if valid width x then Some (op #width (as_bv width x))
  else None

let eval_predicate2
  (op:(#n:Prims.pos -> BV.bv_t n -> BV.bv_t n -> Tot bool))
  (width:int)
  (x y:bv_literal)
  : ML (option bool) =
  if valid width x && valid width y
  then Some (op #width (as_bv width x) (as_bv width y))
  else None

let eval_int
  (op:(#n:Prims.pos -> BV.bv_t n -> Tot int))
  (width:int)
  (x:bv_literal)
  : ML (option int) =
  if valid width x then Some (op #width (as_bv width x))
  else None

let eval_with_nat
  (op:(#n:Prims.pos -> BV.bv_t n -> nat -> Tot (BV.bv_t n)))
  (width:int)
  (x:bv_literal)
  (amount:int)
  : ML (option bv_literal) =
  if valid width x && amount >= 0
  then
    Some {width;
          value=BV.bv2int #width (op #width (as_bv width x) amount)}
  else None

let eval_with_uint
  (op:(#n:Prims.pos -> BV.bv_t n -> UInt.uint_t n -> Tot (BV.bv_t n)))
  (width:int)
  (x:bv_literal)
  (amount:int)
  : ML (option bv_literal) =
  if valid width x
  then
    let value =
      BV.bv2int #width
        (op #width (as_bv width x) (UInt.to_uint_t width amount)) in
    Some {width; value}
  else None

let eval_with_nonzero_uint
  (op:(#w:Prims.pos ->
       BV.bv_t w ->
       b:UInt.uint_t w{b <> 0} ->
       Tot (BV.bv_t w)))
  (width:int)
  (x:bv_literal)
  (amount:int)
  : ML (option bv_literal) =
  if valid width x
  then
    let amount = UInt.to_uint_t width amount in
    if amount <> 0
    then
      Some {width;
            value=BV.bv2int #width (op #width (as_bv width x) amount)}
    else None
  else None

let eval_indexed
  (op:(#n:Prims.pos ->
       #i:Prims.pos ->
       BV.bv_t n ->
       Tot (BV.bv_t (i + n))))
  (width index:int)
  (x:bv_literal)
  : ML (option bv_literal) =
  if valid width x && index > 0
  then
    let output_width = index + width in
    let value =
      BV.bv2int #output_width (op #width #index (as_bv width x)) in
    Some {width=output_width; value}
  else None

let eval_repeat
  (width index:int)
  (x:bv_literal)
  : ML (option bv_literal) =
  if valid width x && index > 0
  then
    let output_width = index * width in
    let value =
      BV.bv2int #output_width
        (BV.bv_repeat #width #index (as_bv width x)) in
    Some {width=output_width; value}
  else None

let eval_concat
  (left_width right_width:int)
  (x y:bv_literal)
  : ML (option bv_literal) =
  if valid left_width x && valid right_width y
  then
    let width = left_width + right_width in
    let value =
      BV.bv2int #width
        (BV.bv_concat #left_width #right_width
          (as_bv left_width x) (as_bv right_width y)) in
    Some {width; value}
  else None

let eval_extract
  (width:int)
  (x:bv_literal)
  (i j:int)
  : ML (option bv_literal) =
  if valid width x && 0 <= j && j <= i && i < width
  then
    let result_width = i - j + 1 in
    let value =
      BV.bv2int #result_width
        (BV.bv_extract #width (as_bv width x) i j) in
    Some {width=result_width; value}
  else None

let ops : list primitive_step = [
  register (mk3' 0 PC.bv_uext_lid)
    (eval_indexed BV.bv_uext);
  register (mk3' 0 PC.bv_sext_lid)
    (eval_indexed BV.bv_sext);
  register (mk3' 0 PC.bv_repeat_lid) eval_repeat;
  register (mk4' 0 PC.bv_concat_lid) eval_concat;
  register (mk4' 0 PC.bv_extract_lid) eval_extract;

  register (mk2' 0 PC.bv_not_lid) (eval_unary BV.bvnot);
  register (mk2' 0 PC.bv_neg_lid) (eval_unary BV.bvneg);

  register (mk3' 0 PC.bv_and_lid) (eval_binary BV.bvand);
  register (mk3' 0 PC.bv_or_lid) (eval_binary BV.bvor);
  register (mk3' 0 PC.bv_xor_lid) (eval_binary BV.bvxor);
  register (mk3' 0 PC.bv_nand_lid) (eval_binary BV.bvnand);
  register (mk3' 0 PC.bv_nor_lid) (eval_binary BV.bvnor);
  register (mk3' 0 PC.bv_xnor_lid) (eval_binary BV.bvxnor);
  register (mk3' 0 PC.bv_comp_lid) eval_comp;
  register (mk3' 0 PC.bv_add_lid) (eval_binary BV.bvadd);
  register (mk3' 0 PC.bv_sub_lid) (eval_binary BV.bvsub);
  register (mk3' 0 PC.bv_mul'_lid) (eval_binary BV.bvmul');
  register (mk3' 0 PC.bv_shift_left'_lid) (eval_binary BV.bvshl');
  register (mk3' 0 PC.bv_shift_right'_lid) (eval_binary BV.bvshr');
  register (mk3' 0 PC.bv_ashr_lid) (eval_binary BV.bvashr);
  register (mk3' 0 PC.bv_rotate_left'_lid) (eval_binary BV.bvrol');
  register (mk3' 0 PC.bv_rotate_right'_lid) (eval_binary BV.bvror');
  register (mk3' 0 PC.bv_udiv_unsafe_lid) (eval_binary BV.bvdiv_unsafe);
  register (mk3' 0 PC.bv_mod_unsafe_lid) (eval_binary BV.bvmod_unsafe);
  register (mk3' 0 PC.bv_sdiv_lid) (eval_binary BV.bvsdiv);
  register (mk3' 0 PC.bv_srem_lid) (eval_binary BV.bvsrem);
  register (mk3' 0 PC.bv_smod_lid) (eval_binary BV.bvsmod);

  register (mk3' 0 PC.bv_shift_left_lid) (eval_with_nat BV.bvshl);
  register (mk3' 0 PC.bv_shift_right_lid) (eval_with_nat BV.bvshr);
  register (mk3' 0 PC.bv_rotate_left_lid) (eval_with_nat BV.bvrol);
  register (mk3' 0 PC.bv_rotate_right_lid) (eval_with_nat BV.bvror);
  register (mk3' 0 PC.bv_mul_lid) (eval_with_uint BV.bvmul);
  register (mk3' 0 PC.bv_udiv_lid) (eval_with_nonzero_uint BV.bvdiv);
  register (mk3' 0 PC.bv_mod_lid) (eval_with_nonzero_uint BV.bvmod);

  register (mk3' 0 PC.bv_ult_lid) (eval_predicate2 BV.bvult);
  register (mk3' 0 PC.bv_ule_lid) (eval_predicate2 BV.bvule);
  register (mk3' 0 PC.bv_ugt_lid) (eval_predicate2 BV.bvugt);
  register (mk3' 0 PC.bv_uge_lid) (eval_predicate2 BV.bvuge);
  register (mk3' 0 PC.bv_slt_lid) (eval_predicate2 BV.bvslt);
  register (mk3' 0 PC.bv_sle_lid) (eval_predicate2 BV.bvsle);
  register (mk3' 0 PC.bv_sgt_lid) (eval_predicate2 BV.bvsgt);
  register (mk3' 0 PC.bv_sge_lid) (eval_predicate2 BV.bvsge);
  register (mk3' 0 PC.bv_uaddo_lid) (eval_predicate2 BV.bvuaddo);
  register (mk3' 0 PC.bv_saddo_lid) (eval_predicate2 BV.bvsaddo);
  register (mk3' 0 PC.bv_umulo_lid) (eval_predicate2 BV.bvumulo);
  register (mk3' 0 PC.bv_smulo_lid) (eval_predicate2 BV.bvsmulo);
  register (mk3' 0 PC.bv_usubo_lid) (eval_predicate2 BV.bvusubo);
  register (mk3' 0 PC.bv_ssubo_lid) (eval_predicate2 BV.bvssubo);
  register (mk3' 0 PC.bv_sdivo_lid) (eval_predicate2 BV.bvsdivo);
  register (mk2' 0 PC.bv_nego_lid) (eval_predicate1 BV.bvnego);

  register (mk2' 0 PC.bv_to_nat_lid) (eval_int BV.bv2int);
  register (mk2' 0 PC.sbv_to_int_lid) (eval_int BV.sbv_to_int);
]
