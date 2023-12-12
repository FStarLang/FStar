module FStar.TypeChecker.Primops.MachineInts

(* Primops about machine integers *)

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Char
open FStar.Syntax.Syntax
open FStar.TypeChecker.Primops.Base
open FStar.Class.Monad
open FStar.Class.Show
open FStar.Compiler.Writer

module I  = FStar.Ident
module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm
module PC = FStar.Parser.Const
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module Z = FStar.BigInt

type machint_kind =
  | Int8
  | Int16
  | Int32
  | Int64
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UInt128
  | SizeT

let all_machint_kinds =
  [Int8; Int16; Int32; Int64; UInt8; UInt16; UInt32; UInt64; UInt128; SizeT]

let is_unsigned (k : machint_kind) : bool =
  match k with
  | Int8
  | Int16
  | Int32
  | Int64 -> false
  | UInt8
  | UInt16
  | UInt32
  | UInt64
  | UInt128
  | SizeT -> true

let width (k : machint_kind) : int =
  match k with
  | Int8 -> 8
  | Int16 -> 16
  | Int32 -> 32
  | Int64 -> 64
  | UInt8 -> 8
  | UInt16 -> 16
  | UInt32 -> 32
  | UInt64 -> 64
  | UInt128 -> 128
  | SizeT -> 64

let module_name_for (k:machint_kind) : string =
  match k with
  | Int8    -> "Int8"
  | Int16   -> "Int16"
  | Int32   -> "Int32"
  | Int64   -> "Int64"
  | UInt8   -> "UInt8"
  | UInt16  -> "UInt16"
  | UInt32  -> "UInt32"
  | UInt64  -> "UInt64"
  | UInt128 -> "UInt128"
  | SizeT   -> "SizeT"

let mask (k:machint_kind) : Z.t =
  match width k with
  | 8 -> Z.of_hex "ff"
  | 16 -> Z.of_hex "ffff"
  | 32 -> Z.of_hex "ffffffff"
  | 64 -> Z.of_hex "ffffffffffffffff"
  | 128 -> Z.of_hex "ffffffffffffffffffffffffffffffff"

let int_to_t_lid_for (k:machint_kind) : Ident.lid =
  let path = "FStar" :: module_name_for k :: (if is_unsigned k then "uint_to_t" else "int_to_t") :: [] in
  Ident.lid_of_path path Range.dummyRange

let int_to_t_for (k:machint_kind) : S.term =
  let lid = int_to_t_lid_for k in
  S.fvar lid None

let __int_to_t_lid_for (k:machint_kind) : Ident.lid =
  let path = "FStar" :: module_name_for k :: (if is_unsigned k then "__uint_to_t" else "__int_to_t") :: [] in
  Ident.lid_of_path path Range.dummyRange

let __int_to_t_for (k:machint_kind) : S.term =
  let lid = __int_to_t_lid_for k in
  S.fvar lid None

(* just a newtype really, no checks or conditions here *)
type machint (k : machint_kind) = | Mk : Z.t -> option S.meta_source_info -> machint k

(* just for debugging *)
instance showable_bounded_K k : Tot (showable (machint k)) = {
  show = (function Mk x m -> "machine integer " ^ show (Z.to_int_fs x) ^ "@@" ^ module_name_for k);
}

instance e_machint (k : machint_kind) : Tot (EMB.embedding (machint k)) =
  let with_meta_ds r t (m:option meta_source_info) =
    match m with
    | None -> t
    | Some m -> S.mk (Tm_meta {tm=t; meta=Meta_desugared m}) r
  in
  let em (x : machint k) rng shadow cb =
    let Mk i m = x in
    let it = embed_simple rng i in
    let int_to_t = int_to_t_for k in
    let t = S.mk_Tm_app int_to_t [S.as_arg it] rng in
    with_meta_ds rng t m
  in
  let un (t:term) cb : option (machint k) =
    let (t, m) =
        (match (SS.compress t).n with
        | Tm_meta {tm=t; meta=Meta_desugared m} -> (t, Some m)
        | _ -> (t, None))
    in
    let t = U.unmeta_safe t in
    match (SS.compress t).n with
    | Tm_app {hd; args=[(a,_)]} when U.is_fvar (int_to_t_lid_for k) hd
                                  || U.is_fvar (__int_to_t_lid_for k) hd ->
      let a = U.unlazy_emb a in
      let! a : Z.t = try_unembed_simple a in
      Some (Mk a m)
    | _ ->
      None
  in
  EMB.mk_emb_full em un (fun () -> S.t_int) (fun _ -> "boundedint") (fun () -> ET_abstract)

instance nbe_machint (k : machint_kind) : Tot (NBE.embedding (machint k)) =
  let open NBE in
  let with_meta_ds t (m:option meta_source_info) =
    match m with
    | None -> t
    | Some m -> NBE.mk_t (Meta(t, Thunk.mk (fun _ -> Meta_desugared m)))
  in
  let em cbs (x : machint k) =
    let Mk i m = x in
    let it = embed e_int cbs i in
    let int_to_t args = mk_t <| FV (S.lid_as_fv (__int_to_t_lid_for k) None, [], args) in
    let t = int_to_t [as_arg it] in
    with_meta_ds t m
  in
  let un cbs a : option (machint k) =
    let (a, m) =
      (match a.nbe_t with
       | Meta(t, tm) ->
         (match Thunk.force tm with
          | Meta_desugared m -> (t, Some m)
          | _ -> (a, None))
       | _ -> (a, None))
    in
    match a.nbe_t with
    | FV (fv1, [], [(a, _)]) when Ident.lid_equals (fv1.fv_name.v) (int_to_t_lid_for k) ->
      let! a : Z.t = unembed e_int cbs a in
      Some (Mk a m)
    | _ -> None
  in
  mk_emb em un (fun () -> mkFV (lid_as_fv PC.int_lid None) [] [] (* fixme *)) (fun () -> ET_abstract)

let v #k (x : machint k) =
  let Mk v _ = x in v
let meta #k (x : machint k) =
  let Mk _ meta = x in meta

let make_as #k (x : machint k) (z : Z.t) : machint k =
  Mk z (meta x)

(* NB: Eta expanding trips typeclass resolution *)
let mymon = writer (list primitive_step)

let bounded_arith_ops_for (k : machint_kind) : mymon unit =
  let mod_name = module_name_for k in
  let nm s = (PC.p2l ["FStar"; module_name_for k; s]) in
  (* Operators common to all *)
  emit [
    mk1 0 (nm "v") (v #k);

    (* basic ops supported by all *)
    mk2 0 (nm "add") (fun (x y : machint k) -> make_as x (Z.add_big_int (v x) (v y)));
    mk2 0 (nm "sub") (fun (x y : machint k) -> make_as x (Z.sub_big_int (v x) (v y)));
    mk2 0 (nm "mul") (fun (x y : machint k) -> make_as x (Z.mult_big_int (v x) (v y)));

    mk2 0 (nm "gt")  (fun (x y : machint k) -> Z.gt_big_int (v x) (v y));
    mk2 0 (nm "gte") (fun (x y : machint k) -> Z.ge_big_int (v x) (v y));
    mk2 0 (nm "lt")  (fun (x y : machint k) -> Z.lt_big_int (v x) (v y));
    mk2 0 (nm "lte") (fun (x y : machint k) -> Z.le_big_int (v x) (v y));
  ];!

  (* Unsigned ints have more operators *)
  let sz = width k in
  let modulus = Z.shift_left_big_int Z.one (Z.of_int_fs sz) in
  let mod x = Z.mod_big_int x modulus in
  if is_unsigned k then
    emit [
      (* modulo operators *)
      mk2 0 (nm "add_mod") (fun (x y : machint k) -> make_as x (mod (Z.add_big_int (v x) (v y))));
      mk2 0 (nm "sub_mod") (fun (x y : machint k) -> make_as x (mod (Z.sub_big_int (v x) (v y))));
      mk2 0 (nm "div")     (fun (x y : machint k) -> make_as x (mod (Z.div_big_int (v x) (v y))));
      mk2 0 (nm "rem")     (fun (x y : machint k) -> make_as x (mod (Z.mod_big_int (v x) (v y))));

      (* bitwise *)
      mk2 0 (nm "logor")  (fun (x y : machint k) -> make_as x (Z.logor_big_int  (v x) (v y)));
      mk2 0 (nm "logand") (fun (x y : machint k) -> make_as x (Z.logand_big_int (v x) (v y)));
      mk2 0 (nm "logxor") (fun (x y : machint k) -> make_as x (Z.logxor_big_int (v x) (v y)));
      mk1 0 (nm "lognot") (fun (x : machint k) ->   make_as x (Z.logand_big_int (Z.lognot_big_int (v x)) (mask k)));

      (* NB: shift_{left,right} always take a UInt32 on the right, hence the annotations
      to choose the right instances. *)
      mk2 0 (nm "shift_left")  (fun (x : machint k) (y : machint UInt32) ->
                                 make_as x (Z.logand_big_int (Z.shift_left_big_int (v x) (v y)) (mask k)));
      mk2 0 (nm "shift_right")  (fun (x : machint k) (y : machint UInt32) ->
                                 make_as x (Z.logand_big_int (Z.shift_right_big_int (v x) (v y)) (mask k)));
    ]
  else return ();!

  (* Most unsigneds, except SizeT, have underspec ops *)
  if is_unsigned k && k <> SizeT then
    emit [
      mk2 0 (nm "add_underspec") (fun (x y : machint k) -> make_as x (Z.add_big_int (v x) (v y)));
      mk2 0 (nm "sub_underspec") (fun (x y : machint k) -> make_as x (Z.sub_big_int (v x) (v y)));
      mk2 0 (nm "mul_underspec") (fun (x y : machint k) -> make_as x (Z.mult_big_int (v x) (v y)));
    ]
  else return ();!

  (* And except for SizeT and UInt128, they have mul_mod *)
  if is_unsigned k && (k <> SizeT && k <> UInt128) then
    emit [
      mk2 0 (nm "mul_mod") (fun (x y : machint k) -> make_as x (mod (Z.mult_big_int (v x) (v y))));
    ]
  else return ();!

  return ()

let bounded_arith_ops : list primitive_step =
  fst <|
  run_writer <|
  (iterM bounded_arith_ops_for all_machint_kinds ;!
   emit [
        (* Single extra op that returns a U32 *)
        mk1 0 PC.char_u32_of_char (fun (c : char) -> let n = Compiler.Util.int_of_char c |> Z.of_int_fs in
                                                        Mk #UInt32 n None);
   ])
