module FStar.Compiler.MachineInts

(* A type representing all the kinds of machine integers, and an
embedding instance for them. *)

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Syntax.Syntax

module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm
module PC = FStar.Parser.Const
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U  = FStar.Syntax.Util
module Z = FStar.BigInt

open FStar.Class.Show
open FStar.Class.Monad

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
let is_signed k = not (is_unsigned k)

let widthn (k : machint_kind) : int =
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
  match widthn k with
  | 8 -> Z.of_hex "ff"
  | 16 -> Z.of_hex "ffff"
  | 32 -> Z.of_hex "ffffffff"
  | 64 -> Z.of_hex "ffffffffffffffff"
  | 128 -> Z.of_hex "ffffffffffffffffffffffffffffffff"

let signedness (k:machint_kind) : Const.signedness =
  if is_unsigned k then Const.Unsigned else Const.Signed

let width (k:machint_kind) : Const.width =
  match k with
  | Int8 | UInt8 -> Const.Int8
  | Int16 | UInt16 -> Const.Int16
  | Int32 | UInt32 -> Const.Int32
  | Int64 | UInt64 -> Const.Int64
  | UInt128 -> Const.Int128
  | SizeT -> Const.Sizet

(* just a newtype really, no checks or conditions here *)
type machint (k : machint_kind) = | Mk : Z.t -> machint k

let mk #k x = Mk #k x
let v #k (x : machint k) =
  let Mk v = x in v
let int_to_t #k (i : Z.t) : machint k =
  (* FIXME: Check bounds? *)
  Mk i

let make_as #k (x : machint k) (z : Z.t) : machint k =
  Mk z

(* just for debugging *)
instance showable_bounded_k k : Tot (showable (machint k)) = {
  show = (function Mk x -> "machine integer " ^ show (Z.to_int_fs x) ^ "@@" ^ module_name_for k);
}

instance e_machint (k : machint_kind) : Tot (EMB.embedding (machint k)) =
  let with_meta_ds r t (m:option meta_source_info) =
    match m with
    | None -> t
    | Some m -> S.mk (Tm_meta {tm=t; meta=Meta_desugared m}) r
  in
  let em (x : machint k) rng shadow cb =
    let Mk i = x in
    let const = Const.Const_int (Z.string_of_big_int i, Some (signedness k, width k)) in
    S.mk (S.Tm_constant const) rng
  in
  let un (t:term) cb : option (machint k) =
    let t = U.unmeta_safe t in
    match (SS.compress t).n with
    | Tm_constant (Const.Const_int (str, Some (s, w)))
        when s = signedness k && w = width k ->
      let n = Z.big_int_of_string str in
      Some (Mk n)
    | _ ->
      None
  in
  EMB.mk_emb_full em un
    (fun () -> S.fvar (Ident.lid_of_path ["FStar"; module_name_for k; "t"] Range.dummyRange) None)
    (fun _ -> "boundedint")
    (fun () -> ET_abstract)

instance nbe_machint (k : machint_kind) : Tot (NBE.embedding (machint k)) =
  let open NBE in
  let with_meta_ds t (m:option meta_source_info) =
    match m with
    | None -> t
    | Some m -> NBE.mk_t (Meta(t, Thunk.mk (fun _ -> Meta_desugared m)))
  in
  let em cbs (x : machint k) : t =
    let Mk i = x in
    let const = Const.Const_int (Z.string_of_big_int i, Some (signedness k, width k)) in
    mk_t <| Constant (SConst const)
  in
  let un cbs a : option (machint k) =
    match a.nbe_t with
    | Constant (SConst (Const.Const_int (str, Some (s, w))))
        when s = signedness k && w = width k ->
      let n = Z.big_int_of_string str in
      Some (Mk n)
    | _ -> None
  in
  mk_emb em un
     (fun () -> mkFV (lid_as_fv (Ident.lid_of_path ["FStar"; module_name_for k; "t"] Range.dummyRange) None) [] [])
     (fun () -> ET_abstract)
