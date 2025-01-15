module FStarC.MachineInts

(* A type representing all the kinds of machine integers, and an
embedding instance for them. *)

open FStar open FStarC
open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax

module EMB = FStarC.Syntax.Embeddings
module NBE = FStarC.TypeChecker.NBETerm
module PC = FStarC.Parser.Const
module S  = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U  = FStarC.Syntax.Util
module Z = FStarC.BigInt

open FStarC.Class.Show
open FStarC.Class.Monad

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

let mk #k x m = Mk #k x m
let v #k (x : machint k) =
  let Mk v _ = x in v
let meta #k (x : machint k) =
  let Mk _ meta = x in meta
let make_as #k (x : machint k) (z : Z.t) : machint k =
  Mk z (meta x)

(* just for debugging *)
instance showable_bounded_k k : Tot (showable (machint k)) = {
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
    let it = EMB.embed i rng None cb in
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
      let! a : Z.t = EMB.try_unembed a cb in
      Some (Mk a m)
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
  mk_emb em un
     (fun () -> mkFV (lid_as_fv (Ident.lid_of_path ["FStar"; module_name_for k; "t"] Range.dummyRange) None) [] [])
     (fun () -> ET_abstract)

