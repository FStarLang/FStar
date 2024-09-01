module FStar.TypeChecker.Primops.Range

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Class.Monad

open FStar.TypeChecker.Primops.Base
open FStar.Compiler.Range

module PC = FStar.Parser.Const
module Z = FStar.BigInt

(* Range ops *)

(* this type only here to use typeclass hackery *)
type unsealedRange = | U of Range.range

let mk_range (fn : string) (from_l from_c to_l to_c : Z.t) : Range.range =
  Range.mk_range fn (mk_pos (Z.to_int_fs from_l) (Z.to_int_fs from_c))
                    (mk_pos (Z.to_int_fs to_l) (Z.to_int_fs to_c))

let __mk_range (fn : string) (from_l from_c to_l to_c : Z.t) : unsealedRange =
  U (mk_range fn from_l from_c to_l to_c)

let explode (r : unsealedRange) : (string & Z.t & Z.t & Z.t & Z.t) =
  match r with
  | U r ->
    let open FStar.Compiler.Range.Type in
    (file_of_range r,
     Z.of_int_fs (line_of_pos (start_of_range r)),
     Z.of_int_fs (col_of_pos  (start_of_range r)),
     Z.of_int_fs (line_of_pos (end_of_range r)),
     Z.of_int_fs (col_of_pos  (end_of_range r)))

instance e_unsealedRange : Syntax.Embeddings.embedding unsealedRange =
  let open FStar.Syntax.Embeddings in
  embed_as e___range
    (fun r -> U r)
    (fun (U r) -> r)
    None

instance nbe_e_unsealedRange : FStar.TypeChecker.NBETerm.embedding unsealedRange =
  let open FStar.TypeChecker.NBETerm in
  embed_as e___range
    (fun r -> U r)
    (fun (U r) -> r)
    None

let ops = [
  mk5 0 PC.__mk_range_lid __mk_range;
  mk5 0 PC.mk_range_lid   mk_range;
  mk1 0 PC.__explode_range_lid explode;
  mk2 0 PC.join_range_lid FStar.Compiler.Range.union_ranges;
]
