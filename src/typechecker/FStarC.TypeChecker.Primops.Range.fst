module FStarC.TypeChecker.Primops.Range

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Monad

open FStarC.TypeChecker.Primops.Base
open FStarC.Range

module PC = FStarC.Parser.Const

(* Range ops *)

(* this type only here to use typeclass hackery *)
type unsealedRange = | U of Range.t

let mk_range (fn : string) (from_l from_c to_l to_c : int) : Range.t =
  Range.mk_range fn (mk_pos from_l from_c)
                    (mk_pos to_l   to_c)

let __mk_range (fn : string) (from_l from_c to_l to_c : int) : unsealedRange =
  U (mk_range fn from_l from_c to_l to_c)

let explode (r : unsealedRange) : (string & int & int & int & int) =
  match r with
  | U r ->
    let open FStarC.Range.Type in
    (file_of_range r,
     line_of_pos (start_of_range r),
     col_of_pos  (start_of_range r),
     line_of_pos (end_of_range r),
     col_of_pos  (end_of_range r))

instance e_unsealedRange : Syntax.Embeddings.embedding unsealedRange =
  let open FStarC.Syntax.Embeddings in
  embed_as e___range
    (fun r -> U r)
    (fun (U r) -> r)
    None

instance nbe_e_unsealedRange : FStarC.TypeChecker.NBETerm.embedding unsealedRange =
  let open FStarC.TypeChecker.NBETerm in
  embed_as e___range
    (fun r -> U r)
    (fun (U r) -> r)
    None

let ops = [
  mk5 0 PC.__mk_range_lid __mk_range;
  mk5 0 PC.mk_range_lid   mk_range;
  mk1 0 PC.__explode_range_lid explode;
  mk2 0 PC.join_range_lid FStarC.Range.union_ranges;
]
