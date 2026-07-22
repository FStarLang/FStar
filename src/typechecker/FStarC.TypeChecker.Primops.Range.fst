module FStarC.TypeChecker.Primops.Range

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Monad

open FStarC.TypeChecker.Primops.Base
open FStarC.Range

module PC = FStarC.Parser.Const

(* Range ops. Ranges are no longer sealed, so [range] embeds directly via
   e_range and we no longer need the unsealed-wrapper hack. *)

let mk_range (fn : string) (from_l from_c to_l to_c : int) : Range.t =
  Range.mk_range fn (mk_pos from_l from_c)
                    (mk_pos to_l   to_c)

let explode (r : Range.t) : (string & int & int & int & int) =
  (file_of_range r,
   line_of_pos (start_of_range r),
   col_of_pos  (start_of_range r),
   line_of_pos (end_of_range r),
   col_of_pos  (end_of_range r))

let ops = [
  mk5 0 PC.mk_range_lid   mk_range;
  mk1 0 PC.__explode_range_lid explode;
  mk2' 0 PC.join_range_lid
    (fun r1 r2 -> Some (FStarC.Range.union_ranges r1 r2))
    (fun r1 r2 -> Some (FStarC.Range.union_ranges r1 r2));
]
