open Prims
type range = FStarC_Range_Type.range
let range_0 : range= FStarC_Range_Type.dummyRange
let mk_range (file : Prims.string) (from_line : Prims.int)
  (from_col : Prims.int) (to_line : Prims.int) (to_col : Prims.int) : 
  range=
  FStarC_Range_Type.mk_range file
    (FStarC_Range_Type.mk_pos from_line from_col)
    (FStarC_Range_Type.mk_pos to_line to_col)
let pos_leq (p1 : FStarC_Range_Type.pos) (p2 : FStarC_Range_Type.pos) :
  Prims.bool=
  (p1.FStarC_Range_Type.line < p2.FStarC_Range_Type.line) ||
    ((p1.FStarC_Range_Type.line = p2.FStarC_Range_Type.line) &&
       (p1.FStarC_Range_Type.col <= p2.FStarC_Range_Type.col))
let min_pos (p1 : FStarC_Range_Type.pos) (p2 : FStarC_Range_Type.pos) :
  FStarC_Range_Type.pos= if pos_leq p1 p2 then p1 else p2
let max_pos (p1 : FStarC_Range_Type.pos) (p2 : FStarC_Range_Type.pos) :
  FStarC_Range_Type.pos= if pos_leq p1 p2 then p2 else p1
let union_rng (r1 : FStarC_Range_Type.rng) (r2 : FStarC_Range_Type.rng) :
  FStarC_Range_Type.rng=
  if r1.FStarC_Range_Type.file_name <> r2.FStarC_Range_Type.file_name
  then r2
  else
    FStarC_Range_Type.mk_rng r1.FStarC_Range_Type.file_name
      (min_pos r1.FStarC_Range_Type.start_pos r2.FStarC_Range_Type.start_pos)
      (max_pos r1.FStarC_Range_Type.end_pos r2.FStarC_Range_Type.end_pos)
let join_range (r1 : range) (r2 : range) : range=
  FStarC_Range_Type.range_of_rng
    (union_rng r1.FStarC_Range_Type.def_range r2.FStarC_Range_Type.def_range)
    (union_rng r1.FStarC_Range_Type.use_range r2.FStarC_Range_Type.use_range)
let explode (r : range) :
  (Prims.string * Prims.int * Prims.int * Prims.int * Prims.int)=
  (((r.FStarC_Range_Type.def_range).FStarC_Range_Type.file_name),
    (((r.FStarC_Range_Type.def_range).FStarC_Range_Type.start_pos).FStarC_Range_Type.line),
    (((r.FStarC_Range_Type.def_range).FStarC_Range_Type.start_pos).FStarC_Range_Type.col),
    (((r.FStarC_Range_Type.def_range).FStarC_Range_Type.end_pos).FStarC_Range_Type.line),
    (((r.FStarC_Range_Type.def_range).FStarC_Range_Type.end_pos).FStarC_Range_Type.col))
