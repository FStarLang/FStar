type __range = FStarC_Compiler_Range_Type.range
type range = __range

let mk_range f a b c d = FStarC_Compiler_Range_Type.mk_range f {line=a;col=b} {line=c;col=d}
let range_0 : range = let z = Prims.parse_int "0" in mk_range "dummy" z z z z
let join_range r1 r2 = FStarC_Compiler_Range_Ops.union_ranges r1 r2

let explode (r:__range) =
  (r.use_range.file_name,
   r.use_range.start_pos.line,
   r.use_range.start_pos.col,
   r.use_range.end_pos.line,
   r.use_range.end_pos.col)

type ('Ar,'Amsg,'Ab) labeled = 'Ab
