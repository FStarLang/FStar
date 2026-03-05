open Prims
let union_rng (r1 : FStarC_Range_Type.rng) (r2 : FStarC_Range_Type.rng) :
  FStarC_Range_Type.rng=
  if r1.FStarC_Range_Type.file_name <> r2.FStarC_Range_Type.file_name
  then r2
  else
    (let start_pos =
       FStarC_Class_Ord.min FStarC_Range_Type.ord_pos
         r1.FStarC_Range_Type.start_pos r2.FStarC_Range_Type.start_pos in
     let end_pos =
       FStarC_Class_Ord.max FStarC_Range_Type.ord_pos
         r1.FStarC_Range_Type.end_pos r2.FStarC_Range_Type.end_pos in
     FStarC_Range_Type.mk_rng r1.FStarC_Range_Type.file_name start_pos
       end_pos)
let union_ranges (r1 : FStarC_Range_Type.range)
  (r2 : FStarC_Range_Type.range) : FStarC_Range_Type.range=
  let uu___ =
    union_rng r1.FStarC_Range_Type.def_range r2.FStarC_Range_Type.def_range in
  let uu___1 =
    union_rng r1.FStarC_Range_Type.use_range r2.FStarC_Range_Type.use_range in
  { FStarC_Range_Type.def_range = uu___; FStarC_Range_Type.use_range = uu___1
  }
let rng_included (r1 : FStarC_Range_Type.rng) (r2 : FStarC_Range_Type.rng) :
  Prims.bool=
  if r1.FStarC_Range_Type.file_name <> r2.FStarC_Range_Type.file_name
  then false
  else
    (let a =
       FStarC_Class_Ord.op_Less_Equals_Question FStarC_Range_Type.ord_pos
         r2.FStarC_Range_Type.start_pos r1.FStarC_Range_Type.start_pos in
     let b =
       FStarC_Class_Ord.op_Greater_Equals_Question FStarC_Range_Type.ord_pos
         r2.FStarC_Range_Type.end_pos r1.FStarC_Range_Type.end_pos in
     a && b)
let string_of_pos (pos : FStarC_Range_Type.pos) : Prims.string=
  let uu___ =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      pos.FStarC_Range_Type.line in
  let uu___1 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int
      pos.FStarC_Range_Type.col in
  FStarC_Format.fmt2 "%s,%s" uu___ uu___1
let file_of_range (r : FStarC_Range_Type.range) : Prims.string=
  (r.FStarC_Range_Type.def_range).FStarC_Range_Type.file_name
let set_file_of_range (r : FStarC_Range_Type.range) (f : Prims.string) :
  FStarC_Range_Type.range=
  {
    FStarC_Range_Type.def_range =
      (let uu___ = r.FStarC_Range_Type.def_range in
       {
         FStarC_Range_Type.file_name = (FStarC_Filepath.basename f);
         FStarC_Range_Type.start_pos = (uu___.FStarC_Range_Type.start_pos);
         FStarC_Range_Type.end_pos = (uu___.FStarC_Range_Type.end_pos)
       });
    FStarC_Range_Type.use_range = (r.FStarC_Range_Type.use_range)
  }
let string_of_rng (r : FStarC_Range_Type.rng) : Prims.string=
  let uu___ = string_of_pos r.FStarC_Range_Type.start_pos in
  let uu___1 = string_of_pos r.FStarC_Range_Type.end_pos in
  FStarC_Format.fmt3 "%s(%s-%s)" r.FStarC_Range_Type.file_name uu___ uu___1
let string_of_def_range (r : FStarC_Range_Type.range) : Prims.string=
  string_of_rng r.FStarC_Range_Type.def_range
let string_of_use_range (r : FStarC_Range_Type.range) : Prims.string=
  string_of_rng r.FStarC_Range_Type.use_range
let string_of_range (r : FStarC_Range_Type.range) : Prims.string=
  string_of_def_range r
let start_of_range (r : FStarC_Range_Type.range) : FStarC_Range_Type.pos=
  (r.FStarC_Range_Type.def_range).FStarC_Range_Type.start_pos
let end_of_range (r : FStarC_Range_Type.range) : FStarC_Range_Type.pos=
  (r.FStarC_Range_Type.def_range).FStarC_Range_Type.end_pos
let file_of_use_range (r : FStarC_Range_Type.range) : Prims.string=
  (r.FStarC_Range_Type.use_range).FStarC_Range_Type.file_name
let start_of_use_range (r : FStarC_Range_Type.range) : FStarC_Range_Type.pos=
  (r.FStarC_Range_Type.use_range).FStarC_Range_Type.start_pos
let end_of_use_range (r : FStarC_Range_Type.range) : FStarC_Range_Type.pos=
  (r.FStarC_Range_Type.use_range).FStarC_Range_Type.end_pos
let line_of_pos (p : FStarC_Range_Type.pos) : Prims.int=
  p.FStarC_Range_Type.line
let col_of_pos (p : FStarC_Range_Type.pos) : Prims.int=
  p.FStarC_Range_Type.col
let end_range (r : FStarC_Range_Type.range) : FStarC_Range_Type.range=
  FStarC_Range_Type.mk_range
    (r.FStarC_Range_Type.def_range).FStarC_Range_Type.file_name
    (r.FStarC_Range_Type.def_range).FStarC_Range_Type.end_pos
    (r.FStarC_Range_Type.def_range).FStarC_Range_Type.end_pos
let compare_rng (r1 : FStarC_Range_Type.rng) (r2 : FStarC_Range_Type.rng) :
  Prims.int=
  let fcomp =
    FStar_String.compare r1.FStarC_Range_Type.file_name
      r2.FStarC_Range_Type.file_name in
  if fcomp = Prims.int_zero
  then
    let start1 = r1.FStarC_Range_Type.start_pos in
    let start2 = r2.FStarC_Range_Type.start_pos in
    let lcomp = start1.FStarC_Range_Type.line - start2.FStarC_Range_Type.line in
    (if lcomp = Prims.int_zero
     then start1.FStarC_Range_Type.col - start2.FStarC_Range_Type.col
     else lcomp)
  else fcomp
let compare (r1 : FStarC_Range_Type.range) (r2 : FStarC_Range_Type.range) :
  Prims.int=
  compare_rng r1.FStarC_Range_Type.def_range r2.FStarC_Range_Type.def_range
let compare_use_range (r1 : FStarC_Range_Type.range)
  (r2 : FStarC_Range_Type.range) : Prims.int=
  compare_rng r1.FStarC_Range_Type.use_range r2.FStarC_Range_Type.use_range
let range_before_pos (m1 : FStarC_Range_Type.range)
  (p : FStarC_Range_Type.pos) : Prims.bool=
  FStarC_Class_Ord.op_Greater_Equals_Question FStarC_Range_Type.ord_pos p
    (end_of_range m1)
let end_of_line (p : FStarC_Range_Type.pos) : FStarC_Range_Type.pos=
  {
    FStarC_Range_Type.line = (p.FStarC_Range_Type.line);
    FStarC_Range_Type.col = FStarC_Util.max_int
  }
let extend_to_end_of_line (r : FStarC_Range_Type.range) :
  FStarC_Range_Type.range=
  FStarC_Range_Type.mk_range (file_of_range r) (start_of_range r)
    (end_of_line (end_of_range r))
let json_of_pos (pos : FStarC_Range_Type.pos) : FStarC_Json.json=
  FStarC_Json.JsonList
    [FStarC_Json.JsonInt (line_of_pos pos);
    FStarC_Json.JsonInt (col_of_pos pos)]
let json_of_range_fields (file : Prims.string) (b : FStarC_Range_Type.pos)
  (e : FStarC_Range_Type.pos) : FStarC_Json.json=
  FStarC_Json.JsonAssoc
    [("fname", (FStarC_Json.JsonStr file));
    ("beg", (json_of_pos b));
    ("end", (json_of_pos e))]
let json_of_use_range (r : FStarC_Range_Type.range) : FStarC_Json.json=
  json_of_range_fields (file_of_use_range r) (start_of_use_range r)
    (end_of_use_range r)
let json_of_def_range (r : FStarC_Range_Type.range) : FStarC_Json.json=
  json_of_range_fields (file_of_range r) (start_of_range r) (end_of_range r)
let intersect_rng (r1 : FStarC_Range_Type.rng) (r2 : FStarC_Range_Type.rng) :
  FStarC_Range_Type.rng=
  if r1.FStarC_Range_Type.file_name <> r2.FStarC_Range_Type.file_name
  then r2
  else
    (let start_pos =
       FStarC_Class_Ord.max FStarC_Range_Type.ord_pos
         r1.FStarC_Range_Type.start_pos r2.FStarC_Range_Type.start_pos in
     let end_pos =
       FStarC_Class_Ord.min FStarC_Range_Type.ord_pos
         r1.FStarC_Range_Type.end_pos r2.FStarC_Range_Type.end_pos in
     let uu___1 =
       FStarC_Class_Ord.op_Greater_Equals_Question FStarC_Range_Type.ord_pos
         start_pos end_pos in
     if uu___1
     then r2
     else
       FStarC_Range_Type.mk_rng r1.FStarC_Range_Type.file_name start_pos
         end_pos)
let intersect_ranges (r1 : FStarC_Range_Type.range)
  (r2 : FStarC_Range_Type.range) : FStarC_Range_Type.range=
  let uu___ =
    intersect_rng r1.FStarC_Range_Type.def_range
      r2.FStarC_Range_Type.def_range in
  let uu___1 =
    intersect_rng r1.FStarC_Range_Type.use_range
      r2.FStarC_Range_Type.use_range in
  { FStarC_Range_Type.def_range = uu___; FStarC_Range_Type.use_range = uu___1
  }
let bound_range (r : FStarC_Range_Type.range)
  (bound : FStarC_Range_Type.range) : FStarC_Range_Type.range=
  intersect_ranges r bound
let showable_range : FStarC_Range_Type.range FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = string_of_range }
let pretty_range : FStarC_Range_Type.range FStarC_Class_PP.pretty=
  {
    FStarC_Class_PP.pp =
      (fun r ->
         let uu___ = string_of_range r in FStar_Pprint.doc_of_string uu___)
  }
let refind_rng (r : FStarC_Range_Type.rng) : FStarC_Range_Type.rng=
  let uu___ =
    let uu___1 = FStarC_Options_Ext.enabled "fstar:no_absolute_paths" in
    if uu___1
    then r.FStarC_Range_Type.file_name
    else FStarC_Find.refind_file r.FStarC_Range_Type.file_name in
  {
    FStarC_Range_Type.file_name = uu___;
    FStarC_Range_Type.start_pos = (r.FStarC_Range_Type.start_pos);
    FStarC_Range_Type.end_pos = (r.FStarC_Range_Type.end_pos)
  }
let refind_range (r : FStarC_Range_Type.range) : FStarC_Range_Type.range=
  let uu___ = refind_rng r.FStarC_Range_Type.def_range in
  let uu___1 = refind_rng r.FStarC_Range_Type.use_range in
  { FStarC_Range_Type.def_range = uu___; FStarC_Range_Type.use_range = uu___1
  }
