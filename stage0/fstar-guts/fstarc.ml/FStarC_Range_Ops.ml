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
    (FStarC_Class_Ord.op_Less_Equals_Question FStarC_Range_Type.ord_pos
       r2.FStarC_Range_Type.start_pos r1.FStarC_Range_Type.start_pos)
      &&
      (FStarC_Class_Ord.op_Greater_Equals_Question FStarC_Range_Type.ord_pos
         r2.FStarC_Range_Type.end_pos r1.FStarC_Range_Type.end_pos)
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
  let uu___ =
    let uu___1 = r.FStarC_Range_Type.def_range in
    let uu___2 = FStarC_Filepath.basename f in
    {
      FStarC_Range_Type.file_name = uu___2;
      FStarC_Range_Type.start_pos = (uu___1.FStarC_Range_Type.start_pos);
      FStarC_Range_Type.end_pos = (uu___1.FStarC_Range_Type.end_pos)
    } in
  {
    FStarC_Range_Type.def_range = uu___;
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
  let uu___ = end_of_range m1 in
  FStarC_Class_Ord.op_Greater_Equals_Question FStarC_Range_Type.ord_pos p
    uu___
let end_of_line (p : FStarC_Range_Type.pos) : FStarC_Range_Type.pos=
  {
    FStarC_Range_Type.line = (p.FStarC_Range_Type.line);
    FStarC_Range_Type.col = FStarC_Util.max_int
  }
let extend_to_end_of_line (r : FStarC_Range_Type.range) :
  FStarC_Range_Type.range=
  let uu___ = file_of_range r in
  let uu___1 = start_of_range r in
  let uu___2 = let uu___3 = end_of_range r in end_of_line uu___3 in
  FStarC_Range_Type.mk_range uu___ uu___1 uu___2
let json_of_pos (pos : FStarC_Range_Type.pos) : FStarC_Json.json=
  let uu___ =
    let uu___1 = let uu___2 = line_of_pos pos in FStarC_Json.JsonInt uu___2 in
    let uu___2 =
      let uu___3 = let uu___4 = col_of_pos pos in FStarC_Json.JsonInt uu___4 in
      [uu___3] in
    uu___1 :: uu___2 in
  FStarC_Json.JsonList uu___
let json_of_range_fields (file : Prims.string) (b : FStarC_Range_Type.pos)
  (e : FStarC_Range_Type.pos) : FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 = let uu___3 = json_of_pos b in ("beg", uu___3) in
      let uu___3 =
        let uu___4 = let uu___5 = json_of_pos e in ("end", uu___5) in
        [uu___4] in
      uu___2 :: uu___3 in
    ("fname", (FStarC_Json.JsonStr file)) :: uu___1 in
  FStarC_Json.JsonAssoc uu___
let json_of_use_range (r : FStarC_Range_Type.range) : FStarC_Json.json=
  let uu___ = file_of_use_range r in
  let uu___1 = start_of_use_range r in
  let uu___2 = end_of_use_range r in json_of_range_fields uu___ uu___1 uu___2
let json_of_def_range (r : FStarC_Range_Type.range) : FStarC_Json.json=
  let uu___ = file_of_range r in
  let uu___1 = start_of_range r in
  let uu___2 = end_of_range r in json_of_range_fields uu___ uu___1 uu___2
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
