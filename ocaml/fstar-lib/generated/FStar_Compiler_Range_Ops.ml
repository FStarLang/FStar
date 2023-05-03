open Prims
let (union_rng :
  FStar_Compiler_Range_Type.rng ->
    FStar_Compiler_Range_Type.rng -> FStar_Compiler_Range_Type.rng)
  =
  fun r1 ->
    fun r2 ->
      if
        r1.FStar_Compiler_Range_Type.file_name <>
          r2.FStar_Compiler_Range_Type.file_name
      then r2
      else
        (let start_pos =
           if
             FStar_Compiler_Range_Type.pos_geq
               r1.FStar_Compiler_Range_Type.start_pos
               r2.FStar_Compiler_Range_Type.start_pos
           then r2.FStar_Compiler_Range_Type.start_pos
           else r1.FStar_Compiler_Range_Type.start_pos in
         let end_pos =
           if
             FStar_Compiler_Range_Type.pos_geq
               r1.FStar_Compiler_Range_Type.end_pos
               r2.FStar_Compiler_Range_Type.end_pos
           then r1.FStar_Compiler_Range_Type.end_pos
           else r2.FStar_Compiler_Range_Type.end_pos in
         FStar_Compiler_Range_Type.mk_rng
           r1.FStar_Compiler_Range_Type.file_name start_pos end_pos)
let (union_ranges :
  FStar_Compiler_Range_Type.range ->
    FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.range)
  =
  fun r1 ->
    fun r2 ->
      let uu___ =
        union_rng r1.FStar_Compiler_Range_Type.def_range
          r2.FStar_Compiler_Range_Type.def_range in
      let uu___1 =
        union_rng r1.FStar_Compiler_Range_Type.use_range
          r2.FStar_Compiler_Range_Type.use_range in
      {
        FStar_Compiler_Range_Type.def_range = uu___;
        FStar_Compiler_Range_Type.use_range = uu___1
      }
let (rng_included :
  FStar_Compiler_Range_Type.rng ->
    FStar_Compiler_Range_Type.rng -> Prims.bool)
  =
  fun r1 ->
    fun r2 ->
      if
        r1.FStar_Compiler_Range_Type.file_name <>
          r2.FStar_Compiler_Range_Type.file_name
      then false
      else
        (FStar_Compiler_Range_Type.pos_geq
           r1.FStar_Compiler_Range_Type.start_pos
           r2.FStar_Compiler_Range_Type.start_pos)
          &&
          (FStar_Compiler_Range_Type.pos_geq
             r2.FStar_Compiler_Range_Type.end_pos
             r1.FStar_Compiler_Range_Type.end_pos)
let (string_of_pos : FStar_Compiler_Range_Type.pos -> Prims.string) =
  fun pos ->
    let uu___ =
      FStar_Compiler_Util.string_of_int pos.FStar_Compiler_Range_Type.line in
    let uu___1 =
      FStar_Compiler_Util.string_of_int pos.FStar_Compiler_Range_Type.col in
    FStar_Compiler_Util.format2 "%s,%s" uu___ uu___1
let (string_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    let uu___ = FStar_Options.ide () in
    if uu___
    then
      try
        (fun uu___1 ->
           match () with
           | () ->
               let uu___2 =
                 let uu___3 = FStar_Compiler_Util.basename f in
                 FStar_Options.find_file uu___3 in
               (match uu___2 with
                | FStar_Pervasives_Native.None -> f
                | FStar_Pervasives_Native.Some absolute_path -> absolute_path))
          ()
      with | uu___1 -> f
    else f
let (file_of_range : FStar_Compiler_Range_Type.range -> Prims.string) =
  fun r ->
    let f =
      (r.FStar_Compiler_Range_Type.def_range).FStar_Compiler_Range_Type.file_name in
    string_of_file_name f
let (set_file_of_range :
  FStar_Compiler_Range_Type.range ->
    Prims.string -> FStar_Compiler_Range_Type.range)
  =
  fun r ->
    fun f ->
      {
        FStar_Compiler_Range_Type.def_range =
          (let uu___ = r.FStar_Compiler_Range_Type.def_range in
           {
             FStar_Compiler_Range_Type.file_name = f;
             FStar_Compiler_Range_Type.start_pos =
               (uu___.FStar_Compiler_Range_Type.start_pos);
             FStar_Compiler_Range_Type.end_pos =
               (uu___.FStar_Compiler_Range_Type.end_pos)
           });
        FStar_Compiler_Range_Type.use_range =
          (r.FStar_Compiler_Range_Type.use_range)
      }
let (string_of_rng : FStar_Compiler_Range_Type.rng -> Prims.string) =
  fun r ->
    let uu___ = string_of_file_name r.FStar_Compiler_Range_Type.file_name in
    let uu___1 = string_of_pos r.FStar_Compiler_Range_Type.start_pos in
    let uu___2 = string_of_pos r.FStar_Compiler_Range_Type.end_pos in
    FStar_Compiler_Util.format3 "%s(%s-%s)" uu___ uu___1 uu___2
let (string_of_def_range : FStar_Compiler_Range_Type.range -> Prims.string) =
  fun r -> string_of_rng r.FStar_Compiler_Range_Type.def_range
let (string_of_use_range : FStar_Compiler_Range_Type.range -> Prims.string) =
  fun r -> string_of_rng r.FStar_Compiler_Range_Type.use_range
let (string_of_range : FStar_Compiler_Range_Type.range -> Prims.string) =
  fun r -> string_of_def_range r
let (start_of_range :
  FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.pos) =
  fun r ->
    (r.FStar_Compiler_Range_Type.def_range).FStar_Compiler_Range_Type.start_pos
let (end_of_range :
  FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.pos) =
  fun r ->
    (r.FStar_Compiler_Range_Type.def_range).FStar_Compiler_Range_Type.end_pos
let (file_of_use_range : FStar_Compiler_Range_Type.range -> Prims.string) =
  fun r ->
    (r.FStar_Compiler_Range_Type.use_range).FStar_Compiler_Range_Type.file_name
let (start_of_use_range :
  FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.pos) =
  fun r ->
    (r.FStar_Compiler_Range_Type.use_range).FStar_Compiler_Range_Type.start_pos
let (end_of_use_range :
  FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.pos) =
  fun r ->
    (r.FStar_Compiler_Range_Type.use_range).FStar_Compiler_Range_Type.end_pos
let (line_of_pos : FStar_Compiler_Range_Type.pos -> Prims.int) =
  fun p -> p.FStar_Compiler_Range_Type.line
let (col_of_pos : FStar_Compiler_Range_Type.pos -> Prims.int) =
  fun p -> p.FStar_Compiler_Range_Type.col
let (end_range :
  FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.range) =
  fun r ->
    FStar_Compiler_Range_Type.mk_range
      (r.FStar_Compiler_Range_Type.def_range).FStar_Compiler_Range_Type.file_name
      (r.FStar_Compiler_Range_Type.def_range).FStar_Compiler_Range_Type.end_pos
      (r.FStar_Compiler_Range_Type.def_range).FStar_Compiler_Range_Type.end_pos
let (compare_rng :
  FStar_Compiler_Range_Type.rng -> FStar_Compiler_Range_Type.rng -> Prims.int)
  =
  fun r1 ->
    fun r2 ->
      let fcomp =
        FStar_String.compare r1.FStar_Compiler_Range_Type.file_name
          r2.FStar_Compiler_Range_Type.file_name in
      if fcomp = Prims.int_zero
      then
        let start1 = r1.FStar_Compiler_Range_Type.start_pos in
        let start2 = r2.FStar_Compiler_Range_Type.start_pos in
        let lcomp =
          start1.FStar_Compiler_Range_Type.line -
            start2.FStar_Compiler_Range_Type.line in
        (if lcomp = Prims.int_zero
         then
           start1.FStar_Compiler_Range_Type.col -
             start2.FStar_Compiler_Range_Type.col
         else lcomp)
      else fcomp
let (compare :
  FStar_Compiler_Range_Type.range ->
    FStar_Compiler_Range_Type.range -> Prims.int)
  =
  fun r1 ->
    fun r2 ->
      compare_rng r1.FStar_Compiler_Range_Type.def_range
        r2.FStar_Compiler_Range_Type.def_range
let (compare_use_range :
  FStar_Compiler_Range_Type.range ->
    FStar_Compiler_Range_Type.range -> Prims.int)
  =
  fun r1 ->
    fun r2 ->
      compare_rng r1.FStar_Compiler_Range_Type.use_range
        r2.FStar_Compiler_Range_Type.use_range
let (range_before_pos :
  FStar_Compiler_Range_Type.range ->
    FStar_Compiler_Range_Type.pos -> Prims.bool)
  =
  fun m1 ->
    fun p ->
      let uu___ = end_of_range m1 in
      FStar_Compiler_Range_Type.pos_geq p uu___
let (end_of_line :
  FStar_Compiler_Range_Type.pos -> FStar_Compiler_Range_Type.pos) =
  fun p ->
    {
      FStar_Compiler_Range_Type.line = (p.FStar_Compiler_Range_Type.line);
      FStar_Compiler_Range_Type.col = FStar_Compiler_Util.max_int
    }
let (extend_to_end_of_line :
  FStar_Compiler_Range_Type.range -> FStar_Compiler_Range_Type.range) =
  fun r ->
    let uu___ = file_of_range r in
    let uu___1 = start_of_range r in
    let uu___2 = let uu___3 = end_of_range r in end_of_line uu___3 in
    FStar_Compiler_Range_Type.mk_range uu___ uu___1 uu___2
let (json_of_pos : FStar_Compiler_Range_Type.pos -> FStar_Json.json) =
  fun pos ->
    let uu___ =
      let uu___1 = let uu___2 = line_of_pos pos in FStar_Json.JsonInt uu___2 in
      let uu___2 =
        let uu___3 = let uu___4 = col_of_pos pos in FStar_Json.JsonInt uu___4 in
        [uu___3] in
      uu___1 :: uu___2 in
    FStar_Json.JsonList uu___
let (json_of_range_fields :
  Prims.string ->
    FStar_Compiler_Range_Type.pos ->
      FStar_Compiler_Range_Type.pos -> FStar_Json.json)
  =
  fun file ->
    fun b ->
      fun e ->
        let uu___ =
          let uu___1 =
            let uu___2 = let uu___3 = json_of_pos b in ("beg", uu___3) in
            let uu___3 =
              let uu___4 = let uu___5 = json_of_pos e in ("end", uu___5) in
              [uu___4] in
            uu___2 :: uu___3 in
          ("fname", (FStar_Json.JsonStr file)) :: uu___1 in
        FStar_Json.JsonAssoc uu___
let (json_of_use_range : FStar_Compiler_Range_Type.range -> FStar_Json.json)
  =
  fun r ->
    let uu___ = file_of_use_range r in
    let uu___1 = start_of_use_range r in
    let uu___2 = end_of_use_range r in
    json_of_range_fields uu___ uu___1 uu___2
let (json_of_def_range : FStar_Compiler_Range_Type.range -> FStar_Json.json)
  =
  fun r ->
    let uu___ = file_of_range r in
    let uu___1 = start_of_range r in
    let uu___2 = end_of_range r in json_of_range_fields uu___ uu___1 uu___2