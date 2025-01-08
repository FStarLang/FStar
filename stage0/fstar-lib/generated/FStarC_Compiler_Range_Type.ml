open Prims
type file_name = Prims.string[@@deriving yojson,show]
type pos = {
  line: Prims.int ;
  col: Prims.int }[@@deriving yojson,show]
let (__proj__Mkpos__item__line : pos -> Prims.int) =
  fun projectee -> match projectee with | { line; col;_} -> line
let (__proj__Mkpos__item__col : pos -> Prims.int) =
  fun projectee -> match projectee with | { line; col;_} -> col
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun i -> fun j -> if i < j then j else i
let (compare_pos : pos -> pos -> FStarC_Compiler_Order.order) =
  fun p1 ->
    fun p2 ->
      let uu___ =
        FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_int p1.line p2.line in
      FStarC_Compiler_Order.lex uu___
        (fun uu___1 ->
           FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_int p1.col p2.col)
let (deq_pos : pos FStarC_Class_Deq.deq) =
  { FStarC_Class_Deq.op_Equals_Question = (=) }
let (ord_pos : pos FStarC_Class_Ord.ord) =
  { FStarC_Class_Ord.super = deq_pos; FStarC_Class_Ord.cmp = compare_pos }
type rng = {
  file_name: file_name ;
  start_pos: pos ;
  end_pos: pos }[@@deriving yojson,show]
let (__proj__Mkrng__item__file_name : rng -> file_name) =
  fun projectee ->
    match projectee with
    | { file_name = file_name1; start_pos; end_pos;_} -> file_name1
let (__proj__Mkrng__item__start_pos : rng -> pos) =
  fun projectee ->
    match projectee with
    | { file_name = file_name1; start_pos; end_pos;_} -> start_pos
let (__proj__Mkrng__item__end_pos : rng -> pos) =
  fun projectee ->
    match projectee with
    | { file_name = file_name1; start_pos; end_pos;_} -> end_pos
type range = {
  def_range: rng ;
  use_range: rng }[@@deriving yojson,show]
let (__proj__Mkrange__item__def_range : range -> rng) =
  fun projectee ->
    match projectee with | { def_range; use_range;_} -> def_range
let (__proj__Mkrange__item__use_range : range -> rng) =
  fun projectee ->
    match projectee with | { def_range; use_range;_} -> use_range
let (dummy_pos : pos) = { line = Prims.int_zero; col = Prims.int_zero }
let (dummy_rng : rng) =
  { file_name = "dummy"; start_pos = dummy_pos; end_pos = dummy_pos }
let (dummyRange : range) = { def_range = dummy_rng; use_range = dummy_rng }
let (use_range : range -> rng) = fun r -> r.use_range
let (def_range : range -> rng) = fun r -> r.def_range
let (range_of_rng : rng -> rng -> range) =
  fun d -> fun u -> { def_range = d; use_range = u }
let (set_use_range : range -> rng -> range) =
  fun r2 ->
    fun use_rng ->
      if use_rng <> dummy_rng
      then { def_range = (r2.def_range); use_range = use_rng }
      else r2
let (set_def_range : range -> rng -> range) =
  fun r2 ->
    fun def_rng ->
      if def_rng <> dummy_rng
      then { def_range = def_rng; use_range = (r2.use_range) }
      else r2
let (mk_pos : Prims.int -> Prims.int -> pos) =
  fun l ->
    fun c -> { line = (max Prims.int_zero l); col = (max Prims.int_zero c) }
let (mk_rng : Prims.string -> pos -> pos -> rng) =
  fun file_name1 ->
    fun start_pos ->
      fun end_pos -> { file_name = file_name1; start_pos; end_pos }
let (mk_range : Prims.string -> pos -> pos -> range) =
  fun f -> fun b -> fun e -> let r = mk_rng f b e in range_of_rng r r
let (string_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    let uu___ =
      let uu___1 = FStarC_Options_Ext.get "fstar:no_absolute_paths" in
      uu___1 = "1" in
    if uu___
    then FStarC_Compiler_Util.basename f
    else
      (let uu___2 = FStarC_Options.ide () in
       if uu___2
       then
         try
           (fun uu___3 ->
              match () with
              | () ->
                  let uu___4 =
                    let uu___5 = FStarC_Compiler_Util.basename f in
                    FStarC_Find.find_file uu___5 in
                  (match uu___4 with
                   | FStar_Pervasives_Native.None -> f
                   | FStar_Pervasives_Native.Some absolute_path ->
                       absolute_path)) ()
         with | uu___3 -> f
       else f)
let (json_of_pos : pos -> FStarC_Json.json) =
  fun r ->
    FStarC_Json.JsonAssoc
      [("line", (FStarC_Json.JsonInt (r.line)));
      ("col", (FStarC_Json.JsonInt (r.col)))]
let (json_of_rng : rng -> FStarC_Json.json) =
  fun r ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = string_of_file_name r.file_name in
          FStarC_Json.JsonStr uu___3 in
        ("file_name", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 = json_of_pos r.start_pos in ("start_pos", uu___4) in
        let uu___4 =
          let uu___5 =
            let uu___6 = json_of_pos r.end_pos in ("end_pos", uu___6) in
          [uu___5] in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStarC_Json.JsonAssoc uu___
let (json_of_range : range -> FStarC_Json.json) =
  fun r ->
    let uu___ =
      let uu___1 = let uu___2 = json_of_rng r.def_range in ("def", uu___2) in
      let uu___2 =
        let uu___3 = let uu___4 = json_of_rng r.use_range in ("use", uu___4) in
        [uu___3] in
      uu___1 :: uu___2 in
    FStarC_Json.JsonAssoc uu___