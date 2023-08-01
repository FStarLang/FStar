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
let (pos_geq : pos -> pos -> Prims.bool) =
  fun p1 ->
    fun p2 ->
      (p1.line > p2.line) || ((p1.line = p2.line) && (p1.col >= p2.col))
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
  { file_name = " dummy"; start_pos = dummy_pos; end_pos = dummy_pos }
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
let (mk_rng : file_name -> pos -> pos -> rng) =
  fun file_name1 ->
    fun start_pos ->
      fun end_pos -> { file_name = file_name1; start_pos; end_pos }
let (mk_range : Prims.string -> pos -> pos -> range) =
  fun f -> fun b -> fun e -> let r = mk_rng f b e in range_of_rng r r