open Prims
type file_name = Prims.string[@@deriving yojson,show]
type pos = {
  line: Prims.int ;
  col: Prims.int }[@@deriving yojson,show]
let __proj__Mkpos__item__line (projectee : pos) : Prims.int=
  match projectee with | { line; col;_} -> line
let __proj__Mkpos__item__col (projectee : pos) : Prims.int=
  match projectee with | { line; col;_} -> col
let max (i : Prims.int) (j : Prims.int) : Prims.int= if i < j then j else i
let compare_pos (p1 : pos) (p2 : pos) : FStarC_Order.order=
  let uu___ = FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_int p1.line p2.line in
  FStarC_Order.lex uu___
    (fun uu___1 ->
       FStarC_Class_Ord.cmp FStarC_Class_Ord.ord_int p1.col p2.col)
let deq_pos : pos FStarC_Class_Deq.deq=
  { FStarC_Class_Deq.op_Equals_Question = (=) }
let ord_pos : pos FStarC_Class_Ord.ord=
  { FStarC_Class_Ord.super = deq_pos; FStarC_Class_Ord.cmp = compare_pos }
type rng = {
  file_name: file_name ;
  start_pos: pos ;
  end_pos: pos }[@@deriving yojson,show]
let __proj__Mkrng__item__file_name (projectee : rng) : file_name=
  match projectee with
  | { file_name = file_name1; start_pos; end_pos;_} -> file_name1
let __proj__Mkrng__item__start_pos (projectee : rng) : pos=
  match projectee with
  | { file_name = file_name1; start_pos; end_pos;_} -> start_pos
let __proj__Mkrng__item__end_pos (projectee : rng) : pos=
  match projectee with
  | { file_name = file_name1; start_pos; end_pos;_} -> end_pos
type range = {
  def_range: rng ;
  use_range: rng }[@@deriving yojson,show]
let __proj__Mkrange__item__def_range (projectee : range) : rng=
  match projectee with | { def_range; use_range;_} -> def_range
let __proj__Mkrange__item__use_range (projectee : range) : rng=
  match projectee with | { def_range; use_range;_} -> use_range
type t = range
let dummy_pos : pos= { line = Prims.int_zero; col = Prims.int_zero }
let dummy_rng : rng=
  { file_name = "dummy"; start_pos = dummy_pos; end_pos = dummy_pos }
let dummyRange : range= { def_range = dummy_rng; use_range = dummy_rng }
let use_range (r : range) : rng= r.use_range
let def_range (r : range) : rng= r.def_range
let range_of_rng (d : rng) (u : rng) : range=
  { def_range = d; use_range = u }
let set_use_range (r2 : range) (use_rng : rng) : range=
  if use_rng <> dummy_rng
  then
    {
      def_range =
        ((if r2.def_range = dummy_rng then use_rng else r2.def_range));
      use_range = use_rng
    }
  else r2
let set_def_range (r2 : range) (def_rng : rng) : range=
  if def_rng <> dummy_rng
  then { def_range = def_rng; use_range = (r2.use_range) }
  else r2
let mk_pos (l : Prims.int) (c : Prims.int) : pos=
  { line = (max Prims.int_zero l); col = (max Prims.int_zero c) }
let mk_rng (file_name1 : Prims.string) (start_pos : pos) (end_pos : pos) :
  rng=
  let uu___ = FStarC_Filepath.basename file_name1 in
  { file_name = uu___; start_pos; end_pos }
let mk_range (f : Prims.string) (b : pos) (e : pos) : range=
  let r = mk_rng f b e in range_of_rng r r
let json_of_pos (r : pos) : FStarC_Json.json=
  FStarC_Json.JsonAssoc
    [("line", (FStarC_Json.JsonInt (r.line)));
    ("col", (FStarC_Json.JsonInt (r.col)))]
let json_of_rng (r : rng) : FStarC_Json.json=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = json_of_pos r.start_pos in ("start_pos", uu___3) in
      let uu___3 =
        let uu___4 =
          let uu___5 = json_of_pos r.end_pos in ("end_pos", uu___5) in
        [uu___4] in
      uu___2 :: uu___3 in
    ("file_name", (FStarC_Json.JsonStr (r.file_name))) :: uu___1 in
  FStarC_Json.JsonAssoc uu___
let json_of_range (r : range) : FStarC_Json.json=
  let uu___ =
    let uu___1 = let uu___2 = json_of_rng r.def_range in ("def", uu___2) in
    let uu___2 =
      let uu___3 = let uu___4 = json_of_rng r.use_range in ("use", uu___4) in
      [uu___3] in
    uu___1 :: uu___2 in
  FStarC_Json.JsonAssoc uu___
