open Prims
type ('uuuuu, 'uuuuu1, 'f, 'g) inverses = unit
type ('a, 'b) view =
  | View of Prims.pos * unit * unit 
let uu___is_View : 'a 'b . ('a, 'b) view -> Prims.bool =
  fun projectee -> true
let __proj__View__item__n : 'a 'b . ('a, 'b) view -> Prims.pos =
  fun projectee -> match projectee with | View (n, get, put) -> n
type 'dest buffer =
  | Buffer of unit * Obj.t LowStar_BufferView_Down.buffer * (Obj.t, 'dest)
  view 
let uu___is_Buffer : 'dest . 'dest buffer -> Prims.bool =
  fun projectee -> true
let __proj__Buffer__item__down_buf :
  'dest . 'dest buffer -> unit LowStar_BufferView_Down.buffer =
  fun uu___ ->
    (fun projectee ->
       match projectee with | Buffer (src, down_buf, v) -> Obj.magic down_buf)
      uu___
let __proj__Buffer__item__v : 'dest . 'dest buffer -> (unit, 'dest) view =
  fun uu___ ->
    (fun projectee ->
       match projectee with | Buffer (src, down_buf, v) -> Obj.magic v) uu___
type ('b, 'bv) buffer_src = Obj.t
let as_down_buffer : 'b . 'b buffer -> Obj.t LowStar_BufferView_Down.buffer =
  fun uu___ ->
    (fun bv -> Obj.magic (__proj__Buffer__item__down_buf bv)) uu___
let get_view : 'b . 'b buffer -> (Obj.t, 'b) view =
  fun uu___ -> (fun v -> Obj.magic (__proj__Buffer__item__v v)) uu___
type ('b, 'h, 'vb) live =
  (unit, unit, unit, unit, unit) LowStar_Monotonic_Buffer.live
type ('b, 'vb, 'h, 'hu) modifies =
  (unit, unit, unit) LowStar_Monotonic_Buffer.modifies