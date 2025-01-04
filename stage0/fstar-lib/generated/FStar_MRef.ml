open Prims
type ('uuuuu, 'p, 'rel) stable = unit
type ('a, 'b, 'r, 'p, 'h) p_pred = unit
type ('uuuuu, 'uuuuu1, 'r, 'p) token = unit FStar_ST.witnessed
let witness_token :
  'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) FStar_ST.mref -> unit -> unit =
  fun m -> fun p -> FStar_ST.gst_recall (); FStar_ST.gst_witness ()
let recall_token :
  'uuuuu 'uuuuu1 . ('uuuuu, 'uuuuu1) FStar_ST.mref -> unit -> unit =
  fun m -> fun p -> FStar_ST.gst_recall ()
type ('a, 'rel) spred = unit
let recall : 'p . unit -> unit = fun uu___ -> FStar_ST.gst_recall ()
let witness : 'p . unit -> unit = fun uu___ -> FStar_ST.gst_witness ()