open Prims
let raise (p : 'a FStar_PCM.pcm) : 'a FStar_Universe.raise_t FStar_PCM.pcm=
  {
    FStar_PCM.p =
      {
        FStar_PCM.composable = ();
        FStar_PCM.op =
          (fun x y ->
             FStar_Universe.raise_val
               ((p.FStar_PCM.p).FStar_PCM.op (FStar_Universe.downgrade_val x)
                  (FStar_Universe.downgrade_val y)));
        FStar_PCM.one =
          (FStar_Universe.raise_val (p.FStar_PCM.p).FStar_PCM.one)
      };
    FStar_PCM.comm = ();
    FStar_PCM.assoc = ();
    FStar_PCM.assoc_r = ();
    FStar_PCM.is_unit = ();
    FStar_PCM.refine = ()
  }
let raise_frame_preserving_upd (p : 'a FStar_PCM.pcm) (x : 'a) (y : 'a)
  (f : ('a, Obj.t, Obj.t, Obj.t) FStar_PCM.frame_preserving_upd) :
  ('a FStar_Universe.raise_t, Obj.t, Obj.t, Obj.t)
    FStar_PCM.frame_preserving_upd=
  fun v ->
    let u = f (FStar_Universe.downgrade_val v) in
    let v_new = FStar_Universe.raise_val u in v_new
