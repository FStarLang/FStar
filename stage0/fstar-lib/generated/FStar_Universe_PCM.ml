open Prims
let raise : 'a . 'a FStar_PCM.pcm -> 'a FStar_Universe.raise_t FStar_PCM.pcm
  =
  fun p ->
    {
      FStar_PCM.p =
        {
          FStar_PCM.composable = ();
          FStar_PCM.op =
            (fun x ->
               fun y ->
                 FStar_Universe.raise_val
                   ((p.FStar_PCM.p).FStar_PCM.op
                      (FStar_Universe.downgrade_val x)
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
let raise_frame_preserving_upd :
  'a .
    'a FStar_PCM.pcm ->
      'a ->
        'a ->
          ('a, unit, unit, unit) FStar_PCM.frame_preserving_upd ->
            ('a FStar_Universe.raise_t, unit, unit, unit)
              FStar_PCM.frame_preserving_upd
  =
  fun p ->
    fun x ->
      fun y ->
        fun f ->
          fun v ->
            let u = f (FStar_Universe.downgrade_val v) in
            let v_new = FStar_Universe.raise_val u in v_new