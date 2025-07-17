open Prims
let read p s arr len i = Pulse_Lib_HigherArray_Core.mask_read arr i () () ()

//majorityocaml$
let majority p s votes len =
  let i = Pulse_Lib_HigherReference.alloc () Stdint.Uint64.one in
  let k = Pulse_Lib_HigherReference.alloc () Stdint.Uint64.one in
  let votes_0 =
    Pulse_Lib_HigherArray_Core.mask_read votes Stdint.Uint64.zero ()
      () () in
  let cand = Pulse_Lib_HigherReference.alloc () votes_0 in
  Pulse_Lib_Dv.while_
    (fun while_cond ->
        let vi = Pulse_Lib_HigherReference.read i () () in
        FStar_SizeT.lt vi len)
    (fun while_body ->
        let vi = Pulse_Lib_HigherReference.read i () () in
        let vk = Pulse_Lib_HigherReference.read k () () in
        let vcand = Pulse_Lib_HigherReference.read cand () () in
        let votes_i =
          Pulse_Lib_HigherArray_Core.mask_read votes vi () () () in
        if vk = Stdint.Uint64.zero
        then
          (Pulse_Lib_HigherReference.write cand votes_i ();
          Pulse_Lib_HigherReference.write k Stdint.Uint64.one ();
          Pulse_Lib_HigherReference.write i
            (FStar_SizeT.add vi Stdint.Uint64.one) ())
        else
          if votes_i = vcand
          then
            (Pulse_Lib_HigherReference.write k
              (FStar_SizeT.add vk Stdint.Uint64.one) ();
            Pulse_Lib_HigherReference.write i
              (FStar_SizeT.add vi Stdint.Uint64.one) ())
          else
            (Pulse_Lib_HigherReference.write k
              (FStar_SizeT.sub vk Stdint.Uint64.one) ();
            Pulse_Lib_HigherReference.write i
              (FStar_SizeT.add vi Stdint.Uint64.one) ()));
  (let vk = Pulse_Lib_HigherReference.read k () () in
    let vcand = Pulse_Lib_HigherReference.read cand () () in
    if vk = Stdint.Uint64.zero
    then FStar_Pervasives_Native.None
    else
      if
        FStar_SizeT.lt len
          (FStar_SizeT.mul (Stdint.Uint64.of_int (2)) vk)
      then FStar_Pervasives_Native.Some vcand
      else
        (Pulse_Lib_HigherReference.write i Stdint.Uint64.zero ();
        Pulse_Lib_HigherReference.write k Stdint.Uint64.zero ();
        Pulse_Lib_Dv.while_
          (fun while_cond ->
              let vi = Pulse_Lib_HigherReference.read i () () in
              FStar_SizeT.lt vi len)
          (fun while_body ->
              let vi = Pulse_Lib_HigherReference.read i () () in
              let vk1 = Pulse_Lib_HigherReference.read k () () in
              let votes_i =
                Pulse_Lib_HigherArray_Core.mask_read votes vi () () () in
              if votes_i = vcand
              then
                (Pulse_Lib_HigherReference.write k
                  (FStar_SizeT.add vk1 Stdint.Uint64.one) ();
                Pulse_Lib_HigherReference.write i
                  (FStar_SizeT.add vi Stdint.Uint64.one) ())
              else
                Pulse_Lib_HigherReference.write i
                  (FStar_SizeT.add vi Stdint.Uint64.one) ());
        (let vk1 = Pulse_Lib_HigherReference.read k () () in
          if
            FStar_SizeT.lt len
              (FStar_SizeT.mul (Stdint.Uint64.of_int (2)) vk1)
          then FStar_Pervasives_Native.Some vcand
          else FStar_Pervasives_Native.None)))
//majorityocamlend$
type u32_t = FStar_UInt32.t
let majority_mono p s votes len = majority () () votes len