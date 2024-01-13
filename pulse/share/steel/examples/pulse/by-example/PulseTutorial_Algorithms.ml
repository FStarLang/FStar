open Prims
let read p s arr len i = Pulse_Lib_Array_Core.op_Array_Access arr i () ()

//majorityocaml$
let majority p s votes len =
  let i = Pulse_Lib_Reference.alloc (FStar_SizeT.uint_to_t Prims.int_one) in
  let k = Pulse_Lib_Reference.alloc (FStar_SizeT.uint_to_t Prims.int_one) in
  let votes_0 =
    Pulse_Lib_Array_Core.op_Array_Access votes Stdint.Uint64.zero () () in
  let cand = Pulse_Lib_Reference.alloc votes_0 in
  let uu___ =
    Pulse_Lib_Core.while_
      (fun _ ->
         let vi = Pulse_Lib_Reference.op_Bang i () () in
         FStar_SizeT.lt vi len)
      (fun _ ->
         let vi = Pulse_Lib_Reference.op_Bang i () () in
         let vk = Pulse_Lib_Reference.op_Bang k () () in
         let vcand = Pulse_Lib_Reference.op_Bang cand () () in
         let votes_i = Pulse_Lib_Array_Core.op_Array_Access votes vi () () in
         let uu___ = () in
         let _bind_c =
           if vk = Stdint.Uint64.zero
           then
             let uu___1 = Pulse_Lib_Reference.op_Colon_Equals cand votes_i () in
             let uu___2 =
               Pulse_Lib_Reference.op_Colon_Equals k Stdint.Uint64.one () in
             Pulse_Lib_Reference.op_Colon_Equals i
               (FStar_SizeT.add vi Stdint.Uint64.one) ()
           else
             if votes_i = vcand
             then
               (let uu___1 =
                  Pulse_Lib_Reference.op_Colon_Equals k
                    (FStar_SizeT.add vk Stdint.Uint64.one) () in
                Pulse_Lib_Reference.op_Colon_Equals i
                  (FStar_SizeT.add vi Stdint.Uint64.one) ())
             else
               (let uu___1 =
                  Pulse_Lib_Reference.op_Colon_Equals k
                    (FStar_SizeT.sub vk Stdint.Uint64.one) () in
                Pulse_Lib_Reference.op_Colon_Equals i
                  (FStar_SizeT.add vi Stdint.Uint64.one) ()) in
         let _while_b = () in ()) in
  let vk = Pulse_Lib_Reference.op_Bang k () () in
  let vcand = Pulse_Lib_Reference.op_Bang cand () () in
  let _bind_c =
    if vk = Stdint.Uint64.zero
    then FStar_Pervasives_Native.None
    else
      if FStar_SizeT.lt len (FStar_SizeT.mul (Stdint.Uint64.of_int (2)) vk)
      then FStar_Pervasives_Native.Some vcand
      else
        (let uu___1 =
           Pulse_Lib_Reference.op_Colon_Equals i Stdint.Uint64.zero () in
         let uu___2 =
           Pulse_Lib_Reference.op_Colon_Equals k Stdint.Uint64.zero () in
         let uu___3 =
           Pulse_Lib_Core.while_
             (fun _ ->
                let vi = Pulse_Lib_Reference.op_Bang i () () in
                FStar_SizeT.lt vi len)
             (fun _ ->
                let vi = Pulse_Lib_Reference.op_Bang i () () in
                let vk1 = Pulse_Lib_Reference.op_Bang k () () in
                let votes_i =
                  Pulse_Lib_Array_Core.op_Array_Access votes vi () () in
                let uu___3 = () in
                let _bind_c =
                  if votes_i = vcand
                  then
                    let uu___4 =
                      Pulse_Lib_Reference.op_Colon_Equals k
                        (FStar_SizeT.add vk1 Stdint.Uint64.one) () in
                    Pulse_Lib_Reference.op_Colon_Equals i
                      (FStar_SizeT.add vi Stdint.Uint64.one) ()
                  else
                    Pulse_Lib_Reference.op_Colon_Equals i
                      (FStar_SizeT.add vi Stdint.Uint64.one) () in
                let _while_b = () in ()) in
         let vk1 = Pulse_Lib_Reference.op_Bang k () () in
         if
           FStar_SizeT.lt len
             (FStar_SizeT.mul (Stdint.Uint64.of_int (2)) vk1)
         then FStar_Pervasives_Native.Some vcand
         else FStar_Pervasives_Native.None) in
  let cand1 = _bind_c in let k1 = cand1 in let i1 = k1 in i1
//majorityocamlend$
type u32_t = FStar_UInt32.t
let majority_mono p s votes len = majority () () votes len