let extractor
  : FStar_Extraction_ML_Modul.extension_extractor
  = fun uenv sigelt tm ->
      let ps = 
        FStar_Tactics_V2_Basic.proofstate_of_goals
            FStar_Compiler_Range.dummyRange
            (FStar_Extraction_ML_UEnv.tcenv_of_uenv uenv)
            [] []
      in
      let result = Pulse_Extract_Main.extract_pulse
                            uenv
                            sigelt
                            (Pulse_RuntimeUtils.unembed_st_term_for_extraction 
                              (Obj.magic tm))
                            ps in
      match result with
      | FStar_Tactics_Result.Success (a, ps) -> a
      | FStar_Tactics_Result.Failed (exn, _) -> raise exn
            

let _ = 
   FStar_Extraction_ML_Modul.register_extension_extractor "pulse" extractor
