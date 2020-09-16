let x =
   let args = Array.to_list Sys.argv in
   let should_kill =
      match args with
      | [_; "-kill"] -> true
      | _ -> false
   in
   FStar_Main.test_z3_process_ctrl should_kill
