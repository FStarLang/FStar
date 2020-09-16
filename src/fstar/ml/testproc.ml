let x =
   let args = Array.to_list Sys.argv in
   let should_kill =
      match args with
      | [_; "-kill"] -> true
      | _ -> false
   in
   for i = 1 to 100 do
     FStar_Main.test_z3_process_ctrl should_kill
   done
