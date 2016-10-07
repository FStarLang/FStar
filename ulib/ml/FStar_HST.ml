let push_frame () = ()
let pop_frame () = ()

let salloc contents =
  FStar_ST.alloc contents

let new_region = FStar_ST.new_region
let new_colored_region = FStar_ST.new_colored_region

let ralloc i contents = FStar_ST.ralloc i contents

let op_Colon_Equals = FStar_ST.write

let op_Bang = FStar_ST.read

let get () = FStar_ST.get ()

let recall = (fun r -> ())

let recall_region = (fun r -> ())
