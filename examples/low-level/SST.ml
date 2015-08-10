
let halloc = (fun ( init ) -> ref init)

let salloc = (fun ( init ) ->  Camlstack.mkref init)

let memread = (fun ( r ) -> !r )

let memwrite = (fun ( r ) ( v ) -> r := v )

let pushStackFrame = (fun ( _ ) -> Camlstack.push_frame 10000) (*in some performance tests, this number had little effect on running time.*)

let popStackFrame = (fun ( _ ) -> Camlstack.pop_frame ())

let get = (fun ( _ ) -> ())




