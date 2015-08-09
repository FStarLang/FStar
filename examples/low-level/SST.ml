
let halloc = (fun ( init ) -> ref init)

let salloc = (fun ( init ) ->  Camlstack.mkref init)

let memread = (fun ( r ) -> !r )

let memwrite = (fun ( r ) ( v ) -> r := v )

let pushStackFrame = (fun ( _ ) -> Camlstack.push_frame 100)

let popStackFrame = (fun ( _ ) -> Camlstack.pop_frame)

let get = (fun ( _ ) -> ())




