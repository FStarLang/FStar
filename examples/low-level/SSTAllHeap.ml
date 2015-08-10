
let halloc = (fun ( init ) -> ref init)

let salloc = (fun ( init ) ->  ref init)

let memread = (fun ( r ) -> !r )

let memwrite = (fun ( r ) ( v ) -> r := v )

let pushStackFrame = (fun ( _ ) -> ())

let popStackFrame = (fun ( _ ) -> ())

let get = (fun ( _ ) -> ())




