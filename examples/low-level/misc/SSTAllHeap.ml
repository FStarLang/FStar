
let halloc = (fun ( init ) -> ref init)

let salloc = (fun ( init ) ->  ref init)

let memread = (fun ( r ) -> !r )

let memwrite = (fun ( r ) ( v ) -> r := v )

let pushStackFrame = (fun ( _ ) -> ()) (*in some performance tests, this number had little effect on running time.*)

let popStackFrame = (fun ( _ ) -> ())

let get = (fun ( _ ) -> ())


let lalloc = (fun ( v ) -> (Support.All.failwith "unexpected. extraction should have redirected calls to this function"))

let llift = (fun ( f ) ( l ) -> (f l))
