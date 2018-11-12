module ValueRestriction

                                         // r generative
val r : #a:Type -> ref (option a)
let r (#a:Type) = alloc #(option a) None

let write () = (r #string) := Some "foo" // -- so the r here generates different

let v : option int = !(r #int)           // -- reference from the r here
