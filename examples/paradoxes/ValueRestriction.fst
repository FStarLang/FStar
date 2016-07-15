module ValueRestriction

// polymorphic reference
val r : #a:Type -> ref (option a)
let r (#a:Type) = alloc #(option a) None

let write () = (r #string) := Some "foo"

let v : option int = !(r #int) // -- but v = Some "foo", so wrong type!
