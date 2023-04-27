module AdmitTermination

// blah not used recursively, silence
#set-options "--warn_error -328"

[@@admit_termination]
let rec blah () = ()
and f (x:int) : int = f x

[@@admit_termination]
let rec g (x:int) : int = g x

val h : int -> int
[@@admit_termination]
let rec h (x:int) : int = h x

[@@admit_termination]
val i : int -> int

let rec i (x:int) : int = i x
