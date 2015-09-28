module Bug

val foo : unit -> St (unit)
let foo _ = ()
 
val bar : unit -> option (u:unit & (unit -> St (unit)))
let bar _ = Some (| (), (fun () -> foo ()) |)
