module Bug179

assume val verify: #p:(int -> Type) -> d:int -> Tot (b:bool{b ==> p d})

opaque type pred (d:int)

val checkmail: list int -> unit
let checkmail xs = 
  (match xs with
   | [ ctxt ] ->
       if verify #pred ctxt then
          (assert(verify #pred ctxt);
           assert(pred ctxt))
       else failwith "stuff"
   | _ -> ())
