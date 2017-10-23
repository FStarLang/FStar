module Bug179

open FStar.All

assume val verify: #p:(int -> Type) -> d:int -> Tot (b:bool{b ==> p d})

type pred (d:int)

val checkmail: list int -> ML unit
let checkmail xs =
  (match xs with
   | [ ctxt ] ->
       if verify #pred ctxt then
          (assert(verify #pred ctxt);
           assert(pred ctxt))
       else failwith "stuff"
   | _ -> ())
