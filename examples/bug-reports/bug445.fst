module Bug445

assume new type t : int -> Type
let rec f (x:int) : t x =  //the x in the annotation is out of scope (mistakenly)
  admit()
