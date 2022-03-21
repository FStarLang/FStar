module Bug1060

val id : _:(#a: Type -> f:(list a -> Tot (list a)){True}){True}
let id #a = (fun l -> l)

val id2 : #a: Type -> f:(list a -> Tot (list a)){True}
let rec id2 #a = (fun l -> l)
