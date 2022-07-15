module Bug2629

let test : prop = forall (a:Type u#a) (x:a). x == x \/ x =!= x
