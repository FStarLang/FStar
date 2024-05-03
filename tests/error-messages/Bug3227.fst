module Bug3227

type box (a:Type) = { x : a; }
let proj (b : box (box (box int))) : int = b.x.x.x

type box2 (a:Type) = | Box2 : x:a -> box2 a

let test (b : box2 (box2 int)) = Box2? b && Box2? (Box2?.x b)