module Bug3227

type box (a:Type) = { x : a; }
let proj (b : box (box (box int))) : int = b.x.x.x

type box2 (a:Type) = | Box2 : x:a -> box2 a

let test (b : box2 (box2 int)) = Box2? b && Box2? (Box2?.x b)

noeq
type boxf (a:Type) = { ff : a -> a }

let test2 (r : boxf int) = r.ff 5

noeq
type boxfi (a:Type) = { ff : (#_:a -> a) }

let test3 (r : boxfi int) = r.ff #5

let test4 (#a:Type) (r : boxf a) (x:a) : a = r.ff x
