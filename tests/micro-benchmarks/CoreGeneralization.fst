module CoreGeneralization

let test (x:int) (#a:Type) (y:a) = y

#push-options "--debug TwoPhases,Gen"
let gen x = test x

