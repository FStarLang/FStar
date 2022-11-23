module CoreGeneralization

let test (x:int) (#a:Type) (y:a) = y

#push-options "--debug CoreGeneralization --debug_level TwoPhases,Gen"
let gen x = test x

