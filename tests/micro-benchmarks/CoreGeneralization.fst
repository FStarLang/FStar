module CoreGeneralization

let test (x:int) (#a:Type) (y:a) = y

#push-options "--debug Gen"
let gen x = test x
#pop-options
