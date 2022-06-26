#r "../../../bin/ulibfs.dll"
#r "bin/net6.0/Debug/Lens.dll"
open Lens

let circle = { center = { x = Prims.of_int 2; y = Prims.of_int 3; z = Prims.of_int 4; }; radius = Prims.of_int 2 }
let redCircle = { color = { red = Prims.of_int 1; green = Prims.of_int 0; blue = Prims.of_int 0 }; payload = circle }
let greenCircle = makeGreen redCircle

printf "%A" greenCircle
if (greenCircle.color.red <> Prims.of_int 0)
    then failwith "Red should be 0"
if (greenCircle.color.green <> Prims.of_int 1)
    then failwith "Green should be 1"
