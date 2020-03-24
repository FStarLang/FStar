module Bug1903

%Fail [178] (* bad ascription *)
let None : option unit = Some ()

%Fail [19] (* incomplete match *)
let None = Some ()

%Fail [72] (* X unbound *)
let X = 42

%Fail [114] (* type doesn't match *)
let None = 42

%Fail [19] (* incomplete match *)
let 0 = 1

let 0 = 0 (* OK *)
