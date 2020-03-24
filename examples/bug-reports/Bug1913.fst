module Bug1913

%Fail
let _ = assert (False /\ True)

%Fail
let _ = assert ((/\) False True)

let _ = assert (False \/ True)

let _ = assert ((\/) False True)
