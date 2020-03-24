module Bug829

type r = { x : int }

%Fail [114]
let true = 2

%Fail [114]
let { x = true } = { x = 2 }

%Fail [19]
let (x, true) = (2, false)

let (x, true)  = (2, true)

%Fail [19]
let (false, false, xx) = (true, true, 9)

%Fail [114]
let (true, true) = (2, false)
