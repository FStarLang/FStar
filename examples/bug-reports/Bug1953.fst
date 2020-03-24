module Bug1953

%Fail [185]
type t1 =
    | A1 : int -> Dv t1
    
type t2 =
    | A2 : int -> Tot t2

%Fail [185]
type t3 =
    | A3 : int -> GTot t3

effect X (a:Type) = Tot a

type t4 =
    | A4 : int -> X t4

type t5 =
    | A5 : int -> X t5
