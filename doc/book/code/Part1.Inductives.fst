module Part1.Inductives

//SNIPPET_START: three
type three =
  | One_of_three : three
  | Two_of_three : three
  | Three_of_three : three
//SNIPPET_END: three

//SNIPPET_START: assert
let distinct = assert (One_of_three <> Two_of_three /\
                       Two_of_three <> Three_of_three /\
                       Three_of_three <> One_of_three)

let exhaustive (x:three) = assert (x = One_of_three \/
                                   x = Two_of_three \/
                                   x = Three_of_three)
//SNIPPET_END: assert

//SNIPPET_START: disc_handrolled
let is_one (x:three)
  : bool
  = match x with
    | One_of_three -> true
    | _ -> false

let is_two (x:three)
  : bool
  = match x with
    | Two_of_three -> true
    | _ -> false

let is_three (x:three)
  : bool
  = match x with
    | Three_of_three -> true
    | _ -> false
//SNIPPET_END: disc_handrolled

//SNIPPET_START: three_as_int
let three_as_int (x:three)
  : int
  = if is_one x then 1
    else if is_two x then 2
    else 3
//SNIPPET_END: three_as_int

//SNIPPET_START: three_as_int'
let three_as_int' (x:three)
  : int
  = if One_of_three? x then 1
    else if Two_of_three? x then 2
    else 3
//SNIPPET_END: three_as_int'


//SNIPPET_START: three_as_int''
let three_as_int'' (x:three)
  : int
  = match x with
    | One_of_three -> 1
    | Two_of_three -> 2
    | Three_of_three -> 3
//SNIPPET_END: three_as_int''

//SNIPPET_START: only_two_as_int
let only_two_as_int (x:three { not (Three_of_three? x) })
  : int
  = match x with
    | One_of_three -> 1
    | Two_of_three -> 2
//SNIPPET_END: only_two_as_int

//SNIPPET_START: tup
type tup2 (a:Type)  (b:Type) =
  | Tup2 : fst:a -> snd:b -> tup2 a b

type tup3 a b c =
  | Tup3 : fst:a -> snd:b -> thd:c -> tup3 a b c
//SNIPPET_END: tup


//SNIPPET_START: proj_handrolled
let tup2_fst #a #b (x:tup2 a b)
  : a
  = match x with
    | Tup2 fst _ -> fst

let tup2_snd #a #b (x:tup2 a b)
  : b
  = match x with
    | Tup2 _ snd -> snd

let tup3_fst #a #b #c (x:tup3 a b c)
  : a
  = match x with
    | Tup3 fst _ _ -> fst

let tup3_snd #a #b #c (x:tup3 a b c)
  : b
  = match x with
    | Tup3 _ snd _ -> snd

let tup3_third #a #b #c (x:tup3 a b c)
  : c
  = match x with
    | Tup3 _ _ thd -> thd
//SNIPPET_END: proj_handrolled

open FStar.Mul
//SNIPPET_START: point
type point3D = { x:int; y:int; z:int}

let origin = { y=0; x=0; z=0 }

let dot (p0 p1:point3D) = p0.x * p1.x + p0.y * p1.y + p0.z * p1.z

let translate_X (p:point3D) (shift:int) = { p with x = p.x + shift}

let is_origin (x:point3D) =
  match x with
  | {z=0;y=0;x=0} -> true
  | _ -> false
//SNIPPET_END: point

//SNIPPET_START: option
let try_divide (x y:int)
  : option int
  = if y = 0 then None else Some (x / y)

let divide (x:int) (y:int{y<>0}) = x / y
//SNIPPET_END: option


//SNIPPET_START: either
let same_case #a #b #c #d (x:either a b) (y:either c d)
  : bool
  = match x, y with
    | Inl _, Inl _
    | Inr _, Inr _ -> true
    | _ -> false

let sum (x:either bool int) (y:either bool int{same_case x y})
  : z:either bool int{ Inl? z <==> Inl? x}
  = match x, y with
    | Inl xl, Inl yl -> Inl (xl || yl)
    | Inr xr, Inr yr -> Inr (xr + yr)
//SNIPPET_END: either

//SNIPPET_START: length
let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl
//SNIPPET_END: length

//SNIPPET_START: sig append
val append (#a:Type) (l1 l2:list a)
  : l:list a { length l = length l1 + length l2 }
//SNIPPET_END: sig append

//SNIPPET_START: def append
let rec append l1 l2
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2
//SNIPPET_END: def append
