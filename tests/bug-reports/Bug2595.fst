module Bug2595

noeq
type sum_type  =
  | SumType1: string -> sum_type
  | SumType2: nat -> sum_type

let test_buggy (x:(b:bool & (if b then nat else string))): sum_type =
  match x with //no magic on x, since although its second component is an Obj.t, we're only using a variable to match it
  | (|false, x2|) -> SumType1 x2 //magic on x2
  | (|true, x4|) -> SumType2 x4 //magic on x4

noeq
type sum_type2  =
  | SumType2_1: string -> string -> sum_type2
  | SumType2_2: nat -> nat -> sum_type2

let test_buggy2 (x:(b:bool & (if b then (nat & nat) else (string & string)))): sum_type2 =
  match x with //magic on x since its second component is an Obj.t
  | (|false, (y, z)|) -> SumType2_1 y z //magics on both y and z
  | (|true, (y, z)|) -> SumType2_2 y z //magics on both y and z

let test_ok2 (x:(b:bool & (nat & y:int{ b ==> y > 17 }))): sum_type2 =
  match x with
  | (|true, (z, y)|) -> SumType2_2 z y //no magics here on refinement types
  | (|false, (z, y)|) -> SumType2_2 z z

noeq
type mixed (a:Type) =
  | Mixed: a -> int -> mixed a


noeq
type t3  =
  | T3_1: string -> int -> t3
  | T3_2: nat -> int -> t3

let test_mixed (x:(b:bool & (if b then mixed string else mixed nat))) 
  : t3
  = match x with //magic n x, since its second component is an Obj.t
    | (|true, Mixed s z |) -> T3_1 s z //only magic s 
    | (|false, Mixed n z |) -> T3_2 n z  // only magic n

//////////////////////////
//Lib.NTuple from HACL* 
/////////////////////////

let flen = pos

inline_for_extraction
let rec ntuple_ (a:Type0) (len:flen) =
  if len = 1 then a
  else a & ntuple_ a (len-1)

inline_for_extraction
let ntuple (a:Type0) (len:flen) = normalize_term (ntuple_ a len)

inline_for_extraction
let rest_ (#a:Type0) (#len:flen{len > 1}) (s:ntuple_ a len) : ntuple_ a (len - 1)=
    snd (s <: a & ntuple_ a (len - 1)) //magic  on s

let rest #a #len s =
  normalize_term (rest_ #a #len s) //magic on s after unfolding to a match
  
