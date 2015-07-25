






type 'b b2t =
(bool, bool, unit, unit) l__Eq2

type l__True =
| T

let is_T = (fun ( _discr_ ) -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))



type ('p, 'q) l_imp =
'p  ->  'q

type ('p, 'q) l_and =
| And

let is_And = (fun ( _discr_ ) -> (match (_discr_) with
| And (_) -> begin
true
end
| _ -> begin
false
end))





type ('p, 'q) l_or =
| Left
| Right

let is_Left = (fun ( _discr_ ) -> (match (_discr_) with
| Left (_) -> begin
true
end
| _ -> begin
false
end))

let is_Right = (fun ( _discr_ ) -> (match (_discr_) with
| Right (_) -> begin
true
end
| _ -> begin
false
end))









type ('p, 'q) l_iff =
('p, (('q, 'q) l_and, 'p) l_imp) l_imp

type 'p l_not =
('p, l__False) l_imp

type ('a, 'p) l__Forall =
'a  ->  'p

type ('dummyV2, 'dummyV1) l__DTuple2 =
| MkDTuple2 of unit * unit * Obj.t * Obj.t

let is_MkDTuple2 = (fun ( _discr_ ) -> (match (_discr_) with
| MkDTuple2 (_) -> begin
true
end
| _ -> begin
false
end))





type ('a, 'p) l__Exists =
('a, 'p) l__DTuple2

type ('p, 'q) l__XOR =
(('p, 'q) l_or, ('p, 'q) l_and l_not) l_and

type ('p, 'q, 'r) l__ITE =
(('p, 'q) l_imp, ('p l_not, 'r) l_imp) l_and







type ('a, 'x, 'p) pure_return =
'p

type ('a, 'b, 'wlp1, 'wlp2, 'p) pure_bind_wlp =
'wlp1

type ('a, 'b, 'wp1, 'wlp1, 'wp2, 'wlp2) pure_bind_wp =
('a, 'b, 'wp1, 'wp2, Obj.t) pure_bind_wlp

type ('a, 'p, 'wp_then, 'wp_else, 'post) pure_if_then_else =
('p, 'wp_then, 'wp_else) l__ITE

type ('a, 'wlp_cases, 'post) pure_ite_wlp =
('a, ('wlp_cases, 'post) l_or) l__Forall

type ('a, 'wlp_cases, 'wp_cases, 'post) pure_ite_wp =
(('a, 'wlp_cases, 'post) pure_ite_wlp, 'wp_cases) l_and

type ('a, 'wp1, 'op, 'wp2, 'p) pure_wp_binop =
'op

type ('a, 'wp) pure_wp_as_type =
'wp l__ForallTyp

type ('a, 'b, 'wp, 'p) pure_close_wp =
('b, 'wp) l__Forall

type ('a, 'wp, 'p) pure_close_wp_t =
'wp l__ForallTyp

type ('a, 'q, 'wp, 'p) pure_assert_p =
('q, 'wp) l_and

type ('a, 'q, 'wp, 'p) pure_assume_p =
('q, 'wp) l_imp

type ('a, 'p) pure_null_wp =
('a, 'p) l__Forall

type ('a, 'wp) pure_trivial =
'wp





let op_AmpAmp = (failwith ("Not yet implemented"))

let op_BarBar = (failwith ("Not yet implemented"))

let op_Negation = (failwith ("Not yet implemented"))

let op_Multiply = (failwith ("Not yet implemented"))

let op_Subtraction = (failwith ("Not yet implemented"))

let op_Addition = (failwith ("Not yet implemented"))

let op_Minus = (failwith ("Not yet implemented"))

let op_LessThanOrEqual = (failwith ("Not yet implemented"))

let op_GreaterThan = (failwith ("Not yet implemented"))

let op_GreaterThanOrEqual = (failwith ("Not yet implemented"))

let op_LessThan = (failwith ("Not yet implemented"))

let op_Equality = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let op_disEquality = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

type int16 =
int

type int32 =
int





















type ('dummyV2, 'dummyV1) l__LBL =





type byte =
uint8

type double =
float

type 'a list =
| Nil
| Cons of 'a * 'a list

let is_Nil = (fun ( _discr_ ) -> (match (_discr_) with
| [] (_) -> begin
true
end
| _ -> begin
false
end))

let is_Cons = (fun ( _discr_ ) -> (match (_discr_) with
| :: (_) -> begin
true
end
| _ -> begin
false
end))





type pattern =
| SMTPat of unit * Obj.t
| SMTPatT of unit

let is_SMTPat = (fun ( _discr_ ) -> (match (_discr_) with
| SMTPat (_) -> begin
true
end
| _ -> begin
false
end))

let is_SMTPatT = (fun ( _discr_ ) -> (match (_discr_) with
| SMTPatT (_) -> begin
true
end
| _ -> begin
false
end))





type ('dummyV2, 'dummyV1) decreases =

type 'a option =
| None
| Some of 'a

let is_None = (fun ( _discr_ ) -> (match (_discr_) with
| None (_) -> begin
true
end
| _ -> begin
false
end))

let is_Some = (fun ( _discr_ ) -> (match (_discr_) with
| Some (_) -> begin
true
end
| _ -> begin
false
end))





type ('a, 'b) either =
| Inl of 'a
| Inr of 'b

let is_Inl = (fun ( _discr_ ) -> (match (_discr_) with
| Inl (_) -> begin
true
end
| _ -> begin
false
end))

let is_Inr = (fun ( _discr_ ) -> (match (_discr_) with
| Inr (_) -> begin
true
end
| _ -> begin
false
end))









type 'a result =
| V of 'a
| E of exn
| Err of string

let is_V = (fun ( _discr_ ) -> (match (_discr_) with
| V (_) -> begin
true
end
| _ -> begin
false
end))

let is_E = (fun ( _discr_ ) -> (match (_discr_) with
| E (_) -> begin
true
end
| _ -> begin
false
end))

let is_Err = (fun ( _discr_ ) -> (match (_discr_) with
| Err (_) -> begin
true
end
| _ -> begin
false
end))







type ('heap, 'a, 'x, 'p) st_return =
'p

type ('heap, 'a, 'b, 'wp1, 'wlp1, 'wp2, 'wlp2, 'p, 'h0) st_bind_wp =
'wp1

type ('heap, 'a, 'b, 'wlp1, 'wlp2, 'p, 'h0) st_bind_wlp =
'wlp1

type ('heap, 'a, 'p, 'wp_then, 'wp_else, 'post, 'h0) st_if_then_else =
('p, 'wp_then, 'wp_else) l__ITE

type ('heap, 'a, 'wlp_cases, 'post, 'h0) st_ite_wlp =
('a, ('heap, ('wlp_cases, 'post) l_or) l__Forall) l__Forall

type ('heap, 'a, 'wlp_cases, 'wp_cases, 'post, 'h0) st_ite_wp =
(('heap, 'a, 'wlp_cases, 'post, unit) st_ite_wlp, 'wp_cases) l_and

type ('heap, 'a, 'wp1, 'op, 'wp2, 'p, 'h) st_wp_binop =
'op

type ('heap, 'a, 'wp) st_wp_as_type =
('heap, 'wp) l__Forall l__ForallTyp

type ('heap, 'a, 'b, 'wp, 'p, 'h) st_close_wp =
('b, 'wp) l__Forall

type ('heap, 'a, 'wp, 'p, 'h) st_close_wp_t =
'wp l__ForallTyp

type ('heap, 'a, 'p, 'wp, 'q, 'h) st_assert_p =
('p, 'wp) l_and

type ('heap, 'a, 'p, 'wp, 'q, 'h) st_assume_p =
('p, 'wp) l_imp

type ('heap, 'a, 'p, 'h) st_null_wp =
('a, ('heap, 'p) l__Forall) l__Forall

type ('heap, 'a, 'wp) st_trivial =
('heap, 'wp) l__Forall



type ('a, 'x, 'p) ex_return =
'p

type ('a, 'b, 'wlp1, 'wlp2, 'p) ex_bind_wlp =
('b result, ('p, 'wlp1) l_or) l__Forall

type ('a, 'b, 'wp1, 'wlp1, 'wp2, 'wlp2, 'p) ex_bind_wp =
(('a, 'b, 'wlp1, 'wlp2, 'p) ex_bind_wlp, 'wp1) l_and

type ('a, 'p, 'wp_then, 'wp_else, 'post) ex_if_then_else =
('p, 'wp_then, 'wp_else) l__ITE

type ('a, 'wlp_cases, 'post) ex_ite_wlp =
('a result, ('wlp_cases, 'post) l_or) l__Forall

type ('a, 'wlp_cases, 'wp_cases, 'post) ex_ite_wp =
(('a, 'wlp_cases, 'post) ex_ite_wlp, 'wp_cases) l_and

type ('a, 'wp1, 'op, 'wp2, 'p) ex_wp_binop =
'op

type ('a, 'wp) ex_wp_as_type =
'wp l__ForallTyp

type ('a, 'b, 'wp, 'p) ex_close_wp =
('b, 'wp) l__Forall

type ('a, 'wp, 'p) ex_close_wp_t =
'wp l__ForallTyp

type ('a, 'q, 'wp, 'p) ex_assert_p =
('q, 'wp) l_and

type ('a, 'q, 'wp, 'p) ex_assume_p =
('q, 'wp) l_imp

type ('a, 'p) ex_null_wp =
('a result, 'p) l__Forall

type ('a, 'wp) ex_trivial =
'wp

type ('heap, 'a, 'x, 'p) all_return =
'p

type ('heap, 'a, 'b, 'wp1, 'wlp1, 'wp2, 'wlp2, 'p, 'h0) all_bind_wp =
'wp1

type ('heap, 'a, 'b, 'wlp1, 'wlp2, 'p, 'h0) all_bind_wlp =
('b result, ('heap, ('wlp1, 'p) l_or) l__Forall) l__Forall

type ('heap, 'a, 'p, 'wp_then, 'wp_else, 'post, 'h0) all_if_then_else =
('p, 'wp_then, 'wp_else) l__ITE

type ('heap, 'a, 'wlp_cases, 'post, 'h0) all_ite_wlp =
('a result, ('heap, ('wlp_cases, 'post) l_or) l__Forall) l__Forall

type ('heap, 'a, 'wlp_cases, 'wp_cases, 'post, 'h0) all_ite_wp =
(('a result, ('heap, ('wlp_cases, 'post) l_or) l__Forall) l__Forall, 'wp_cases) l_and

type ('heap, 'a, 'wp1, 'op, 'wp2, 'p, 'h) all_wp_binop =
'op

type ('heap, 'a, 'wp) all_wp_as_type =
('heap, 'wp) l__Forall l__ForallTyp

type ('heap, 'a, 'b, 'wp, 'p, 'h) all_close_wp =
('b, 'wp) l__Forall

type ('heap, 'a, 'wp, 'p, 'h) all_close_wp_t =
'wp l__ForallTyp

type ('heap, 'a, 'p, 'wp, 'q, 'h) all_assert_p =
('p, 'wp) l_and

type ('heap, 'a, 'p, 'wp, 'q, 'h) all_assume_p =
('p, 'wp) l_imp

type ('heap, 'a, 'p, 'h0) all_null_wp =
('a result, ('heap, 'p) l__Forall) l__Forall

type ('heap, 'a, 'wp) all_trivial =
('heap, 'wp) l__Forall

type lex_t =
| LexTop
| LexCons of unit * Obj.t * lex_t

let is_LexTop = (fun ( _discr_ ) -> (match (_discr_) with
| LexTop (_) -> begin
true
end
| _ -> begin
false
end))

let is_LexCons = (fun ( _discr_ ) -> (match (_discr_) with
| LexCons (_) -> begin
true
end
| _ -> begin
false
end))

type ('a, 'b) l__Tuple2 =
| MkTuple2 of 'a * 'b

let is_MkTuple2 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple2 (_) -> begin
true
end
| _ -> begin
false
end))





type ('a, 'b, 'c) l__Tuple3 =
| MkTuple3 of 'a * 'b * 'c

let is_MkTuple3 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple3 (_) -> begin
true
end
| _ -> begin
false
end))







type ('a, 'b, 'c, 'd) l__Tuple4 =
| MkTuple4 of 'a * 'b * 'c * 'd

let is_MkTuple4 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple4 (_) -> begin
true
end
| _ -> begin
false
end))









type ('a, 'b, 'c, 'd, 'e) l__Tuple5 =
| MkTuple5 of 'a * 'b * 'c * 'd * 'e

let is_MkTuple5 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple5 (_) -> begin
true
end
| _ -> begin
false
end))











type ('a, 'b, 'c, 'd, 'e, 'f) l__Tuple6 =
| MkTuple6 of 'a * 'b * 'c * 'd * 'e * 'f

let is_MkTuple6 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple6 (_) -> begin
true
end
| _ -> begin
false
end))













type ('a, 'b, 'c, 'd, 'e, 'f, 'g) l__Tuple7 =
| MkTuple7 of 'a * 'b * 'c * 'd * 'e * 'f * 'g

let is_MkTuple7 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple7 (_) -> begin
true
end
| _ -> begin
false
end))















type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) l__Tuple8 =
| MkTuple8 of 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h

let is_MkTuple8 = (fun ( _discr_ ) -> (match (_discr_) with
| MkTuple8 (_) -> begin
true
end
| _ -> begin
false
end))

















type ('dummyV3, 'dummyV2, 'dummyV1) l__DTuple3 =
| MkDTuple3 of unit * unit * unit * Obj.t * Obj.t * Obj.t

let is_MkDTuple3 = (fun ( _discr_ ) -> (match (_discr_) with
| MkDTuple3 (_) -> begin
true
end
| _ -> begin
false
end))







type ('dummyV4, 'dummyV3, 'dummyV2, 'dummyV1) l__DTuple4 =
| MkDTuple4 of unit * unit * unit * unit * Obj.t * Obj.t * Obj.t * Obj.t

let is_MkDTuple4 = (fun ( _discr_ ) -> (match (_discr_) with
| MkDTuple4 (_) -> begin
true
end
| _ -> begin
false
end))









type ('a, 'wp) as_requires =
'wp

type ('a, 'wlp, 'x) as_ensures =
'wlp l_not

let fst = (fun ( _47_392  :  unit ) ( x  :  ('a, 'b) l__Tuple2 ) -> ((Prims_MkTuple2._1 ()) x))

let snd = (fun ( _47_392  :  unit ) ( x  :  ('a, 'b) l__Tuple2 ) -> ((Prims_MkTuple2._2 ()) x))

let dfst = (Obj.magic (fun ( _47_392  :  unit ) ( t  :  ('a, 'b) l__DTuple2 ) -> ((Prims_MkDTuple2._1 ()) t)))

let dsnd = (Obj.magic (fun ( _47_392  :  unit ) ( t  :  ('a, 'b) l__DTuple2 ) -> ((Prims_MkDTuple2._2 ()) t)))

type ('a, 'x, 'body) l__Let =
'body



let by_induction_on = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let _assume = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let admit = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let magic = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let admitP = (Obj.magic (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented"))))

let _assert = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let cut = (Obj.magic (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented"))))

let qintro = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let failwith = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let raise = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let pipe_right = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let pipe_left = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let ignore = (fun ( _47_392  :  unit ) ( x  :  'a ) -> ())

let erase = (fun ( _47_392  :  unit ) ( x  :  'a ) -> ())

let exit = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let try_with = (fun ( _47_392  :  unit ) -> (failwith ("Not yet implemented")))

let min = (failwith ("Not yet implemented"))

let max = (failwith ("Not yet implemented"))

type nat =
int

type pos =
int

type nonzero =
int

let op_Modulus = (failwith ("Not yet implemented"))

let op_Division = (failwith ("Not yet implemented"))

type 'dummyV1 l__Boxed =




