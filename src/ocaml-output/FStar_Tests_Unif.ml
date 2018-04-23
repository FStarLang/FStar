
open Prims
open FStar_Pervasives

let tcenv : unit  ->  FStar_TypeChecker_Env.env = (fun uu____5 -> (FStar_Tests_Pars.init ()))


let guard_to_string : FStar_TypeChecker_Common.guard_formula  ->  Prims.string = (fun g -> (match (g) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____12 = (tcenv ())
in (FStar_TypeChecker_Normalize.term_to_string uu____12 f))
end))


let guard_eq : Prims.int  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  unit = (fun i g g' -> (

let uu____28 = (match (((g), (g'))) with
| (FStar_TypeChecker_Common.Trivial, FStar_TypeChecker_Common.Trivial) -> begin
((true), (g), (g'))
end
| (FStar_TypeChecker_Common.NonTrivial (f), FStar_TypeChecker_Common.NonTrivial (f')) -> begin
(

let f1 = (

let uu____44 = (tcenv ())
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) uu____44 f))
in (

let f'1 = (

let uu____46 = (tcenv ())
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) uu____46 f'))
in (

let uu____47 = (FStar_Tests_Util.term_eq f1 f'1)
in ((uu____47), (FStar_TypeChecker_Common.NonTrivial (f1)), (FStar_TypeChecker_Common.NonTrivial (f'1))))))
end
| uu____48 -> begin
((false), (g), (g'))
end)
in (match (uu____28) with
| (b, g1, g'1) -> begin
(match ((not (b))) with
| true -> begin
(

let msg = (

let uu____57 = (FStar_Util.string_of_int i)
in (

let uu____58 = (guard_to_string g'1)
in (

let uu____59 = (guard_to_string g1)
in (FStar_Util.format3 "Test %s failed:\n\tExpected guard %s;\n\tGot guard      %s\n" uu____57 uu____58 uu____59))))
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedGuard), (msg)) FStar_Range.dummyRange))
end
| uu____60 -> begin
()
end)
end)))


let unify : Prims.int  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.guard_formula  ->  (unit  ->  unit)  ->  unit = (fun i x1 y1 g' check1 -> ((

let uu____92 = (FStar_Util.string_of_int i)
in (FStar_Util.print1 "%s ..." uu____92));
(

let uu____94 = (FStar_Main.process_args ())
in (FStar_All.pipe_right uu____94 (fun a245 -> ())));
(

let uu____108 = (FStar_Syntax_Print.term_to_string x1)
in (

let uu____109 = (FStar_Syntax_Print.term_to_string y1)
in (FStar_Util.print2 "Unify %s\nand %s\n" uu____108 uu____109)));
(

let g = (

let uu____111 = (

let uu____112 = (tcenv ())
in (FStar_TypeChecker_Rel.teq uu____112 x1 y1))
in (

let uu____113 = (

let uu____118 = (tcenv ())
in (FStar_TypeChecker_Rel.solve_deferred_constraints uu____118))
in (FStar_All.pipe_right uu____111 uu____113)))
in ((guard_eq i g.FStar_TypeChecker_Env.guard_f g');
(check1 ());
(FStar_Options.init ());
));
))


let should_fail : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  unit = (fun x1 y1 -> (FStar_All.try_with (fun uu___80_134 -> (match (()) with
| () -> begin
(

let g = (

let uu____136 = (

let uu____137 = (tcenv ())
in (FStar_TypeChecker_Rel.teq uu____137 x1 y1))
in (

let uu____138 = (

let uu____143 = (tcenv ())
in (FStar_TypeChecker_Rel.solve_deferred_constraints uu____143))
in (FStar_All.pipe_right uu____136 uu____138)))
in (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
(

let uu____144 = (

let uu____145 = (FStar_Syntax_Print.term_to_string x1)
in (

let uu____146 = (FStar_Syntax_Print.term_to_string y1)
in (FStar_Util.format2 "%s and %s should not be unifiable\n" uu____145 uu____146)))
in (failwith uu____144))
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(

let uu____148 = (FStar_Syntax_Print.term_to_string x1)
in (

let uu____149 = (FStar_Syntax_Print.term_to_string y1)
in (

let uu____150 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print3 "%s and %s are unifiable if %s\n" uu____148 uu____149 uu____150))))
end))
end)) (fun uu___79_155 -> (match (uu___79_155) with
| FStar_Errors.Error (e, msg, r) -> begin
(FStar_Util.print1 "%s\n" msg)
end))))


let unify' : Prims.string  ->  Prims.string  ->  unit = (fun x1 y1 -> (

let x2 = (FStar_Tests_Pars.pars x1)
in (

let y2 = (FStar_Tests_Pars.pars y1)
in (

let g = (

let uu____172 = (

let uu____173 = (tcenv ())
in (FStar_TypeChecker_Rel.teq uu____173 x2 y2))
in (

let uu____174 = (

let uu____179 = (tcenv ())
in (FStar_TypeChecker_Rel.solve_deferred_constraints uu____179))
in (FStar_All.pipe_right uu____172 uu____174)))
in (

let uu____180 = (FStar_Syntax_Print.term_to_string x2)
in (

let uu____181 = (FStar_Syntax_Print.term_to_string y2)
in (

let uu____182 = (guard_to_string g.FStar_TypeChecker_Env.guard_f)
in (FStar_Util.print3 "%s and %s are unifiable with guard %s\n" uu____180 uu____181 uu____182))))))))


let norm : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____188 = (tcenv ())
in (FStar_TypeChecker_Normalize.normalize [] uu____188 t)))


let inst : Prims.int  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term Prims.list) = (fun n1 tm1 -> (

let rec aux = (fun out n2 -> (match ((Prims.op_Equality n2 (Prims.parse_int "0"))) with
| true -> begin
out
end
| uu____228 -> begin
(

let uu____229 = (

let uu____242 = (FStar_Tests_Pars.init ())
in (FStar_TypeChecker_Util.new_implicit_var "" FStar_Range.dummyRange uu____242 FStar_Syntax_Util.ktype0))
in (match (uu____229) with
| (t, uu____246, uu____247) -> begin
(

let uu____260 = (

let uu____273 = (FStar_Tests_Pars.init ())
in (FStar_TypeChecker_Util.new_implicit_var "" FStar_Range.dummyRange uu____273 t))
in (match (uu____260) with
| (u, uu____277, uu____278) -> begin
(aux ((u)::out) (n2 - (Prims.parse_int "1")))
end))
end))
end))
in (

let us = (aux [] n1)
in (

let uu____294 = (

let uu____295 = (FStar_Tests_Util.app tm1 us)
in (norm uu____295))
in ((uu____294), (us))))))


let run_all : unit  ->  unit = (fun uu____302 -> ((FStar_Util.print_string "Testing the unifier\n");
(FStar_Options.__set_unit_tests ());
(

let unify_check = (fun n1 x1 y1 g f -> (unify n1 x1 y1 g f))
in (

let unify1 = (fun n1 x1 y1 g -> (unify n1 x1 y1 g (fun uu____358 -> ())))
in (

let int_t = (FStar_Tests_Pars.tc "Prims.int")
in (

let x1 = (

let uu____361 = (FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None int_t)
in (FStar_All.pipe_right uu____361 FStar_Syntax_Syntax.bv_to_name))
in (

let y1 = (

let uu____363 = (FStar_Syntax_Syntax.gen_bv "y" FStar_Pervasives_Native.None int_t)
in (FStar_All.pipe_right uu____363 FStar_Syntax_Syntax.bv_to_name))
in ((unify1 (Prims.parse_int "0") x1 x1 FStar_TypeChecker_Common.Trivial);
(

let uu____366 = (

let uu____367 = (FStar_Syntax_Util.mk_eq2 FStar_Syntax_Syntax.U_zero FStar_Syntax_Util.t_bool x1 y1)
in FStar_TypeChecker_Common.NonTrivial (uu____367))
in (unify1 (Prims.parse_int "1") x1 y1 uu____366));
(

let id1 = (FStar_Tests_Pars.tc "fun x -> x")
in ((

let uu____370 = (FStar_Tests_Util.app id1 ((x1)::[]))
in (unify1 (Prims.parse_int "2") x1 uu____370 FStar_TypeChecker_Common.Trivial));
(

let id2 = (FStar_Tests_Pars.tc "fun x -> x")
in ((unify1 (Prims.parse_int "3") id2 id2 FStar_TypeChecker_Common.Trivial);
(

let id3 = (FStar_Tests_Pars.tc "fun x -> x")
in (

let id' = (FStar_Tests_Pars.tc "fun y -> y")
in ((unify1 (Prims.parse_int "4") id3 id' FStar_TypeChecker_Common.Trivial);
(

let uu____377 = (FStar_Tests_Pars.tc "fun x y -> x")
in (

let uu____378 = (FStar_Tests_Pars.tc "fun a b -> a")
in (unify1 (Prims.parse_int "5") uu____377 uu____378 FStar_TypeChecker_Common.Trivial)));
(

let uu____380 = (FStar_Tests_Pars.tc "fun x y z -> y")
in (

let uu____381 = (FStar_Tests_Pars.tc "fun a b c -> b")
in (unify1 (Prims.parse_int "6") uu____380 uu____381 FStar_TypeChecker_Common.Trivial)));
(

let uu____383 = (FStar_Tests_Pars.tc "fun (x:int) (y:int) -> y")
in (

let uu____384 = (FStar_Tests_Pars.tc "fun (x:int) (y:int) -> x")
in (

let uu____385 = (

let uu____386 = (FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). y==x))")
in FStar_TypeChecker_Common.NonTrivial (uu____386))
in (unify1 (Prims.parse_int "7") uu____383 uu____384 uu____385))));
(

let uu____388 = (FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> y")
in (

let uu____389 = (FStar_Tests_Pars.tc "fun (x:int) (y:int) (z:int) -> z")
in (

let uu____390 = (

let uu____391 = (FStar_Tests_Pars.tc "(forall (x:int). (forall (y:int). (forall (z:int). y==z)))")
in FStar_TypeChecker_Common.NonTrivial (uu____391))
in (unify1 (Prims.parse_int "8") uu____388 uu____389 uu____390))));
(

let uu____393 = (FStar_Main.process_args ())
in (FStar_All.pipe_right uu____393 (fun a246 -> ())));
(

let uu____406 = (

let uu____413 = (FStar_Tests_Pars.tc "fun u x -> u x")
in (inst (Prims.parse_int "1") uu____413))
in (match (uu____406) with
| (tm1, us) -> begin
(

let sol = (FStar_Tests_Pars.tc "fun x -> c_and x x")
in ((unify_check (Prims.parse_int "9") tm1 sol FStar_TypeChecker_Common.Trivial (fun uu____426 -> (

let uu____427 = (

let uu____428 = (

let uu____431 = (FStar_List.hd us)
in (norm uu____431))
in (

let uu____432 = (norm sol)
in (FStar_Tests_Util.term_eq uu____428 uu____432)))
in (FStar_Tests_Util.always (Prims.parse_int "9") uu____427))));
(

let uu____433 = (

let uu____440 = (FStar_Tests_Pars.tc "fun u x -> u x")
in (inst (Prims.parse_int "1") uu____440))
in (match (uu____433) with
| (tm2, us1) -> begin
(

let sol1 = (FStar_Tests_Pars.tc "fun x y -> x + y")
in ((unify_check (Prims.parse_int "10") tm2 sol1 FStar_TypeChecker_Common.Trivial (fun uu____453 -> (

let uu____454 = (

let uu____455 = (

let uu____458 = (FStar_List.hd us1)
in (norm uu____458))
in (

let uu____459 = (norm sol1)
in (FStar_Tests_Util.term_eq uu____455 uu____459)))
in (FStar_Tests_Util.always (Prims.parse_int "10") uu____454))));
(

let tm11 = (FStar_Tests_Pars.tc "x:int -> y:int{eq2 y x} -> bool")
in (

let tm21 = (FStar_Tests_Pars.tc "x:int -> y:int -> bool")
in ((

let uu____463 = (

let uu____464 = (FStar_Tests_Pars.tc "forall (x:int). (forall (y:int). y==x)")
in FStar_TypeChecker_Common.NonTrivial (uu____464))
in (unify1 (Prims.parse_int "11") tm11 tm21 uu____463));
(

let tm12 = (FStar_Tests_Pars.tc "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0")
in (

let tm22 = (FStar_Tests_Pars.tc "a:Type0 -> b:(a -> Type0) -> x:a -> y:b x -> Tot Type0")
in ((unify1 (Prims.parse_int "12") tm12 tm22 FStar_TypeChecker_Common.Trivial);
(

let uu____468 = (

let int_typ = (FStar_Tests_Pars.tc "int")
in (

let x2 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None int_typ)
in (

let typ = (FStar_Tests_Pars.tc "unit -> Type0")
in (

let l = (FStar_Tests_Pars.tc "fun (q:(unit -> Type0)) -> q ()")
in (

let q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ)
in (

let tm13 = (

let uu____481 = (

let uu____482 = (

let uu____485 = (FStar_Syntax_Syntax.bv_to_name q)
in (uu____485)::[])
in (FStar_Tests_Util.app l uu____482))
in (norm uu____481))
in (

let l1 = (FStar_Tests_Pars.tc "fun (p:unit -> Type0) -> p")
in (

let unit = (FStar_Tests_Pars.tc "()")
in (

let env = (

let uu____489 = (FStar_Tests_Pars.init ())
in (

let uu____490 = (

let uu____491 = (FStar_Syntax_Syntax.mk_binder x2)
in (

let uu____496 = (

let uu____503 = (FStar_Syntax_Syntax.mk_binder q)
in (uu____503)::[])
in (uu____491)::uu____496))
in (FStar_TypeChecker_Env.push_binders uu____489 uu____490)))
in (

let uu____520 = (FStar_TypeChecker_Util.new_implicit_var "" FStar_Range.dummyRange env typ)
in (match (uu____520) with
| (u_p, uu____540, uu____541) -> begin
(

let tm23 = (

let uu____557 = (

let uu____560 = (FStar_Tests_Util.app l1 ((u_p)::[]))
in (norm uu____560))
in (FStar_Tests_Util.app uu____557 ((unit)::[])))
in ((tm13), (tm23)))
end)))))))))))
in (match (uu____468) with
| (tm13, tm23) -> begin
((

let uu____570 = (

let uu____571 = (FStar_Tests_Pars.tc "Prims.l_True")
in FStar_TypeChecker_Common.NonTrivial (uu____571))
in (unify1 (Prims.parse_int "13") tm13 tm23 uu____570));
(

let uu____572 = (

let int_typ = (FStar_Tests_Pars.tc "int")
in (

let x2 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None int_typ)
in (

let typ = (FStar_Tests_Pars.tc "pure_post unit")
in (

let l = (FStar_Tests_Pars.tc "fun (q:pure_post unit) -> q ()")
in (

let q = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None typ)
in (

let tm14 = (

let uu____585 = (

let uu____586 = (

let uu____589 = (FStar_Syntax_Syntax.bv_to_name q)
in (uu____589)::[])
in (FStar_Tests_Util.app l uu____586))
in (norm uu____585))
in (

let l1 = (FStar_Tests_Pars.tc "fun (p:pure_post unit) -> p")
in (

let unit = (FStar_Tests_Pars.tc "()")
in (

let env = (

let uu____593 = (FStar_Tests_Pars.init ())
in (

let uu____594 = (

let uu____595 = (FStar_Syntax_Syntax.mk_binder x2)
in (

let uu____600 = (

let uu____607 = (FStar_Syntax_Syntax.mk_binder q)
in (uu____607)::[])
in (uu____595)::uu____600))
in (FStar_TypeChecker_Env.push_binders uu____593 uu____594)))
in (

let uu____624 = (FStar_TypeChecker_Util.new_implicit_var "" FStar_Range.dummyRange env typ)
in (match (uu____624) with
| (u_p, uu____644, uu____645) -> begin
(

let tm24 = (

let uu____661 = (

let uu____664 = (FStar_Tests_Util.app l1 ((u_p)::[]))
in (norm uu____664))
in (FStar_Tests_Util.app uu____661 ((unit)::[])))
in ((tm14), (tm24)))
end)))))))))))
in (match (uu____572) with
| (tm14, tm24) -> begin
((

let uu____674 = (

let uu____675 = (FStar_Tests_Pars.tc "Prims.l_True")
in FStar_TypeChecker_Common.NonTrivial (uu____675))
in (unify1 (Prims.parse_int "14") tm14 tm24 uu____674));
(FStar_Options.__clear_unit_tests ());
(FStar_Util.print_string "Unifier ok\n");
)
end));
)
end));
)));
)));
))
end));
))
end));
)));
));
));
))))));
))




