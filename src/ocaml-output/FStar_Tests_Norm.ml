
open Prims
open FStar_Pervasives

let b : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.binder = FStar_Syntax_Syntax.mk_binder


let id : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun x -> x")


let apply : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun f x -> f x")


let twice : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun f x -> f (f x)")


let tt : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun x y -> x")


let ff : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun x y -> y")


let z : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun f x -> x")


let one : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun f x -> f x")


let two : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun f x -> f (f x)")


let succ : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun n f x -> f (n f x)")


let pred : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun n f x -> n (fun g h -> h (g f)) (fun y -> x) (fun y -> y)")


let mul : FStar_Syntax_Syntax.term = (FStar_Tests_Pars.pars "fun m n f -> m (n f)")


let rec encode : Prims.int  ->  FStar_Syntax_Syntax.term = (fun n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
z
end
| uu____10 -> begin
(

let uu____11 = (

let uu____14 = (encode (n1 - (Prims.parse_int "1")))
in (uu____14)::[])
in (FStar_Tests_Util.app succ uu____11))
end))


let minus : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun m1 n1 -> (FStar_Tests_Util.app n1 ((pred)::(m1)::[])))


let let_ : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun x1 e e' -> (

let uu____50 = (

let uu____53 = (

let uu____54 = (b x1)
in (uu____54)::[])
in (FStar_Syntax_Util.abs uu____53 e' FStar_Pervasives_Native.None))
in (FStar_Tests_Util.app uu____50 ((e)::[]))))


let mk_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun x1 e e' -> (

let e'1 = (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NM (((x1), ((Prims.parse_int "0")))))::[]) e')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x1); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})::[]))), (e'1)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let lid : Prims.string  ->  FStar_Ident.lident = (fun x1 -> (FStar_Ident.lid_of_path ((x1)::[]) FStar_Range.dummyRange))


let znat_l : FStar_Syntax_Syntax.fv = (

let uu____104 = (lid "Z")
in (FStar_Syntax_Syntax.lid_as_fv uu____104 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))


let snat_l : FStar_Syntax_Syntax.fv = (

let uu____105 = (lid "S")
in (FStar_Syntax_Syntax.lid_as_fv uu____105 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))


let tm_fv : FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun fv -> (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_fvar (fv)) FStar_Pervasives_Native.None FStar_Range.dummyRange))


let znat : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (tm_fv znat_l)


let snat : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s -> (

let uu____122 = (

let uu____129 = (

let uu____130 = (

let uu____145 = (tm_fv snat_l)
in (

let uu____148 = (

let uu____157 = (FStar_Syntax_Syntax.as_arg s)
in (uu____157)::[])
in ((uu____145), (uu____148))))
in FStar_Syntax_Syntax.Tm_app (uu____130))
in (FStar_Syntax_Syntax.mk uu____129))
in (uu____122 FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let pat : 'Auu____193 . 'Auu____193  ->  'Auu____193 FStar_Syntax_Syntax.withinfo_t = (fun p -> (FStar_Syntax_Syntax.withinfo p FStar_Range.dummyRange))


let mk_match : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun h1 branches -> (

let branches1 = (FStar_All.pipe_right branches (FStar_List.map FStar_Syntax_Util.branch))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((h1), (branches1)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)))


let pred_nat : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun s -> (

let zbranch = (

let uu____300 = (pat (FStar_Syntax_Syntax.Pat_cons (((znat_l), ([])))))
in ((uu____300), (FStar_Pervasives_Native.None), (znat)))
in (

let sbranch = (

let uu____342 = (

let uu____345 = (

let uu____346 = (

let uu____359 = (

let uu____368 = (

let uu____375 = (pat (FStar_Syntax_Syntax.Pat_var (FStar_Tests_Util.x)))
in ((uu____375), (false)))
in (uu____368)::[])
in ((snat_l), (uu____359)))
in FStar_Syntax_Syntax.Pat_cons (uu____346))
in (pat uu____345))
in (

let uu____400 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_bvar ((

let uu___79_405 = FStar_Tests_Util.x
in {FStar_Syntax_Syntax.ppname = uu___79_405.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = uu___79_405.FStar_Syntax_Syntax.sort}))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in ((uu____342), (FStar_Pervasives_Native.None), (uu____400))))
in (mk_match s ((zbranch)::(sbranch)::[])))))


let minus_nat : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 -> (

let minus1 = FStar_Tests_Util.m
in (

let zbranch = (

let uu____442 = (pat (FStar_Syntax_Syntax.Pat_cons (((znat_l), ([])))))
in (

let uu____459 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in ((uu____442), (FStar_Pervasives_Native.None), (uu____459))))
in (

let sbranch = (

let uu____483 = (

let uu____486 = (

let uu____487 = (

let uu____500 = (

let uu____509 = (

let uu____516 = (pat (FStar_Syntax_Syntax.Pat_var (FStar_Tests_Util.n)))
in ((uu____516), (false)))
in (uu____509)::[])
in ((snat_l), (uu____500)))
in FStar_Syntax_Syntax.Pat_cons (uu____487))
in (pat uu____486))
in (

let uu____541 = (

let uu____544 = (FStar_Tests_Util.nm minus1)
in (

let uu____547 = (

let uu____550 = (

let uu____551 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (pred_nat uu____551))
in (

let uu____554 = (

let uu____557 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (uu____557)::[])
in (uu____550)::uu____554))
in (FStar_Tests_Util.app uu____544 uu____547)))
in ((uu____483), (FStar_Pervasives_Native.None), (uu____541))))
in (

let lb = (

let uu____569 = (FStar_Ident.lid_of_path (("Pure")::[]) FStar_Range.dummyRange)
in (

let uu____570 = (

let uu____573 = (

let uu____574 = (

let uu____575 = (b FStar_Tests_Util.x)
in (

let uu____580 = (

let uu____587 = (b FStar_Tests_Util.y)
in (uu____587)::[])
in (uu____575)::uu____580))
in (

let uu____604 = (

let uu____607 = (FStar_Tests_Util.nm FStar_Tests_Util.y)
in (mk_match uu____607 ((zbranch)::(sbranch)::[])))
in (FStar_Syntax_Util.abs uu____574 uu____604 FStar_Pervasives_Native.None)))
in (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NM (((minus1), ((Prims.parse_int "0")))))::[]) uu____573))
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (minus1); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = uu____569; FStar_Syntax_Syntax.lbdef = uu____570; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange}))
in (

let uu____612 = (

let uu____619 = (

let uu____620 = (

let uu____633 = (

let uu____636 = (

let uu____637 = (FStar_Tests_Util.nm minus1)
in (FStar_Tests_Util.app uu____637 ((t1)::(t2)::[])))
in (FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NM (((minus1), ((Prims.parse_int "0")))))::[]) uu____636))
in ((((true), ((lb)::[]))), (uu____633)))
in FStar_Syntax_Syntax.Tm_let (uu____620))
in (FStar_Syntax_Syntax.mk uu____619))
in (uu____612 FStar_Pervasives_Native.None FStar_Range.dummyRange)))))))


let encode_nat : Prims.int  ->  FStar_Syntax_Syntax.term = (fun n1 -> (

let rec aux = (fun out n2 -> (match ((Prims.op_Equality n2 (Prims.parse_int "0"))) with
| true -> begin
out
end
| uu____669 -> begin
(

let uu____670 = (snat out)
in (aux uu____670 (n2 - (Prims.parse_int "1"))))
end))
in (aux znat n1)))


let run : Prims.int  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  unit = (fun i r expected -> ((

let uu____687 = (FStar_Util.string_of_int i)
in (FStar_Util.print1 "%s: ... \n" uu____687));
(

let tcenv = (FStar_Tests_Pars.init ())
in ((

let uu____690 = (FStar_Main.process_args ())
in (FStar_All.pipe_right uu____690 (fun a245 -> ())));
(

let x1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.Primops)::[]) tcenv r)
in ((FStar_Options.init ());
(FStar_Options.set_option "print_universes" (FStar_Options.Bool (true)));
(FStar_Options.set_option "print_implicits" (FStar_Options.Bool (true)));
(

let uu____707 = (

let uu____708 = (FStar_Syntax_Util.unascribe x1)
in (FStar_Tests_Util.term_eq uu____708 expected))
in (FStar_Tests_Util.always i uu____707));
));
));
))


let run_all : unit  ->  unit = (fun uu____715 -> ((FStar_Util.print_string "Testing the normalizer\n");
(FStar_Tests_Pars.pars_and_tc_fragment "let rec copy (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::copy tl");
(FStar_Tests_Pars.pars_and_tc_fragment "let recons (x:list int) : Tot (list int) = match x with | [] -> []  | hd::tl -> hd::tl");
(FStar_Tests_Pars.pars_and_tc_fragment "let rev (x:list \'a) : Tot (list \'a) = let rec aux (x:list \'a) (out:list \'a) : Tot (list \'a) = match x with | [] -> out | hd::tl -> aux tl (hd::out) in aux x []");
(FStar_Tests_Pars.pars_and_tc_fragment "type t = | A : int -> int -> t | B : int -> int -> t let f = function | A x y | B y x -> y - x");
(FStar_Options.__set_unit_tests ());
(

let uu____723 = (

let uu____724 = (

let uu____727 = (

let uu____730 = (

let uu____733 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (uu____733)::[])
in (id)::uu____730)
in (one)::uu____727)
in (FStar_Tests_Util.app apply uu____724))
in (

let uu____734 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (run (Prims.parse_int "0") uu____723 uu____734)));
(

let uu____736 = (

let uu____737 = (

let uu____740 = (

let uu____743 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (

let uu____744 = (

let uu____747 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (uu____747)::[])
in (uu____743)::uu____744))
in (tt)::uu____740)
in (FStar_Tests_Util.app apply uu____737))
in (

let uu____748 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (run (Prims.parse_int "1") uu____736 uu____748)));
(

let uu____750 = (

let uu____751 = (

let uu____754 = (

let uu____757 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (

let uu____758 = (

let uu____761 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (uu____761)::[])
in (uu____757)::uu____758))
in (ff)::uu____754)
in (FStar_Tests_Util.app apply uu____751))
in (

let uu____762 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (run (Prims.parse_int "2") uu____750 uu____762)));
(

let uu____764 = (

let uu____765 = (

let uu____768 = (

let uu____771 = (

let uu____774 = (

let uu____777 = (

let uu____780 = (

let uu____783 = (

let uu____786 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (

let uu____787 = (

let uu____790 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (uu____790)::[])
in (uu____786)::uu____787))
in (ff)::uu____783)
in (apply)::uu____780)
in (apply)::uu____777)
in (apply)::uu____774)
in (apply)::uu____771)
in (apply)::uu____768)
in (FStar_Tests_Util.app apply uu____765))
in (

let uu____791 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (run (Prims.parse_int "3") uu____764 uu____791)));
(

let uu____793 = (

let uu____794 = (

let uu____797 = (

let uu____800 = (

let uu____803 = (FStar_Tests_Util.nm FStar_Tests_Util.n)
in (

let uu____804 = (

let uu____807 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (uu____807)::[])
in (uu____803)::uu____804))
in (ff)::uu____800)
in (apply)::uu____797)
in (FStar_Tests_Util.app twice uu____794))
in (

let uu____808 = (FStar_Tests_Util.nm FStar_Tests_Util.m)
in (run (Prims.parse_int "4") uu____793 uu____808)));
(

let uu____810 = (minus one z)
in (run (Prims.parse_int "5") uu____810 one));
(

let uu____812 = (FStar_Tests_Util.app pred ((one)::[]))
in (run (Prims.parse_int "6") uu____812 z));
(

let uu____814 = (minus one one)
in (run (Prims.parse_int "7") uu____814 z));
(

let uu____816 = (FStar_Tests_Util.app mul ((one)::(one)::[]))
in (run (Prims.parse_int "8") uu____816 one));
(

let uu____818 = (FStar_Tests_Util.app mul ((two)::(one)::[]))
in (run (Prims.parse_int "9") uu____818 two));
(

let uu____820 = (

let uu____821 = (

let uu____824 = (FStar_Tests_Util.app succ ((one)::[]))
in (uu____824)::(one)::[])
in (FStar_Tests_Util.app mul uu____821))
in (run (Prims.parse_int "10") uu____820 two));
(

let uu____826 = (

let uu____827 = (encode (Prims.parse_int "10"))
in (

let uu____828 = (encode (Prims.parse_int "10"))
in (minus uu____827 uu____828)))
in (run (Prims.parse_int "11") uu____826 z));
(

let uu____832 = (

let uu____833 = (encode (Prims.parse_int "100"))
in (

let uu____834 = (encode (Prims.parse_int "100"))
in (minus uu____833 uu____834)))
in (run (Prims.parse_int "12") uu____832 z));
(

let uu____838 = (

let uu____839 = (encode (Prims.parse_int "100"))
in (

let uu____840 = (

let uu____843 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (

let uu____844 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (minus uu____843 uu____844)))
in (let_ FStar_Tests_Util.x uu____839 uu____840)))
in (run (Prims.parse_int "13") uu____838 z));
(

let uu____848 = (

let uu____849 = (FStar_Tests_Util.app succ ((one)::[]))
in (

let uu____850 = (

let uu____853 = (

let uu____854 = (

let uu____857 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (

let uu____858 = (

let uu____861 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (uu____861)::[])
in (uu____857)::uu____858))
in (FStar_Tests_Util.app mul uu____854))
in (

let uu____862 = (

let uu____865 = (

let uu____866 = (

let uu____869 = (FStar_Tests_Util.nm FStar_Tests_Util.y)
in (

let uu____870 = (

let uu____873 = (FStar_Tests_Util.nm FStar_Tests_Util.y)
in (uu____873)::[])
in (uu____869)::uu____870))
in (FStar_Tests_Util.app mul uu____866))
in (

let uu____874 = (

let uu____877 = (FStar_Tests_Util.nm FStar_Tests_Util.h)
in (

let uu____878 = (FStar_Tests_Util.nm FStar_Tests_Util.h)
in (minus uu____877 uu____878)))
in (let_ FStar_Tests_Util.h uu____865 uu____874)))
in (let_ FStar_Tests_Util.y uu____853 uu____862)))
in (let_ FStar_Tests_Util.x uu____849 uu____850)))
in (run (Prims.parse_int "14") uu____848 z));
(

let uu____882 = (

let uu____883 = (FStar_Tests_Util.app succ ((one)::[]))
in (

let uu____886 = (

let uu____887 = (

let uu____890 = (

let uu____893 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (

let uu____894 = (

let uu____897 = (FStar_Tests_Util.nm FStar_Tests_Util.x)
in (uu____897)::[])
in (uu____893)::uu____894))
in (FStar_Tests_Util.app mul uu____890))
in (

let uu____898 = (

let uu____899 = (

let uu____902 = (

let uu____905 = (FStar_Tests_Util.nm FStar_Tests_Util.y)
in (

let uu____906 = (

let uu____909 = (FStar_Tests_Util.nm FStar_Tests_Util.y)
in (uu____909)::[])
in (uu____905)::uu____906))
in (FStar_Tests_Util.app mul uu____902))
in (

let uu____910 = (

let uu____911 = (FStar_Tests_Util.nm FStar_Tests_Util.h)
in (

let uu____912 = (FStar_Tests_Util.nm FStar_Tests_Util.h)
in (minus uu____911 uu____912)))
in (mk_let FStar_Tests_Util.h uu____899 uu____910)))
in (mk_let FStar_Tests_Util.y uu____887 uu____898)))
in (mk_let FStar_Tests_Util.x uu____883 uu____886)))
in (run (Prims.parse_int "15") uu____882 z));
(

let uu____916 = (

let uu____917 = (

let uu____920 = (snat znat)
in (snat uu____920))
in (pred_nat uu____917))
in (

let uu____921 = (snat znat)
in (run (Prims.parse_int "16") uu____916 uu____921)));
(

let uu____923 = (

let uu____924 = (

let uu____925 = (snat znat)
in (snat uu____925))
in (

let uu____926 = (snat znat)
in (minus_nat uu____924 uu____926)))
in (

let uu____927 = (snat znat)
in (run (Prims.parse_int "17") uu____923 uu____927)));
(

let uu____929 = (

let uu____930 = (encode_nat (Prims.parse_int "100"))
in (

let uu____931 = (encode_nat (Prims.parse_int "100"))
in (minus_nat uu____930 uu____931)))
in (run (Prims.parse_int "18") uu____929 znat));
(

let uu____933 = (

let uu____934 = (encode_nat (Prims.parse_int "10000"))
in (

let uu____935 = (encode_nat (Prims.parse_int "10000"))
in (minus_nat uu____934 uu____935)))
in (run (Prims.parse_int "19") uu____933 znat));
(

let uu____937 = (

let uu____938 = (encode_nat (Prims.parse_int "10"))
in (

let uu____939 = (encode_nat (Prims.parse_int "10"))
in (minus_nat uu____938 uu____939)))
in (run (Prims.parse_int "20") uu____937 znat));
(FStar_Options.__clear_unit_tests ());
(

let uu____942 = (FStar_Tests_Pars.tc "recons [0;1]")
in (

let uu____943 = (FStar_Tests_Pars.tc "[0;1]")
in (run (Prims.parse_int "21") uu____942 uu____943)));
(

let uu____945 = (FStar_Tests_Pars.tc "copy [0;1]")
in (

let uu____946 = (FStar_Tests_Pars.tc "[0;1]")
in (run (Prims.parse_int "22") uu____945 uu____946)));
(

let uu____948 = (FStar_Tests_Pars.tc "rev [0;1;2;3;4;5;6;7;8;9;10]")
in (

let uu____949 = (FStar_Tests_Pars.tc "[10;9;8;7;6;5;4;3;2;1;0]")
in (run (Prims.parse_int "23") uu____948 uu____949)));
(

let uu____951 = (FStar_Tests_Pars.tc "f (B 5 3)")
in (

let uu____952 = (FStar_Tests_Pars.tc "2")
in (run (Prims.parse_int "1062") uu____951 uu____952)));
(FStar_Util.print_string "Normalizer ok\n");
))




