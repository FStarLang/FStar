(set-option :global-decls false)
(set-option :smt.mbqi false)
(declare-sort Ref)
(declare-fun Ref_constr_id (Ref) Int)

(declare-sort String)
(declare-fun String_constr_id (String) Int)

(declare-sort Kind)
(declare-fun Kind_constr_id (Kind) Int)

(declare-sort Type)
(declare-fun Type_constr_id (Type) Int)

(declare-sort Term)
(declare-fun Term_constr_id (Term) Int)
(declare-datatypes () ((Fuel 
(ZFuel) 
(SFuel (prec Fuel)))))
(declare-fun MaxIFuel () Fuel)
(declare-fun MaxFuel () Fuel)
(declare-fun PreKind (Type) Kind)
(declare-fun PreType (Term) Type)
(declare-fun Valid (Type) Bool)
(declare-fun HasKind (Type Kind) Bool)
(declare-fun HasTypeFuel (Fuel Term Type) Bool)
(define-fun HasTypeZ ((x Term) (t Type)) Bool
(HasTypeFuel ZFuel x t))
(define-fun HasType ((x Term) (t Type)) Bool
(HasTypeFuel MaxIFuel x t))
;;fuel irrelevance
(assert (forall ((f Fuel) (x Term) (t Type))
(! (= (HasTypeFuel (SFuel f) x t)
(HasTypeZ x t))
:pattern ((HasTypeFuel (SFuel f) x t)))))
(define-fun  IsTyped ((x Term)) Bool
(exists ((t Type)) (HasTypeZ x t)))
(declare-fun ApplyEF (Term Fuel) Term)
(declare-fun ApplyEE (Term Term) Term)
(declare-fun ApplyET (Term Type) Term)
(declare-fun ApplyTE (Type Term) Type)
(declare-fun ApplyTT (Type Type) Type)
(declare-fun Rank (Term) Int)
(declare-fun Closure (Term) Term)
(declare-fun ConsTerm (Term Term) Term)
(declare-fun ConsType (Type Term) Term)
(declare-fun ConsFuel (Fuel Term) Term)
(declare-fun Precedes (Term Term) Type)
(assert (forall ((t Type))
(! (implies (exists ((e Term)) (HasType e t))
(Valid t))
:pattern ((Valid t)))))
(assert (forall ((t1 Term) (t2 Term))
(! (iff (Valid (Precedes t1 t2)) 
(< (Rank t1) (Rank t2)))
:pattern ((Precedes t1 t2)))))
(define-fun Prims.Precedes ((a Type) (b Type) (t1 Term) (t2 Term)) Type
(Precedes t1 t2))

; <start constructor String_const>
;;;;;;;;;;;;;;;;Constructor
(declare-fun String_const (Int) String)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 0
(String_constr_id (String_const @u0)))
  
:pattern ((String_const @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun String_const_proj_0 (String) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (String_const_proj_0 (String_const @u0))
@u0)
  
:pattern ((String_const @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-String_const ((@u0 String)) Bool
 (and (= (String_constr_id @u0)
0)
(= @u0
(String_const (String_const_proj_0 @u0)))))

; </end constructor String_const>

; <start constructor Kind_type>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Kind_type () Kind)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 0
(Kind_constr_id Kind_type)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Kind_type ((@u0 Kind)) Bool
 (and (= (Kind_constr_id @u0)
0)
(= @u0
Kind_type)))

; </end constructor Kind_type>

; <start constructor Kind_arrow>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Kind_arrow (Int) Kind)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 1
(Kind_constr_id (Kind_arrow @u0)))
  
:pattern ((Kind_arrow @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Kind_arrow_id (Kind) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (Kind_arrow_id (Kind_arrow @u0))
@u0)
  
:pattern ((Kind_arrow @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Kind_arrow ((@u0 Kind)) Bool
 (and (= (Kind_constr_id @u0)
1)
(= @u0
(Kind_arrow (Kind_arrow_id @u0)))))

; </end constructor Kind_arrow>

; <start constructor Kind_uvar>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Kind_uvar (Int) Kind)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 2
(Kind_constr_id (Kind_uvar @u0)))
  
:pattern ((Kind_uvar @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Kind_uvar_fst (Kind) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (Kind_uvar_fst (Kind_uvar @u0))
@u0)
  
:pattern ((Kind_uvar @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Kind_uvar ((@u0 Kind)) Bool
 (and (= (Kind_constr_id @u0)
2)
(= @u0
(Kind_uvar (Kind_uvar_fst @u0)))))

; </end constructor Kind_uvar>

; <start constructor Typ_fun>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Typ_fun (Int) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 1
(Type_constr_id (Typ_fun @u0)))
  
:pattern ((Typ_fun @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Typ_fun_id (Type) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (Typ_fun_id (Typ_fun @u0))
@u0)
  
:pattern ((Typ_fun @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Typ_fun ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1)
(= @a0
(Typ_fun (Typ_fun_id @a0)))))

; </end constructor Typ_fun>

; <start constructor Typ_app>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Typ_app (Type Type) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 2
(Type_constr_id (Typ_app @a0
@a1)))
  
:pattern ((Typ_app @a0
@a1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Typ_app_fst (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Typ_app_fst (Typ_app @a0
@a1))
@a0)
  
:pattern ((Typ_app @a0
@a1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Typ_app_snd (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Typ_app_snd (Typ_app @a0
@a1))
@a1)
  
:pattern ((Typ_app @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Typ_app ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2)
(= @a0
(Typ_app (Typ_app_fst @a0)
(Typ_app_snd @a0)))))

; </end constructor Typ_app>

; <start constructor Typ_dep>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Typ_dep (Type Term) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 3
(Type_constr_id (Typ_dep @a0
@x1)))
  
:pattern ((Typ_dep @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Typ_dep_fst (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Typ_dep_fst (Typ_dep @a0
@x1))
@a0)
  
:pattern ((Typ_dep @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Typ_dep_snd (Type) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Typ_dep_snd (Typ_dep @a0
@x1))
@x1)
  
:pattern ((Typ_dep @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Typ_dep ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
3)
(= @a0
(Typ_dep (Typ_dep_fst @a0)
(Typ_dep_snd @a0)))))

; </end constructor Typ_dep>

; <start constructor Typ_uvar>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Typ_uvar (Int) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 4
(Type_constr_id (Typ_uvar @u0)))
  
:pattern ((Typ_uvar @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Typ_uvar_fst (Type) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (Typ_uvar_fst (Typ_uvar @u0))
@u0)
  
:pattern ((Typ_uvar @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Typ_uvar ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
4)
(= @a0
(Typ_uvar (Typ_uvar_fst @a0)))))

; </end constructor Typ_uvar>

; <start constructor Term_unit>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Term_unit () Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 0
(Term_constr_id Term_unit)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Term_unit ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
0)
(= @x0
Term_unit)))

; </end constructor Term_unit>

; <start constructor BoxInt>
;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxInt (Int) Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 1
(Term_constr_id (BoxInt @u0)))
  
:pattern ((BoxInt @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxInt_proj_0 (Term) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (BoxInt_proj_0 (BoxInt @u0))
@u0)
  
:pattern ((BoxInt @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxInt ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1)
(= @x0
(BoxInt (BoxInt_proj_0 @x0)))))

; </end constructor BoxInt>

; <start constructor BoxBool>
;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxBool (Bool) Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Bool))
 (! (= 2
(Term_constr_id (BoxBool @u0)))
  
:pattern ((BoxBool @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxBool_proj_0 (Term) Bool)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Bool))
 (! (= (BoxBool_proj_0 (BoxBool @u0))
@u0)
  
:pattern ((BoxBool @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxBool ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
2)
(= @x0
(BoxBool (BoxBool_proj_0 @x0)))))

; </end constructor BoxBool>

; <start constructor BoxString>
;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxString (String) Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 String))
 (! (= 3
(Term_constr_id (BoxString @u0)))
  
:pattern ((BoxString @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxString_proj_0 (Term) String)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 String))
 (! (= (BoxString_proj_0 (BoxString @u0))
@u0)
  
:pattern ((BoxString @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxString ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
3)
(= @x0
(BoxString (BoxString_proj_0 @x0)))))

; </end constructor BoxString>

; <start constructor BoxRef>
;;;;;;;;;;;;;;;;Constructor
(declare-fun BoxRef (Ref) Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Ref))
 (! (= 4
(Term_constr_id (BoxRef @u0)))
  
:pattern ((BoxRef @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun BoxRef_proj_0 (Term) Ref)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Ref))
 (! (= (BoxRef_proj_0 (BoxRef @u0))
@u0)
  
:pattern ((BoxRef @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-BoxRef ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
4)
(= @x0
(BoxRef (BoxRef_proj_0 @x0)))))

; </end constructor BoxRef>

; <start constructor Exp_uvar>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Exp_uvar (Int) Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@u0 Int))
 (! (= 5
(Term_constr_id (Exp_uvar @u0)))
  
:pattern ((Exp_uvar @u0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Exp_uvar_fst (Term) Int)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@u0 Int))
 (! (= (Exp_uvar_fst (Exp_uvar @u0))
@u0)
  
:pattern ((Exp_uvar @u0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Exp_uvar ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
5)
(= @x0
(Exp_uvar (Exp_uvar_fst @x0)))))

; </end constructor Exp_uvar>

; <start constructor LexCons>
;;;;;;;;;;;;;;;;Constructor
(declare-fun LexCons (Term Term) Term)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= 6
(Term_constr_id (LexCons @x0
@x1)))
  
:pattern ((LexCons @x0
@x1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun LexCons_0 (Term) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (LexCons_0 (LexCons @x0
@x1))
@x0)
  
:pattern ((LexCons @x0
@x1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun LexCons_1 (Term) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (LexCons_1 (LexCons @x0
@x1))
@x1)
  
:pattern ((LexCons @x0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-LexCons ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
6)
(= @x0
(LexCons (LexCons_0 @x0)
(LexCons_1 @x0)))))

; </end constructor LexCons>
(define-fun is-Prims.LexCons ((t Term)) Bool 
(is-LexCons t))
(assert (forall ((x1 Term) (x2 Term) (y1 Term) (y2 Term))
(iff (Valid (Precedes (LexCons x1 x2) (LexCons y1 y2)))
(or (Valid (Precedes x1 y1))
(and (= x1 y1)
(Valid (Precedes x2 y2)))))))


; encoding sigelt Prims.Unop

; <Skipped Prims.Unop/>

; encoding sigelt Prims.Binop

; <Skipped Prims.Binop/>

; encoding sigelt Prims.bool

; <Start encoding Prims.bool>

; <start constructor Prims.bool>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.bool () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 14
(Type_constr_id Prims.bool)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.bool ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
14)
(= @a0
Prims.bool)))

; </end constructor Prims.bool>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.bool
Kind_type))
;;;;;;;;;;;;;;;;bool inversion
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Prims.bool)
(is-BoxBool @x1))
  
:pattern ((HasTypeFuel @u0
@x1
Prims.bool)))))
;;;;;;;;;;;;;;;;bool typing
(assert (forall ((@u0 Bool))
 (! (HasType (BoxBool @u0)
Prims.bool)
  
:pattern ((BoxBool @u0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.bool)
(= Prims.bool
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.bool)))))

; </end encoding Prims.bool>

; encoding sigelt Prims.EqTyp

; <Start encoding Prims.EqTyp>
(declare-fun Prims.EqTyp (Type Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.EqTyp@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 19
(Type_constr_id Prims.EqTyp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.EqTyp@tok
@a0)
@a1)
(Prims.EqTyp @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.EqTyp@tok
@a0)
@a1))

:pattern ((Prims.EqTyp @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.EqTyp@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.EqTyp @a0
@a1)
Kind_type))
  
:pattern ((Prims.EqTyp @a0
@a1)))))

; </end encoding Prims.EqTyp>

; encoding sigelt Prims.Eq2

; <Start encoding Prims.Eq2>

; <start constructor Prims.Eq2>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Eq2 (Type Type Term Term) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= 20
(Type_constr_id (Prims.Eq2 @a0
@a1
@x2
@x3)))
  
:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Eq2@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.Eq2@a0 (Prims.Eq2 @a0
@a1
@x2
@x3))
@a0)
  
:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Eq2@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.Eq2@a1 (Prims.Eq2 @a0
@a1
@x2
@x3))
@a1)
  
:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Eq2@x2 (Type) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.Eq2@x2 (Prims.Eq2 @a0
@a1
@x2
@x3))
@x2)
  
:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Eq2@x3 (Type) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.Eq2@x3 (Prims.Eq2 @a0
@a1
@x2
@x3))
@x3)
  
:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Eq2 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
20)
(= @a0
(Prims.Eq2 (Prims.Eq2@a0 @a0)
(Prims.Eq2@a1 @a0)
(Prims.Eq2@x2 @a0)
(Prims.Eq2@x3 @a0)))))

; </end constructor Prims.Eq2>
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Eq2@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 21
(Type_constr_id Prims.Eq2@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT Prims.Eq2@tok
@a0)
@a1)
@x2)
@x3)
(Prims.Eq2 @a0
@a1
@x2
@x3))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT Prims.Eq2@tok
@a0)
@a1)
@x2)
@x3))

:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Eq2@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
@a0)
(HasType @x3
@a1))
(HasKind (Prims.Eq2 @a0
@a1
@x2
@x3)
Kind_type))
  
:pattern ((Prims.Eq2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Eq2 interpretation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (iff (= @x2
@x3)
(Valid (Prims.Eq2 @a0
@a1
@x2
@x3)))
  
:pattern ((Valid (Prims.Eq2 @a0
@a1
@x2
@x3))))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Eq2 @a2
@a3
@x4
@x5))
(= (Prims.Eq2 @a2
@a3
@x4
@x5)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Eq2 @a2
@a3
@x4
@x5))))))

; </end encoding Prims.Eq2>

; encoding sigelt Prims.b2t

; <Start encoding Prims.b2t>
(declare-fun Prims.b2t (Term) Type)
;;;;;;;;;;;;;;;;b2t def
(assert (forall ((@x0 Term))
 (! (= (Valid (Prims.b2t @x0))
(BoxBool_proj_0 @x0))
  
:pattern ((Valid (Prims.b2t @x0))))))

; </end encoding Prims.b2t>

; encoding sigelt Prims.True, Prims.T

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.True () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.T () Term)
;;;;;;;;;;;;;;;;data constructor proxy: T
(declare-fun Prims.T@tok () Term)

; <Start encoding Prims.True>

; <start constructor Prims.True>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 29
(Type_constr_id Prims.True)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.True ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
29)
(= @a0
Prims.True)))

; </end constructor Prims.True>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.True
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.True)
(= Prims.True
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.True)))))

; </end encoding Prims.True>

; <Start encoding Prims.T>

; <start constructor Prims.T>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 35
(Term_constr_id Prims.T)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.T ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
35)
(= @x0
Prims.T)))

; </end constructor Prims.T>
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.T@tok
Prims.True))
;;;;;;;;;;;;;;;;equality for proxy
(assert (= Prims.T@tok
Prims.T))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel))
 (! (HasTypeFuel @u0
Prims.T
Prims.True)
  
:pattern ((HasTypeFuel @u0
Prims.T
Prims.True)))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert true)
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.T>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
Prims.True)
(is-Prims.T @x1))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
Prims.True)))))

; </end encoding >

; encoding sigelt Prims.is_T

; <Start encoding Prims.is_T>
(declare-fun Prims.is_T (Term) Term)
;;;;;;;;;;;;;;;;(True -> Tot bool)
(declare-fun Typ_fun_37 () Type)
;;;;;;;;;;;;;;;;Typ_fun_37 kinding
(assert (HasKind Typ_fun_37
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_37)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_37)))))
;;;;;;;;;;;;;;;;Typ_fun_37 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_37)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Prims.True)
(HasType (ApplyEE @x0
@x1)
Prims.bool))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_37)))))
(declare-fun Prims.is_T@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 39
(Term_constr_id Prims.is_T@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_T@tok
@x0)
(Prims.is_T @x0))
  
:pattern ((ApplyEE Prims.is_T@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_T@tok
Typ_fun_37))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.True)
(HasType (Prims.is_T @x0)
Prims.bool))
  
:pattern ((Prims.is_T @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (Prims.is_T @x0)
(BoxBool (is-Prims.T @x0)))
  
:pattern ((Prims.is_T @x0)))))

; </end encoding Prims.is_T>

; encoding sigelt Prims.False

; <Start encoding Prims.False>
(declare-fun Prims.False () Type)
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.False
Kind_type))

; </end encoding Prims.False>

; encoding sigelt Prims.l_imp

; <Start encoding Prims.l_imp>
(declare-fun Prims.l_imp (Type Type) Type)
(declare-fun Prims.l_imp@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 41
(Type_constr_id Prims.l_imp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.l_imp@tok
@a0)
@a1)
(Prims.l_imp @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.l_imp@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;(p -> Tot q)
(declare-fun Typ_fun_43 (Type Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_43 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_43 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_43 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u0
@x1
(Typ_fun_43 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_43 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_43 interpretation
(assert (forall ((@x0 Term) (@a1 Type) (@a2 Type))
 (! (iff (HasTypeZ @x0
(Typ_fun_43 @a1
@a2))
(forall ((@x3 Term))
 (! (implies (HasType @x3
@a2)
(HasType (ApplyEE @x0
@x3)
@a1))
  
:pattern ((ApplyEE @x0
@x3)))))
  
:pattern ((HasTypeZ @x0
(Typ_fun_43 @a1
@a2))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(= (Prims.l_imp @a0
@a1)
(Typ_fun_43 @a1
@a0)))
  
:pattern ((Prims.l_imp @a0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.l_imp @a0
@a1)
Kind_type))
  
:pattern ((Prims.l_imp @a0
@a1)))))
;;;;;;;;;;;;;;;;==> interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (implies (Valid @a0)
(Valid @a1))
(Valid (Prims.l_imp @a0
@a1)))
  
:pattern ((Valid (Prims.l_imp @a0
@a1))))))

; </end encoding Prims.l_imp>

; encoding sigelt Prims.l_and, Prims.And

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.l_and (Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.l_and@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.l_and@a1 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.l_and@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.And (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And_p (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And_q (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And__0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And__1 (Term) Term)
;;;;;;;;;;;;;;;;(_0:p -> _1:q -> Tot (p /\ q))
(declare-fun Typ_fun_64 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: And
(declare-fun Prims.And@tok () Term)

; <Start encoding Prims.l_and>

; <start constructor Prims.l_and>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 55
(Type_constr_id (Prims.l_and @a0
@a1)))
  
:pattern ((Prims.l_and @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.l_and@a0 (Prims.l_and @a0
@a1))
@a0)
  
:pattern ((Prims.l_and @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.l_and@a1 (Prims.l_and @a0
@a1))
@a1)
  
:pattern ((Prims.l_and @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.l_and ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
55)
(= @a0
(Prims.l_and (Prims.l_and@a0 @a0)
(Prims.l_and@a1 @a0)))))

; </end constructor Prims.l_and>
;;;;;;;;;;;;;;;;fresh token
(assert (= 56
(Type_constr_id Prims.l_and@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.l_and@tok
@a0)
@a1)
(Prims.l_and @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.l_and@tok
@a0)
@a1))

:pattern ((Prims.l_and @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.l_and@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.l_and @a0
@a1)
Kind_type))
  
:pattern ((Prims.l_and @a0
@a1)))))
;;;;;;;;;;;;;;;;/\ interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (and (Valid @a0)
(Valid @a1))
(Valid (Prims.l_and @a0
@a1)))
  
:pattern ((Valid (Prims.l_and @a0
@a1))))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.l_and @a2
@a3))
(= (Prims.l_and @a2
@a3)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.l_and @a2
@a3))))))

; </end encoding Prims.l_and>

; <Start encoding Prims.And>

; <start constructor Prims.And>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= 62
(Term_constr_id (Prims.And @a0
@a1
@x2
@x3)))
  
:pattern ((Prims.And @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.And_p (Prims.And @a0
@a1
@x2
@x3))
@a0)
  
:pattern ((Prims.And @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.And_q (Prims.And @a0
@a1
@x2
@x3))
@a1)
  
:pattern ((Prims.And @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.And__0 (Prims.And @a0
@a1
@x2
@x3))
@x2)
  
:pattern ((Prims.And @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.And__1 (Prims.And @a0
@a1
@x2
@x3))
@x3)
  
:pattern ((Prims.And @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.And ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
62)
(= @x0
(Prims.And (Prims.And_p @x0)
(Prims.And_q @x0)
(Prims.And__0 @x0)
(Prims.And__1 @x0)))))

; </end constructor Prims.And>
;;;;;;;;;;;;;;;;Typ_fun_64 kinding
(assert (HasKind Typ_fun_64
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_64)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_64)))))
;;;;;;;;;;;;;;;;Typ_fun_64 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_64)
(forall ((@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
@a1)
(HasType @x4
@a2))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
(Prims.l_and @a1
@a2)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_64)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 66
(Term_constr_id Prims.And@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.And@tok
Typ_fun_64))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET Prims.And@tok
@a0)
@a1)
@x2)
@x3)
(Prims.And @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET Prims.And@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1)
(HasTypeFuel @u0
@x4
@a2))
(HasTypeFuel @u0
(Prims.And @a1
@a2
@x3
@x4)
(Prims.l_and @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.And @a1
@a2
@x3
@x4)
(Prims.l_and @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.And @a1
@a2
@x3
@x4)
(Prims.l_and @a5
@a6))
(and (= @a2
@a6)
(= @a1
@a5)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1)
(HasTypeFuel @u0
@x4
@a2)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.And @a1
@a2
@x3
@x4)
(Prims.l_and @a5
@a6))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.And @a1
@a2
@x3
@x4)
(Prims.l_and @a5
@a6))
(and (Valid (Precedes @x3
(Prims.And @a1
@a2
@x3
@x4)))
(Valid (Precedes @x4
(Prims.And @a1
@a2
@x3
@x4)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.And @a1
@a2
@x3
@x4)
(Prims.l_and @a5
@a6))))))

; </end encoding Prims.And>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.l_and @a2
@a3))
(and (is-Prims.And @x1)
(= @a2
(Prims.And_p @x1))
(= @a3
(Prims.And_q @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.l_and @a2
@a3))))))

; </end encoding >

; encoding sigelt Prims.is_And

; <Start encoding Prims.is_And>
(declare-fun Prims.is_And (Type Type Term) Term)
;;;;;;;;;;;;;;;;((p /\ q) -> Tot bool)
(declare-fun Typ_fun_68 () Type)
;;;;;;;;;;;;;;;;Typ_fun_68 kinding
(assert (HasKind Typ_fun_68
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_68)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_68)))))
;;;;;;;;;;;;;;;;Typ_fun_68 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_68)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.l_and @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_68)))))
(declare-fun Prims.is_And@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 70
(Term_constr_id Prims.is_And@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_And@tok
@a0)
@a1)
@x2)
(Prims.is_And @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_And@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_And@tok
Typ_fun_68))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_and @a0
@a1)))
(HasType (Prims.is_And @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_And @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_And @a0
@a1
@x2)
(BoxBool (is-Prims.And @x2)))
  
:pattern ((Prims.is_And @a0
@a1
@x2)))))

; </end encoding Prims.is_And>

; encoding sigelt Prims.And._0

; <Start encoding Prims.And._0>
(declare-fun Prims.And._0 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(p /\ q) -> Tot p)
(declare-fun Typ_fun_72 () Type)
;;;;;;;;;;;;;;;;Typ_fun_72 kinding
(assert (HasKind Typ_fun_72
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_72)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_72)))))
;;;;;;;;;;;;;;;;Typ_fun_72 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_72)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.l_and @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_72)))))
(declare-fun Prims.And._0@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 74
(Term_constr_id Prims.And._0@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.And._0@tok
@a0)
@a1)
@x2)
(Prims.And._0 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.And._0@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.And._0@tok
Typ_fun_72))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_and @a0
@a1)))
(HasType (Prims.And._0 @a0
@a1
@x2)
@a0))
  
:pattern ((Prims.And._0 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.And._0 @a0
@a1
@x2)
(Prims.And__0 @x2))
  
:pattern ((Prims.And._0 @a0
@a1
@x2)))))

; </end encoding Prims.And._0>

; encoding sigelt Prims.And._1

; <Start encoding Prims.And._1>
(declare-fun Prims.And._1 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(p /\ q) -> Tot q)
(declare-fun Typ_fun_76 () Type)
;;;;;;;;;;;;;;;;Typ_fun_76 kinding
(assert (HasKind Typ_fun_76
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_76)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_76)))))
;;;;;;;;;;;;;;;;Typ_fun_76 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_76)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.l_and @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_76)))))
(declare-fun Prims.And._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 78
(Term_constr_id Prims.And._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.And._1@tok
@a0)
@a1)
@x2)
(Prims.And._1 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.And._1@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.And._1@tok
Typ_fun_76))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_and @a0
@a1)))
(HasType (Prims.And._1 @a0
@a1
@x2)
@a1))
  
:pattern ((Prims.And._1 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.And._1 @a0
@a1
@x2)
(Prims.And__1 @x2))
  
:pattern ((Prims.And._1 @a0
@a1
@x2)))))

; </end encoding Prims.And._1>

; encoding sigelt Prims.l_or, Prims.Left, Prims.Right

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.l_or (Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.l_or@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.l_or@a1 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.l_or@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Left (Type Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left_p (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left_q (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left__0 (Term) Term)
;;;;;;;;;;;;;;;;(_0:p -> Tot (p \/ q))
(declare-fun Typ_fun_104 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Left
(declare-fun Prims.Left@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Right (Type Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right_p (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right_q (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right__0 (Term) Term)
;;;;;;;;;;;;;;;;(_0:q -> Tot (p \/ q))
(declare-fun Typ_fun_110 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Right
(declare-fun Prims.Right@tok () Term)

; <Start encoding Prims.l_or>

; <start constructor Prims.l_or>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 95
(Type_constr_id (Prims.l_or @a0
@a1)))
  
:pattern ((Prims.l_or @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.l_or@a0 (Prims.l_or @a0
@a1))
@a0)
  
:pattern ((Prims.l_or @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.l_or@a1 (Prims.l_or @a0
@a1))
@a1)
  
:pattern ((Prims.l_or @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.l_or ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
95)
(= @a0
(Prims.l_or (Prims.l_or@a0 @a0)
(Prims.l_or@a1 @a0)))))

; </end constructor Prims.l_or>
;;;;;;;;;;;;;;;;fresh token
(assert (= 96
(Type_constr_id Prims.l_or@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.l_or@tok
@a0)
@a1)
(Prims.l_or @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.l_or@tok
@a0)
@a1))

:pattern ((Prims.l_or @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.l_or@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.l_or @a0
@a1)
Kind_type))
  
:pattern ((Prims.l_or @a0
@a1)))))
;;;;;;;;;;;;;;;;\/ interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (or (Valid @a0)
(Valid @a1))
(Valid (Prims.l_or @a0
@a1)))
  
:pattern ((Valid (Prims.l_or @a0
@a1))))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.l_or @a2
@a3))
(= (Prims.l_or @a2
@a3)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.l_or @a2
@a3))))))

; </end encoding Prims.l_or>

; <Start encoding Prims.Left>

; <start constructor Prims.Left>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= 102
(Term_constr_id (Prims.Left @a0
@a1
@x2)))
  
:pattern ((Prims.Left @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Left_p (Prims.Left @a0
@a1
@x2))
@a0)
  
:pattern ((Prims.Left @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Left_q (Prims.Left @a0
@a1
@x2))
@a1)
  
:pattern ((Prims.Left @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Left__0 (Prims.Left @a0
@a1
@x2))
@x2)
  
:pattern ((Prims.Left @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Left ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
102)
(= @x0
(Prims.Left (Prims.Left_p @x0)
(Prims.Left_q @x0)
(Prims.Left__0 @x0)))))

; </end constructor Prims.Left>
;;;;;;;;;;;;;;;;Typ_fun_104 kinding
(assert (HasKind Typ_fun_104
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_104)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_104)))))
;;;;;;;;;;;;;;;;Typ_fun_104 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_104)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
@a1))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(Prims.l_or @a1
@a2)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_104)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 106
(Term_constr_id Prims.Left@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Left@tok
Typ_fun_104))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Left@tok
@a0)
@a1)
@x2)
(Prims.Left @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Left@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1))
(HasTypeFuel @u0
(Prims.Left @a1
@a2
@x3)
(Prims.l_or @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.Left @a1
@a2
@x3)
(Prims.l_or @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Left @a1
@a2
@x3)
(Prims.l_or @a4
@a5))
(and (= @a2
@a5)
(= @a1
@a4)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Left @a1
@a2
@x3)
(Prims.l_or @a4
@a5))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Left @a1
@a2
@x3)
(Prims.l_or @a4
@a5))
(Valid (Precedes @x3
(Prims.Left @a1
@a2
@x3))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Left @a1
@a2
@x3)
(Prims.l_or @a4
@a5))))))

; </end encoding Prims.Left>

; <Start encoding Prims.Right>

; <start constructor Prims.Right>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= 108
(Term_constr_id (Prims.Right @a0
@a1
@x2)))
  
:pattern ((Prims.Right @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Right_p (Prims.Right @a0
@a1
@x2))
@a0)
  
:pattern ((Prims.Right @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Right_q (Prims.Right @a0
@a1
@x2))
@a1)
  
:pattern ((Prims.Right @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Right__0 (Prims.Right @a0
@a1
@x2))
@x2)
  
:pattern ((Prims.Right @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Right ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
108)
(= @x0
(Prims.Right (Prims.Right_p @x0)
(Prims.Right_q @x0)
(Prims.Right__0 @x0)))))

; </end constructor Prims.Right>
;;;;;;;;;;;;;;;;Typ_fun_110 kinding
(assert (HasKind Typ_fun_110
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_110)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_110)))))
;;;;;;;;;;;;;;;;Typ_fun_110 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_110)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
@a2))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(Prims.l_or @a1
@a2)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_110)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 112
(Term_constr_id Prims.Right@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Right@tok
Typ_fun_110))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Right@tok
@a0)
@a1)
@x2)
(Prims.Right @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Right@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a2))
(HasTypeFuel @u0
(Prims.Right @a1
@a2
@x3)
(Prims.l_or @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.Right @a1
@a2
@x3)
(Prims.l_or @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Right @a1
@a2
@x3)
(Prims.l_or @a4
@a5))
(and (= @a2
@a5)
(= @a1
@a4)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a2)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Right @a1
@a2
@x3)
(Prims.l_or @a4
@a5))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Right @a1
@a2
@x3)
(Prims.l_or @a4
@a5))
(Valid (Precedes @x3
(Prims.Right @a1
@a2
@x3))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Right @a1
@a2
@x3)
(Prims.l_or @a4
@a5))))))

; </end encoding Prims.Right>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.l_or @a2
@a3))
(or (and (is-Prims.Left @x1)
(= @a2
(Prims.Left_p @x1))
(= @a3
(Prims.Left_q @x1)))
(and (is-Prims.Right @x1)
(= @a2
(Prims.Right_p @x1))
(= @a3
(Prims.Right_q @x1)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.l_or @a2
@a3))))))

; </end encoding >

; encoding sigelt Prims.is_Left

; <Start encoding Prims.is_Left>
(declare-fun Prims.is_Left (Type Type Term) Term)
;;;;;;;;;;;;;;;;((p \/ q) -> Tot bool)
(declare-fun Typ_fun_114 () Type)
;;;;;;;;;;;;;;;;Typ_fun_114 kinding
(assert (HasKind Typ_fun_114
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_114)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_114)))))
;;;;;;;;;;;;;;;;Typ_fun_114 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_114)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.l_or @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_114)))))
(declare-fun Prims.is_Left@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 116
(Term_constr_id Prims.is_Left@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_Left@tok
@a0)
@a1)
@x2)
(Prims.is_Left @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_Left@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Left@tok
Typ_fun_114))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_or @a0
@a1)))
(HasType (Prims.is_Left @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_Left @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_Left @a0
@a1
@x2)
(BoxBool (is-Prims.Left @x2)))
  
:pattern ((Prims.is_Left @a0
@a1
@x2)))))

; </end encoding Prims.is_Left>

; encoding sigelt Prims.is_Right

; <Start encoding Prims.is_Right>
(declare-fun Prims.is_Right (Type Type Term) Term)
(declare-fun Prims.is_Right@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 118
(Term_constr_id Prims.is_Right@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_Right@tok
@a0)
@a1)
@x2)
(Prims.is_Right @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_Right@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Right@tok
Typ_fun_114))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_or @a0
@a1)))
(HasType (Prims.is_Right @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_Right @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_Right @a0
@a1
@x2)
(BoxBool (is-Prims.Right @x2)))
  
:pattern ((Prims.is_Right @a0
@a1
@x2)))))

; </end encoding Prims.is_Right>

; encoding sigelt Prims.Left._0

; <Start encoding Prims.Left._0>
(declare-fun Typ_refine_120 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_120 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_120 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_16:(p \/ q){(is_Left _0_16)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_120 @a2
@a3))
(and (HasTypeFuel @u0
@x1
(Prims.l_or @a3
@a2))
(BoxBool_proj_0 (Prims.is_Left @a3
@a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_120 @a2
@a3))))))
(declare-fun Prims.Left._0 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_16:(p \/ q){(is_Left _0_16)} -> Tot p)
(declare-fun Typ_fun_123 () Type)
;;;;;;;;;;;;;;;;Typ_fun_123 kinding
(assert (HasKind Typ_fun_123
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_123)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_123)))))
;;;;;;;;;;;;;;;;Typ_fun_123 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_123)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_120 @a2
@a1)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_123)))))
(declare-fun Prims.Left._0@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 125
(Term_constr_id Prims.Left._0@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Left._0@tok
@a0)
@a1)
@x2)
(Prims.Left._0 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Left._0@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Left._0@tok
Typ_fun_123))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_120 @a1
@a0)))
(HasType (Prims.Left._0 @a0
@a1
@x2)
@a0))
  
:pattern ((Prims.Left._0 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Left._0 @a0
@a1
@x2)
(Prims.Left__0 @x2))
  
:pattern ((Prims.Left._0 @a0
@a1
@x2)))))

; </end encoding Prims.Left._0>

; encoding sigelt Prims.Right._0

; <Start encoding Prims.Right._0>
(declare-fun Typ_refine_127 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_127 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_127 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_18:(p \/ q){(is_Right _0_18)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_127 @a2
@a3))
(and (HasTypeFuel @u0
@x1
(Prims.l_or @a3
@a2))
(BoxBool_proj_0 (Prims.is_Right @a3
@a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_127 @a2
@a3))))))
(declare-fun Prims.Right._0 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_18:(p \/ q){(is_Right _0_18)} -> Tot q)
(declare-fun Typ_fun_130 () Type)
;;;;;;;;;;;;;;;;Typ_fun_130 kinding
(assert (HasKind Typ_fun_130
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_130)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_130)))))
;;;;;;;;;;;;;;;;Typ_fun_130 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_130)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_127 @a2
@a1)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_130)))))
(declare-fun Prims.Right._0@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 132
(Term_constr_id Prims.Right._0@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Right._0@tok
@a0)
@a1)
@x2)
(Prims.Right._0 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Right._0@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Right._0@tok
Typ_fun_130))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_127 @a1
@a0)))
(HasType (Prims.Right._0 @a0
@a1
@x2)
@a1))
  
:pattern ((Prims.Right._0 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Right._0 @a0
@a1
@x2)
(Prims.Right__0 @x2))
  
:pattern ((Prims.Right._0 @a0
@a1
@x2)))))

; </end encoding Prims.Right._0>

; encoding sigelt Prims.l_iff

; <Start encoding Prims.l_iff>
(declare-fun Prims.l_iff (Type Type) Type)
(declare-fun Prims.l_iff@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 133
(Type_constr_id Prims.l_iff@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.l_iff@tok
@a0)
@a1)
(Prims.l_iff @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.l_iff@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(= (Valid (Prims.l_iff @a0
@a1))
(and (implies (Valid @a0)
(Valid @a1))
(implies (Valid @a1)
(Valid @a0)))))
  
:pattern ((Valid (Prims.l_iff @a0
@a1))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.l_iff @a0
@a1)
Kind_type))
  
:pattern ((Prims.l_iff @a0
@a1)))))
;;;;;;;;;;;;;;;;<==> interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (iff (Valid @a0)
(Valid @a1))
(Valid (Prims.l_iff @a0
@a1)))
  
:pattern ((Valid (Prims.l_iff @a0
@a1))))))

; </end encoding Prims.l_iff>

; encoding sigelt Prims.l_not

; <Start encoding Prims.l_not>
(declare-fun Prims.l_not (Type) Type)
(declare-fun Prims.l_not@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 134
(Type_constr_id Prims.l_not@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.l_not@tok
@a0)
(Prims.l_not @a0))
  
:pattern ((ApplyTT Prims.l_not@tok
@a0)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(= (Valid (Prims.l_not @a0))
(implies (Valid @a0)
false)))
  
:pattern ((Valid (Prims.l_not @a0))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (Prims.l_not @a0)
Kind_type))
  
:pattern ((Prims.l_not @a0)))))

; </end encoding Prims.l_not>

; encoding sigelt Prims.Forall

; <Start encoding Prims.Forall>
;;;;;;;;;;;;;;;;(a -> Type)
(declare-fun Kind_arrow_136 (Type) Kind)
;;;;;;;;;;;;;;;;Kind_arrow_136 interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (HasKind @a0
(Kind_arrow_136 @a1))
(and (is-Kind_arrow (PreKind @a0))
(forall ((@x2 Term))
 (! (implies (HasType @x2
@a1)
(HasKind (ApplyTE @a0
@x2)
Kind_type))
  
:pattern ((ApplyTE @a0
@x2))))))
  
:pattern ((HasKind @a0
(Kind_arrow_136 @a1))))))
(declare-fun Prims.Forall (Type Type) Type)
(declare-fun Prims.Forall@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 137
(Type_constr_id Prims.Forall@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.Forall@tok
@a0)
@a1)
(Prims.Forall @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.Forall@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;(x:a -> Tot (p x))
(declare-fun Typ_fun_139 (Type Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_139 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_139 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_139 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u0
@x1
(Typ_fun_139 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_139 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_139 interpretation
(assert (forall ((@x0 Term) (@a1 Type) (@a2 Type))
 (! (iff (HasTypeZ @x0
(Typ_fun_139 @a1
@a2))
(forall ((@x3 Term))
 (! (implies (HasType @x3
@a2)
(HasType (ApplyEE @x0
@x3)
(ApplyTE @a1
@x3)))
  
:pattern ((ApplyEE @x0
@x3)))))
  
:pattern ((HasTypeZ @x0
(Typ_fun_139 @a1
@a2))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0)))
(= (Prims.Forall @a0
@a1)
(Typ_fun_139 @a1
@a0)))
  
:pattern ((Prims.Forall @a0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0)))
(HasKind (Prims.Forall @a0
@a1)
Kind_type))
  
:pattern ((Prims.Forall @a0
@a1)))))
;;;;;;;;;;;;;;;;forall interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (forall ((@x2 Term))
 (! (implies (HasTypeZ @x2
@a0)
(Valid (ApplyTE @a1
@x2)))
  
:pattern ((HasTypeZ @x2
@a0))))
(Valid (Prims.Forall @a0
@a1)))
  
:pattern ((Valid (Prims.Forall @a0
@a1))))))

; </end encoding Prims.Forall>

; encoding sigelt Prims.DTuple2, Prims.MkDTuple2

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.DTuple2 (Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple2@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple2@a1 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.DTuple2@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkDTuple2 (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple2_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple2_b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple2__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple2__2 (Term) Term)
;;;;;;;;;;;;;;;;(_1:a -> _2:(b _1) -> Tot (DTuple2 a b))
(declare-fun Typ_fun_168 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkDTuple2
(declare-fun Prims.MkDTuple2@tok () Term)

; <Start encoding Prims.DTuple2>

; <start constructor Prims.DTuple2>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 157
(Type_constr_id (Prims.DTuple2 @a0
@a1)))
  
:pattern ((Prims.DTuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.DTuple2@a0 (Prims.DTuple2 @a0
@a1))
@a0)
  
:pattern ((Prims.DTuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.DTuple2@a1 (Prims.DTuple2 @a0
@a1))
@a1)
  
:pattern ((Prims.DTuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.DTuple2 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
157)
(= @a0
(Prims.DTuple2 (Prims.DTuple2@a0 @a0)
(Prims.DTuple2@a1 @a0)))))

; </end constructor Prims.DTuple2>
;;;;;;;;;;;;;;;;fresh token
(assert (= 158
(Type_constr_id Prims.DTuple2@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.DTuple2@tok
@a0)
@a1)
(Prims.DTuple2 @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.DTuple2@tok
@a0)
@a1))

:pattern ((Prims.DTuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.DTuple2@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0)))
(HasKind (Prims.DTuple2 @a0
@a1)
Kind_type))
  
:pattern ((Prims.DTuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.DTuple2 @a2
@a3))
(= (Prims.DTuple2 @a2
@a3)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.DTuple2 @a2
@a3))))))

; </end encoding Prims.DTuple2>

; <Start encoding Prims.MkDTuple2>

; <start constructor Prims.MkDTuple2>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= 165
(Term_constr_id (Prims.MkDTuple2 @a0
@a1
@x2
@x3)))
  
:pattern ((Prims.MkDTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkDTuple2_a (Prims.MkDTuple2 @a0
@a1
@x2
@x3))
@a0)
  
:pattern ((Prims.MkDTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkDTuple2_b (Prims.MkDTuple2 @a0
@a1
@x2
@x3))
@a1)
  
:pattern ((Prims.MkDTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkDTuple2__1 (Prims.MkDTuple2 @a0
@a1
@x2
@x3))
@x2)
  
:pattern ((Prims.MkDTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkDTuple2__2 (Prims.MkDTuple2 @a0
@a1
@x2
@x3))
@x3)
  
:pattern ((Prims.MkDTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkDTuple2 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
165)
(= @x0
(Prims.MkDTuple2 (Prims.MkDTuple2_a @x0)
(Prims.MkDTuple2_b @x0)
(Prims.MkDTuple2__1 @x0)
(Prims.MkDTuple2__2 @x0)))))

; </end constructor Prims.MkDTuple2>
;;;;;;;;;;;;;;;;Typ_fun_168 kinding
(assert (HasKind Typ_fun_168
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_168)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_168)))))
;;;;;;;;;;;;;;;;Typ_fun_168 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_168)
(forall ((@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasType @x3
@a1)
(HasType @x4
(ApplyTE @a2
@x3)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
(Prims.DTuple2 @a1
@a2)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_168)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 171
(Term_constr_id Prims.MkDTuple2@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkDTuple2@tok
Typ_fun_168))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET Prims.MkDTuple2@tok
@a0)
@a1)
@x2)
@x3)
(Prims.MkDTuple2 @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET Prims.MkDTuple2@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasTypeFuel @u0
@x3
@a1)
(HasTypeFuel @u0
@x4
(ApplyTE @a2
@x3)))
(HasTypeFuel @u0
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)
(Prims.DTuple2 @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)
(Prims.DTuple2 @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)
(Prims.DTuple2 @a5
@a6))
(and (= @a2
@a6)
(= @a1
@a5)
(HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasTypeFuel @u0
@x3
@a1)
(HasTypeFuel @u0
@x4
(ApplyTE @a2
@x3))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)
(Prims.DTuple2 @a5
@a6))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)
(Prims.DTuple2 @a5
@a6))
(and (Valid (Precedes @x3
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)))
(Valid (Precedes @x4
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkDTuple2 @a1
@a2
@x3
@x4)
(Prims.DTuple2 @a5
@a6))))))

; </end encoding Prims.MkDTuple2>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.DTuple2 @a2
@a3))
(and (is-Prims.MkDTuple2 @x1)
(= @a2
(Prims.MkDTuple2_a @x1))
(= @a3
(Prims.MkDTuple2_b @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.DTuple2 @a2
@a3))))))

; </end encoding >

; encoding sigelt Prims.is_MkDTuple2

; <Start encoding Prims.is_MkDTuple2>
(declare-fun Prims.is_MkDTuple2 (Type Type Term) Term)
;;;;;;;;;;;;;;;;((DTuple2 a b) -> Tot bool)
(declare-fun Typ_fun_176 () Type)
;;;;;;;;;;;;;;;;Typ_fun_176 kinding
(assert (HasKind Typ_fun_176
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_176)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_176)))))
;;;;;;;;;;;;;;;;Typ_fun_176 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_176)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasType @x3
(Prims.DTuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_176)))))
(declare-fun Prims.is_MkDTuple2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 178
(Term_constr_id Prims.is_MkDTuple2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_MkDTuple2@tok
@a0)
@a1)
@x2)
(Prims.is_MkDTuple2 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_MkDTuple2@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkDTuple2@tok
Typ_fun_176))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.is_MkDTuple2 @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_MkDTuple2 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_MkDTuple2 @a0
@a1
@x2)
(BoxBool (is-Prims.MkDTuple2 @x2)))
  
:pattern ((Prims.is_MkDTuple2 @a0
@a1
@x2)))))

; </end encoding Prims.is_MkDTuple2>

; encoding sigelt Prims.MkDTuple2.a

; <Start encoding Prims.MkDTuple2.a>
(declare-fun Prims.MkDTuple2.a (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple2.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 182
(Type_constr_id Prims.MkDTuple2.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.MkDTuple2.a@tok
@a0)
@a1)
@x2)
(Prims.MkDTuple2.a @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.MkDTuple2.a@tok
@a0)
@a1)
@x2))

:pattern ((Prims.MkDTuple2.a @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple2.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasKind (Prims.MkDTuple2.a @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.MkDTuple2.a @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkDTuple2.a @a0
@a1
@x2)
(Prims.MkDTuple2_a @x2))
  
:pattern ((Prims.MkDTuple2.a @a0
@a1
@x2)))))

; </end encoding Prims.MkDTuple2.a>

; encoding sigelt Prims.MkDTuple2.b

; <Start encoding Prims.MkDTuple2.b>
(declare-fun Prims.MkDTuple2.b (Type Type Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple2.b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 186
(Type_constr_id Prims.MkDTuple2.b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT Prims.MkDTuple2.b@tok
@a0)
@a1)
@x2)
@x3)
(Prims.MkDTuple2.b @a0
@a1
@x2
@x3))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT Prims.MkDTuple2.b@tok
@a0)
@a1)
@x2)
@x3))

:pattern ((Prims.MkDTuple2.b @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple2.b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1))
(HasType @x3
(Prims.MkDTuple2.a @a0
@a1
@x2)))
(HasKind (Prims.MkDTuple2.b @a0
@a1
@x2
@x3)
Kind_type))
  
:pattern ((Prims.MkDTuple2.b @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkDTuple2.b @a0
@a1
@x2
@x3)
(ApplyTE (Prims.MkDTuple2_b @x2)
@x3))
  
:pattern ((Prims.MkDTuple2.b @a0
@a1
@x2
@x3)))))

; </end encoding Prims.MkDTuple2.b>

; encoding sigelt Prims.MkDTuple2._1

; <Start encoding Prims.MkDTuple2._1>
(declare-fun Prims.MkDTuple2._1 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple2 a b) -> Tot (a projectee))
(declare-fun Typ_fun_191 () Type)
;;;;;;;;;;;;;;;;Typ_fun_191 kinding
(assert (HasKind Typ_fun_191
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_191)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_191)))))
;;;;;;;;;;;;;;;;Typ_fun_191 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_191)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasType @x3
(Prims.DTuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(Prims.MkDTuple2.a @a1
@a2
@x3)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_191)))))
(declare-fun Prims.MkDTuple2._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 193
(Term_constr_id Prims.MkDTuple2._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.MkDTuple2._1@tok
@a0)
@a1)
@x2)
(Prims.MkDTuple2._1 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.MkDTuple2._1@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple2._1@tok
Typ_fun_191))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.MkDTuple2._1 @a0
@a1
@x2)
(Prims.MkDTuple2.a @a0
@a1
@x2)))
  
:pattern ((Prims.MkDTuple2._1 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkDTuple2._1 @a0
@a1
@x2)
(Prims.MkDTuple2__1 @x2))
  
:pattern ((Prims.MkDTuple2._1 @a0
@a1
@x2)))))

; </end encoding Prims.MkDTuple2._1>

; encoding sigelt Prims.MkDTuple2._2

; <Start encoding Prims.MkDTuple2._2>
(declare-fun Prims.MkDTuple2._2 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple2 a b) -> Tot (b projectee (_1 projectee)))
(declare-fun Typ_fun_198 () Type)
;;;;;;;;;;;;;;;;Typ_fun_198 kinding
(assert (HasKind Typ_fun_198
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_198)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_198)))))
;;;;;;;;;;;;;;;;Typ_fun_198 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_198)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasType @x3
(Prims.DTuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(Prims.MkDTuple2.b @a1
@a2
@x3
(Prims.MkDTuple2._1 @a1
@a2
@x3))))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_198)))))
(declare-fun Prims.MkDTuple2._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 200
(Term_constr_id Prims.MkDTuple2._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.MkDTuple2._2@tok
@a0)
@a1)
@x2)
(Prims.MkDTuple2._2 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.MkDTuple2._2@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple2._2@tok
Typ_fun_198))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.MkDTuple2._2 @a0
@a1
@x2)
(Prims.MkDTuple2.b @a0
@a1
@x2
(Prims.MkDTuple2._1 @a0
@a1
@x2))))
  
:pattern ((Prims.MkDTuple2._2 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkDTuple2._2 @a0
@a1
@x2)
(Prims.MkDTuple2__2 @x2))
  
:pattern ((Prims.MkDTuple2._2 @a0
@a1
@x2)))))

; </end encoding Prims.MkDTuple2._2>

; encoding sigelt Prims.Exists

; <Start encoding Prims.Exists>
(declare-fun Prims.Exists (Type Type) Type)
(declare-fun Prims.Exists@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 203
(Type_constr_id Prims.Exists@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.Exists@tok
@a0)
@a1)
(Prims.Exists @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.Exists@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0)))
(= (Prims.Exists @a0
@a1)
(Prims.DTuple2 @a0
@a1)))
  
:pattern ((Prims.Exists @a0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0)))
(HasKind (Prims.Exists @a0
@a1)
Kind_type))
  
:pattern ((Prims.Exists @a0
@a1)))))
;;;;;;;;;;;;;;;;exists interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (exists ((@x2 Term))
 (! (implies (HasTypeZ @x2
@a0)
(Valid (ApplyTE @a1
@x2)))
  
:pattern ((HasTypeZ @x2
@a0))))
(Valid (Prims.Exists @a0
@a1)))
  
:pattern ((Valid (Prims.Exists @a0
@a1))))))

; </end encoding Prims.Exists>

; encoding sigelt Prims.XOR

; <Start encoding Prims.XOR>
(declare-fun Prims.XOR (Type Type) Type)
(declare-fun Prims.XOR@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 204
(Type_constr_id Prims.XOR@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.XOR@tok
@a0)
@a1)
(Prims.XOR @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.XOR@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(= (Valid (Prims.XOR @a0
@a1))
(and (or (Valid @a0)
(Valid @a1))
(not (and (Valid @a0)
(Valid @a1))))))
  
:pattern ((Valid (Prims.XOR @a0
@a1))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.XOR @a0
@a1)
Kind_type))
  
:pattern ((Prims.XOR @a0
@a1)))))

; </end encoding Prims.XOR>

; encoding sigelt Prims.ITE

; <Start encoding Prims.ITE>
(declare-fun Prims.ITE (Type Type Type) Type)
(declare-fun Prims.ITE@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 205
(Type_constr_id Prims.ITE@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT Prims.ITE@tok
@a0)
@a1)
@a2)
(Prims.ITE @a0
@a1
@a2))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT Prims.ITE@tok
@a0)
@a1)
@a2)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type))
(= (Valid (Prims.ITE @a0
@a1
@a2))
(and (implies (Valid @a0)
(Valid @a1))
(implies (not (Valid @a0))
(Valid @a2)))))
  
:pattern ((Valid (Prims.ITE @a0
@a1
@a2))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type))
(HasKind (Prims.ITE @a0
@a1
@a2)
Kind_type))
  
:pattern ((Prims.ITE @a0
@a1
@a2)))))

; </end encoding Prims.ITE>

; encoding sigelt Prims.ForallTyp

; <Start encoding Prims.ForallTyp>
(declare-fun Prims.ForallTyp (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.ForallTyp@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 209
(Type_constr_id Prims.ForallTyp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.ForallTyp@tok
@a0)
(Prims.ForallTyp @a0))
  
:pattern ((ApplyTT Prims.ForallTyp@tok
@a0))

:pattern ((Prims.ForallTyp @a0)))))
;;;;;;;;;;;;;;;;(Type -> Type)
(declare-fun Kind_arrow_207 () Kind)
;;;;;;;;;;;;;;;;Kind_arrow_207 interpretation
(assert (forall ((@a0 Type))
 (! (iff (HasKind @a0
Kind_arrow_207)
(and (is-Kind_arrow (PreKind @a0))
(forall ((@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasKind (ApplyTT @a0
@a1)
Kind_type))
  
:pattern ((ApplyTT @a0
@a1))))))
  
:pattern ((HasKind @a0
Kind_arrow_207)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.ForallTyp@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_arrow_207)
(HasKind (Prims.ForallTyp @a0)
Kind_type))
  
:pattern ((Prims.ForallTyp @a0)))))

; </end encoding Prims.ForallTyp>

; encoding sigelt Prims.ExistsTyp

; <Start encoding Prims.ExistsTyp>
(declare-fun Prims.ExistsTyp (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.ExistsTyp@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 212
(Type_constr_id Prims.ExistsTyp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.ExistsTyp@tok
@a0)
(Prims.ExistsTyp @a0))
  
:pattern ((ApplyTT Prims.ExistsTyp@tok
@a0))

:pattern ((Prims.ExistsTyp @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.ExistsTyp@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_arrow_207)
(HasKind (Prims.ExistsTyp @a0)
Kind_type))
  
:pattern ((Prims.ExistsTyp @a0)))))

; </end encoding Prims.ExistsTyp>

; encoding sigelt Prims.Precedes

; <Skipped Prims.Precedes/>

; encoding sigelt Prims.PurePre

; <Skipped Prims.PurePre/>

; encoding sigelt Prims.PurePost

; <Skipped Prims.PurePost/>

; encoding sigelt Prims.PureWP

; <Skipped Prims.PureWP/>

; encoding sigelt Prims.pure_return

; <Skipped Prims.pure_return/>

; encoding sigelt Prims.pure_bind_wlp

; <Skipped Prims.pure_bind_wlp/>

; encoding sigelt Prims.pure_bind_wp

; <Skipped Prims.pure_bind_wp/>

; encoding sigelt Prims.pure_if_then_else

; <Skipped Prims.pure_if_then_else/>

; encoding sigelt Prims.pure_ite_wlp

; <Skipped Prims.pure_ite_wlp/>

; encoding sigelt Prims.pure_ite_wp

; <Skipped Prims.pure_ite_wp/>

; encoding sigelt Prims.pure_wp_binop

; <Skipped Prims.pure_wp_binop/>

; encoding sigelt Prims.pure_wp_as_type

; <Skipped Prims.pure_wp_as_type/>

; encoding sigelt Prims.pure_close_wp

; <Skipped Prims.pure_close_wp/>

; encoding sigelt Prims.pure_close_wp_t

; <Skipped Prims.pure_close_wp_t/>

; encoding sigelt Prims.pure_assert_p

; <Skipped Prims.pure_assert_p/>

; encoding sigelt Prims.pure_assume_p

; <Skipped Prims.pure_assume_p/>

; encoding sigelt Prims.pure_null_wp

; <Skipped Prims.pure_null_wp/>

; encoding sigelt Prims.pure_trivial

; <Skipped Prims.pure_trivial/>

; encoding sigelt Prims.PURE

; <Skipped Prims.PURE/>

; encoding sigelt Prims.Pure

; <Skipped Prims.Pure/>

; encoding sigelt Prims.Admit

; <Skipped Prims.Admit/>

; encoding sigelt Prims.Tot

; <Skipped Prims.Tot/>

; encoding sigelt Prims.GHOST

; <Skipped Prims.GHOST/>

; encoding sigelt 

; <Skipped />

; encoding sigelt Prims.GTot

; <Skipped Prims.GTot/>

; encoding sigelt Prims.Ghost

; <Skipped Prims.Ghost/>

; encoding sigelt Prims.unit

; <Start encoding Prims.unit>

; <start constructor Prims.unit>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.unit () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 464
(Type_constr_id Prims.unit)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.unit ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
464)
(= @a0
Prims.unit)))

; </end constructor Prims.unit>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.unit
Kind_type))
;;;;;;;;;;;;;;;;unit typing
(assert (HasType Term_unit
Prims.unit))
;;;;;;;;;;;;;;;;unit inversion
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Prims.unit)
(= @x1
Term_unit))
  
:pattern ((HasTypeFuel @u0
@x1
Prims.unit)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.unit)
(= Prims.unit
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.unit)))))

; </end encoding Prims.unit>

; encoding sigelt Prims.int

; <Start encoding Prims.int>

; <start constructor Prims.int>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.int () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 468
(Type_constr_id Prims.int)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.int ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
468)
(= @a0
Prims.int)))

; </end constructor Prims.int>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.int
Kind_type))
;;;;;;;;;;;;;;;;int inversion
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Prims.int)
(is-BoxInt @x1))
  
:pattern ((HasTypeFuel @u0
@x1
Prims.int)))))
;;;;;;;;;;;;;;;;int typing
(assert (forall ((@u0 Int))
 (! (HasType (BoxInt @u0)
Prims.int)
  
:pattern ((BoxInt @u0)))))
;;;;;;;;;;;;;;;;well-founded ordering on nat (alt)
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (implies (and (HasTypeFuel @u0
@x1
Prims.int)
(HasTypeFuel @u0
@x2
Prims.int)
(> (BoxInt_proj_0 @x1)
0)
(>= (BoxInt_proj_0 @x2)
0)
(< (BoxInt_proj_0 @x2)
(BoxInt_proj_0 @x1)))
(Valid (Precedes @x2
@x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Prims.int) (HasTypeFuel @u0
@x2
Prims.int) (Valid (Precedes @x2
@x1))))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.int)
(= Prims.int
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.int)))))

; </end encoding Prims.int>

; encoding sigelt Prims.op_AmpAmp

; <Start encoding Prims.op_AmpAmp>
(declare-fun Prims.op_AmpAmp (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_AmpAmp @x0
@x1)
(BoxBool (and (BoxBool_proj_0 @x0)
(BoxBool_proj_0 @x1))))
  
:pattern ((Prims.op_AmpAmp @x0
@x1)))))

; </end encoding Prims.op_AmpAmp>

; encoding sigelt Prims.op_BarBar

; <Start encoding Prims.op_BarBar>
(declare-fun Prims.op_BarBar (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_BarBar @x0
@x1)
(BoxBool (or (BoxBool_proj_0 @x0)
(BoxBool_proj_0 @x1))))
  
:pattern ((Prims.op_BarBar @x0
@x1)))))

; </end encoding Prims.op_BarBar>

; encoding sigelt Prims.op_Negation

; <Start encoding Prims.op_Negation>
(declare-fun Prims.op_Negation (Term) Term)
(assert (forall ((@x0 Term))
 (! (= (Prims.op_Negation @x0)
(BoxBool (not (BoxBool_proj_0 @x0))))
  
:pattern ((Prims.op_Negation @x0)))))

; </end encoding Prims.op_Negation>

; encoding sigelt Prims.op_Multiply

; <Start encoding Prims.op_Multiply>
(declare-fun Prims.op_Multiply (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Multiply @x0
@x1)
(BoxInt (* (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_Multiply @x0
@x1)))))

; </end encoding Prims.op_Multiply>

; encoding sigelt Prims.op_Subtraction

; <Start encoding Prims.op_Subtraction>
(declare-fun Prims.op_Subtraction (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Subtraction @x0
@x1)
(BoxInt (- (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_Subtraction @x0
@x1)))))

; </end encoding Prims.op_Subtraction>

; encoding sigelt Prims.op_Addition

; <Start encoding Prims.op_Addition>
(declare-fun Prims.op_Addition (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Addition @x0
@x1)
(BoxInt (+ (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_Addition @x0
@x1)))))

; </end encoding Prims.op_Addition>

; encoding sigelt Prims.op_Minus

; <Start encoding Prims.op_Minus>
(declare-fun Prims.op_Minus (Term) Term)
(assert (forall ((@x0 Term))
 (! (= (Prims.op_Minus @x0)
(BoxInt (- (BoxInt_proj_0 @x0))))
  
:pattern ((Prims.op_Minus @x0)))))

; </end encoding Prims.op_Minus>

; encoding sigelt Prims.op_LessThanOrEqual

; <Start encoding Prims.op_LessThanOrEqual>
(declare-fun Prims.op_LessThanOrEqual (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_LessThanOrEqual @x0
@x1)
(BoxBool (<= (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_LessThanOrEqual @x0
@x1)))))

; </end encoding Prims.op_LessThanOrEqual>

; encoding sigelt Prims.op_GreaterThan

; <Start encoding Prims.op_GreaterThan>
(declare-fun Prims.op_GreaterThan (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_GreaterThan @x0
@x1)
(BoxBool (> (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_GreaterThan @x0
@x1)))))

; </end encoding Prims.op_GreaterThan>

; encoding sigelt Prims.op_GreaterThanOrEqual

; <Start encoding Prims.op_GreaterThanOrEqual>
(declare-fun Prims.op_GreaterThanOrEqual (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_GreaterThanOrEqual @x0
@x1)
(BoxBool (>= (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_GreaterThanOrEqual @x0
@x1)))))

; </end encoding Prims.op_GreaterThanOrEqual>

; encoding sigelt Prims.op_LessThan

; <Start encoding Prims.op_LessThan>
(declare-fun Prims.op_LessThan (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_LessThan @x0
@x1)
(BoxBool (< (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_LessThan @x0
@x1)))))

; </end encoding Prims.op_LessThan>

; encoding sigelt Prims.op_Equality

; <Start encoding Prims.op_Equality>
(declare-fun Prims.op_Equality (Type Term Term) Term)
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (Prims.op_Equality @a0
@x1
@x2)
(BoxBool (= @x1
@x2)))
  
:pattern ((Prims.op_Equality @a0
@x1
@x2)))))

; </end encoding Prims.op_Equality>

; encoding sigelt Prims.op_disEquality

; <Start encoding Prims.op_disEquality>
(declare-fun Prims.op_disEquality (Type Term Term) Term)
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (Prims.op_disEquality @a0
@x1
@x2)
(BoxBool (not (= @x1
@x2))))
  
:pattern ((Prims.op_disEquality @a0
@x1
@x2)))))

; </end encoding Prims.op_disEquality>

; encoding sigelt Prims.int16

; <Start encoding Prims.int16>
(declare-fun Prims.int16 () Type)
(declare-fun Prims.int16@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.int16@tok
Prims.int16))
(declare-fun Typ_refine_474 () Type)
(assert (HasKind Typ_refine_474
Kind_type))
;;;;;;;;;;;;;;;;i:int{((i > (- 32769)) /\ (32768 > i))}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_474)
(and (HasTypeFuel @u0
@x1
Prims.int)
(> (BoxInt_proj_0 @x1)
(BoxInt_proj_0 (Prims.op_Minus (BoxInt 32769))))
(> (BoxInt_proj_0 (BoxInt 32768))
(BoxInt_proj_0 @x1))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_474)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.int16
Typ_refine_474))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.int16
Kind_type))

; </end encoding Prims.int16>

; encoding sigelt Prims.int32

; <Start encoding Prims.int32>
(declare-fun Prims.int32 () Type)
(declare-fun Prims.int32@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.int32@tok
Prims.int32))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.int32
Prims.int))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.int32
Kind_type))

; </end encoding Prims.int32>

; encoding sigelt Prims.int64

; <Start encoding Prims.int64>

; <start constructor Prims.int64>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.int64 () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 475
(Type_constr_id Prims.int64)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.int64 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
475)
(= @a0
Prims.int64)))

; </end constructor Prims.int64>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.int64
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.int64)
(= Prims.int64
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.int64)))))

; </end encoding Prims.int64>

; encoding sigelt Prims.uint8

; <Start encoding Prims.uint8>
(declare-fun Prims.uint8 () Type)
;;;;;;;;;;;;;;;;mapping to int; for now
(assert (= Prims.uint8
Prims.int))

; </end encoding Prims.uint8>

; encoding sigelt Prims.uint16

; <Start encoding Prims.uint16>

; <start constructor Prims.uint16>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.uint16 () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 478
(Type_constr_id Prims.uint16)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.uint16 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
478)
(= @a0
Prims.uint16)))

; </end constructor Prims.uint16>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.uint16
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.uint16)
(= Prims.uint16
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.uint16)))))

; </end encoding Prims.uint16>

; encoding sigelt Prims.uint32

; <Start encoding Prims.uint32>

; <start constructor Prims.uint32>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.uint32 () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 481
(Type_constr_id Prims.uint32)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.uint32 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
481)
(= @a0
Prims.uint32)))

; </end constructor Prims.uint32>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.uint32
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.uint32)
(= Prims.uint32
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.uint32)))))

; </end encoding Prims.uint32>

; encoding sigelt Prims.uint64

; <Start encoding Prims.uint64>

; <start constructor Prims.uint64>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.uint64 () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 484
(Type_constr_id Prims.uint64)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.uint64 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
484)
(= @a0
Prims.uint64)))

; </end constructor Prims.uint64>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.uint64
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.uint64)
(= Prims.uint64
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.uint64)))))

; </end encoding Prims.uint64>

; encoding sigelt Prims.char

; <Start encoding Prims.char>
(declare-fun Prims.char () Type)
;;;;;;;;;;;;;;;;mapping to int; for now
(assert (= Prims.char
Prims.int))

; </end encoding Prims.char>

; encoding sigelt Prims.float

; <Start encoding Prims.float>

; <start constructor Prims.float>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.float () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 487
(Type_constr_id Prims.float)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.float ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
487)
(= @a0
Prims.float)))

; </end constructor Prims.float>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.float
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.float)
(= Prims.float
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.float)))))

; </end encoding Prims.float>

; encoding sigelt Prims.string

; <Start encoding Prims.string>

; <start constructor Prims.string>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.string () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 490
(Type_constr_id Prims.string)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.string ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
490)
(= @a0
Prims.string)))

; </end constructor Prims.string>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.string
Kind_type))
;;;;;;;;;;;;;;;;string inversion
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Prims.string)
(is-BoxString @x1))
  
:pattern ((HasTypeFuel @u0
@x1
Prims.string)))))
;;;;;;;;;;;;;;;;string typing
(assert (forall ((@u0 String))
 (! (HasType (BoxString @u0)
Prims.string)
  
:pattern ((BoxString @u0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.string)
(= Prims.string
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.string)))))

; </end encoding Prims.string>

; encoding sigelt Prims.array

; <Start encoding Prims.array>

; <start constructor Prims.array>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.array (Type) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 494
(Type_constr_id (Prims.array @a0)))
  
:pattern ((Prims.array @a0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.array@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.array@a0 (Prims.array @a0))
@a0)
  
:pattern ((Prims.array @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.array ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
494)
(= @a0
(Prims.array (Prims.array@a0 @a0)))))

; </end constructor Prims.array>
;;;;;;;;;;;;;;;;token
(declare-fun Prims.array@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 495
(Type_constr_id Prims.array@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.array@tok
@a0)
(Prims.array @a0))
  
:pattern ((ApplyTT Prims.array@tok
@a0))

:pattern ((Prims.array @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.array@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (Prims.array @a0)
Kind_type))
  
:pattern ((Prims.array @a0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.array @a2))
(= (Prims.array @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.array @a2))))))

; </end encoding Prims.array>

; encoding sigelt Prims.strcat

; <Start encoding Prims.strcat>
(declare-fun Prims.strcat (Term Term) Term)
;;;;;;;;;;;;;;;;(string -> string -> Tot string)
(declare-fun Typ_fun_499 () Type)
;;;;;;;;;;;;;;;;Typ_fun_499 kinding
(assert (HasKind Typ_fun_499
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_499)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_499)))))
;;;;;;;;;;;;;;;;Typ_fun_499 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_499)
(forall ((@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x1
Prims.string)
(HasType @x2
Prims.string))
(HasType (ApplyEE (ApplyEE @x0
@x1)
@x2)
Prims.string))
  
:pattern ((ApplyEE (ApplyEE @x0
@x1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_499)))))
(declare-fun Prims.strcat@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 501
(Term_constr_id Prims.strcat@tok)))
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (ApplyEE (ApplyEE Prims.strcat@tok
@x0)
@x1)
(Prims.strcat @x0
@x1))
  
:pattern ((ApplyEE (ApplyEE Prims.strcat@tok
@x0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.strcat@tok
Typ_fun_499))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
Prims.string)
(HasType @x1
Prims.string))
(HasType (Prims.strcat @x0
@x1)
Prims.string))
  
:pattern ((Prims.strcat @x0
@x1)))))

; </end encoding Prims.strcat>

; encoding sigelt Prims.LBL

; <Start encoding Prims.LBL>
(declare-fun Prims.LBL (Term Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.LBL@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 503
(Type_constr_id Prims.LBL@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term) (@a1 Type))
 (! (= (ApplyTT (ApplyTE Prims.LBL@tok
@x0)
@a1)
(Prims.LBL @x0
@a1))
  
:pattern ((ApplyTT (ApplyTE Prims.LBL@tok
@x0)
@a1))

:pattern ((Prims.LBL @x0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.LBL@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@x0 Term) (@a1 Type))
 (! (implies (and (HasType @x0
Prims.string)
(HasKind @a1
Kind_type))
(HasKind (Prims.LBL @x0
@a1)
Kind_type))
  
:pattern ((Prims.LBL @x0
@a1)))))

; </end encoding Prims.LBL>

; encoding sigelt Prims.exn

; <Start encoding Prims.exn>

; <start constructor Prims.exn>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.exn () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 504
(Type_constr_id Prims.exn)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.exn ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
504)
(= @a0
Prims.exn)))

; </end constructor Prims.exn>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.exn
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.exn)
(= Prims.exn
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.exn)))))

; </end encoding Prims.exn>

; encoding sigelt Prims.HashMultiMap

; <Start encoding Prims.HashMultiMap>

; <start constructor Prims.HashMultiMap>
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.HashMultiMap (Type Type) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 507
(Type_constr_id (Prims.HashMultiMap @a0
@a1)))
  
:pattern ((Prims.HashMultiMap @a0
@a1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.HashMultiMap@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.HashMultiMap@a0 (Prims.HashMultiMap @a0
@a1))
@a0)
  
:pattern ((Prims.HashMultiMap @a0
@a1)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.HashMultiMap@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.HashMultiMap@a1 (Prims.HashMultiMap @a0
@a1))
@a1)
  
:pattern ((Prims.HashMultiMap @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.HashMultiMap ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
507)
(= @a0
(Prims.HashMultiMap (Prims.HashMultiMap@a0 @a0)
(Prims.HashMultiMap@a1 @a0)))))

; </end constructor Prims.HashMultiMap>
;;;;;;;;;;;;;;;;token
(declare-fun Prims.HashMultiMap@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 508
(Type_constr_id Prims.HashMultiMap@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.HashMultiMap@tok
@a0)
@a1)
(Prims.HashMultiMap @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.HashMultiMap@tok
@a0)
@a1))

:pattern ((Prims.HashMultiMap @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.HashMultiMap@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.HashMultiMap @a0
@a1)
Kind_type))
  
:pattern ((Prims.HashMultiMap @a0
@a1)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.HashMultiMap @a2
@a3))
(= (Prims.HashMultiMap @a2
@a3)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.HashMultiMap @a2
@a3))))))

; </end encoding Prims.HashMultiMap>

; encoding sigelt Prims.byte

; <Start encoding Prims.byte>
(declare-fun Prims.byte () Type)
(declare-fun Prims.byte@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.byte@tok
Prims.byte))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.byte
Prims.uint8))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.byte
Kind_type))

; </end encoding Prims.byte>

; encoding sigelt Prims.double

; <Start encoding Prims.double>
(declare-fun Prims.double () Type)
(declare-fun Prims.double@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.double@tok
Prims.double))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.double
Prims.float))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.double
Kind_type))

; </end encoding Prims.double>

; encoding sigelt Prims.list, Prims.Nil, Prims.Cons

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.list (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.list@a0 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.list@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Nil (Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Nil_a (Term) Type)
;;;;;;;;;;;;;;;;( -> Tot (list a))
(declare-fun Typ_fun_536 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Nil
(declare-fun Prims.Nil@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Cons (Type Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Cons_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Cons_hd (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Cons_tl (Term) Term)
;;;;;;;;;;;;;;;;(hd:a -> tl:(list a) -> Tot (list a))
(declare-fun Typ_fun_542 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Cons
(declare-fun Prims.Cons@tok () Term)

; <Start encoding Prims.list>

; <start constructor Prims.list>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 527
(Type_constr_id (Prims.list @a0)))
  
:pattern ((Prims.list @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.list@a0 (Prims.list @a0))
@a0)
  
:pattern ((Prims.list @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.list ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
527)
(= @a0
(Prims.list (Prims.list@a0 @a0)))))

; </end constructor Prims.list>
;;;;;;;;;;;;;;;;fresh token
(assert (= 528
(Type_constr_id Prims.list@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.list@tok
@a0)
(Prims.list @a0))
  
:pattern ((ApplyTT Prims.list@tok
@a0))

:pattern ((Prims.list @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.list@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (Prims.list @a0)
Kind_type))
  
:pattern ((Prims.list @a0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.list @a2))
(= (Prims.list @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.list @a2))))))

; </end encoding Prims.list>

; <Start encoding Prims.Nil>

; <start constructor Prims.Nil>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 534
(Term_constr_id (Prims.Nil @a0)))
  
:pattern ((Prims.Nil @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.Nil_a (Prims.Nil @a0))
@a0)
  
:pattern ((Prims.Nil @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Nil ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
534)
(= @x0
(Prims.Nil (Prims.Nil_a @x0)))))

; </end constructor Prims.Nil>
;;;;;;;;;;;;;;;;Typ_fun_536 kinding
(assert (HasKind Typ_fun_536
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_536)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_536)))))
;;;;;;;;;;;;;;;;Typ_fun_536 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_536)
(forall ((@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasType (ApplyET @x0
@a1)
(Prims.list @a1)))
  
:pattern ((ApplyET @x0
@a1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_536)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 538
(Term_constr_id Prims.Nil@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Nil@tok
Typ_fun_536))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.Nil@tok
@a0)
(Prims.Nil @a0))
  
:pattern ((ApplyET Prims.Nil@tok
@a0)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasTypeFuel @u0
(Prims.Nil @a1)
(Prims.list @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.Nil @a1)
(Prims.list @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Nil @a1)
(Prims.list @a2))
(and (= @a1
@a2)
(HasKind @a1
Kind_type)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Nil @a1)
(Prims.list @a2))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.Nil>

; <Start encoding Prims.Cons>

; <start constructor Prims.Cons>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= 540
(Term_constr_id (Prims.Cons @a0
@x1
@x2)))
  
:pattern ((Prims.Cons @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (Prims.Cons_a (Prims.Cons @a0
@x1
@x2))
@a0)
  
:pattern ((Prims.Cons @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (Prims.Cons_hd (Prims.Cons @a0
@x1
@x2))
@x1)
  
:pattern ((Prims.Cons @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (Prims.Cons_tl (Prims.Cons @a0
@x1
@x2))
@x2)
  
:pattern ((Prims.Cons @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Cons ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
540)
(= @x0
(Prims.Cons (Prims.Cons_a @x0)
(Prims.Cons_hd @x0)
(Prims.Cons_tl @x0)))))

; </end constructor Prims.Cons>
;;;;;;;;;;;;;;;;Typ_fun_542 kinding
(assert (HasKind Typ_fun_542
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_542)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_542)))))
;;;;;;;;;;;;;;;;Typ_fun_542 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_542)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1)
(HasType @x3
(Prims.list @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
(Prims.list @a1)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_542)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 544
(Term_constr_id Prims.Cons@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Cons@tok
Typ_fun_542))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET Prims.Cons@tok
@a0)
@x1)
@x2)
(Prims.Cons @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET Prims.Cons@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1)
(HasTypeFuel @u0
@x3
(Prims.list @a1)))
(HasTypeFuel @u0
(Prims.Cons @a1
@x2
@x3)
(Prims.list @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.Cons @a1
@x2
@x3)
(Prims.list @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Cons @a1
@x2
@x3)
(Prims.list @a4))
(and (= @a1
@a4)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1)
(HasTypeFuel @u0
@x3
(Prims.list @a1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Cons @a1
@x2
@x3)
(Prims.list @a4))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Cons @a1
@x2
@x3)
(Prims.list @a4))
(and (Valid (Precedes @x2
(Prims.Cons @a1
@x2
@x3)))
(Valid (Precedes @x3
(Prims.Cons @a1
@x2
@x3)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Cons @a1
@x2
@x3)
(Prims.list @a4))))))

; </end encoding Prims.Cons>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.list @a2))
(or (and (is-Prims.Nil @x1)
(= @a2
(Prims.Nil_a @x1)))
(and (is-Prims.Cons @x1)
(= @a2
(Prims.Cons_a @x1)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.list @a2))))))

; </end encoding >

; encoding sigelt Prims.is_Nil

; <Start encoding Prims.is_Nil>
(declare-fun Prims.is_Nil (Type Term) Term)
;;;;;;;;;;;;;;;;((list a) -> Tot bool)
(declare-fun Typ_fun_546 () Type)
;;;;;;;;;;;;;;;;Typ_fun_546 kinding
(assert (HasKind Typ_fun_546
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_546)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_546)))))
;;;;;;;;;;;;;;;;Typ_fun_546 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_546)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Prims.list @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_546)))))
(declare-fun Prims.is_Nil@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 548
(Term_constr_id Prims.is_Nil@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_Nil@tok
@a0)
@x1)
(Prims.is_Nil @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_Nil@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Nil@tok
Typ_fun_546))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.list @a0)))
(HasType (Prims.is_Nil @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_Nil @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_Nil @a0
@x1)
(BoxBool (is-Prims.Nil @x1)))
  
:pattern ((Prims.is_Nil @a0
@x1)))))

; </end encoding Prims.is_Nil>

; encoding sigelt Prims.is_Cons

; <Start encoding Prims.is_Cons>
(declare-fun Prims.is_Cons (Type Term) Term)
(declare-fun Prims.is_Cons@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 550
(Term_constr_id Prims.is_Cons@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_Cons@tok
@a0)
@x1)
(Prims.is_Cons @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_Cons@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Cons@tok
Typ_fun_546))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.list @a0)))
(HasType (Prims.is_Cons @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_Cons @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_Cons @a0
@x1)
(BoxBool (is-Prims.Cons @x1)))
  
:pattern ((Prims.is_Cons @a0
@x1)))))

; </end encoding Prims.is_Cons>

; encoding sigelt Prims.Cons.hd

; <Start encoding Prims.Cons.hd>
(declare-fun Typ_refine_552 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_552 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_552 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_143:(list a){(is_Cons _0_143)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_552 @a2))
(and (HasTypeFuel @u0
@x1
(Prims.list @a2))
(BoxBool_proj_0 (Prims.is_Cons @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_552 @a2))))))
(declare-fun Prims.Cons.hd (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_143:(list a){(is_Cons _0_143)} -> Tot a)
(declare-fun Typ_fun_555 () Type)
;;;;;;;;;;;;;;;;Typ_fun_555 kinding
(assert (HasKind Typ_fun_555
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_555)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_555)))))
;;;;;;;;;;;;;;;;Typ_fun_555 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_555)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_552 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
@a1))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_555)))))
(declare-fun Prims.Cons.hd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 557
(Term_constr_id Prims.Cons.hd@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.Cons.hd@tok
@a0)
@x1)
(Prims.Cons.hd @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.Cons.hd@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Cons.hd@tok
Typ_fun_555))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_552 @a0)))
(HasType (Prims.Cons.hd @a0
@x1)
@a0))
  
:pattern ((Prims.Cons.hd @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Cons.hd @a0
@x1)
(Prims.Cons_hd @x1))
  
:pattern ((Prims.Cons.hd @a0
@x1)))))

; </end encoding Prims.Cons.hd>

; encoding sigelt Prims.Cons.tl

; <Start encoding Prims.Cons.tl>
(declare-fun Prims.Cons.tl (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_143:(list a){(is_Cons _0_143)} -> Tot (list a))
(declare-fun Typ_fun_561 () Type)
;;;;;;;;;;;;;;;;Typ_fun_561 kinding
(assert (HasKind Typ_fun_561
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_561)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_561)))))
;;;;;;;;;;;;;;;;Typ_fun_561 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_561)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_552 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(Prims.list @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_561)))))
(declare-fun Prims.Cons.tl@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 563
(Term_constr_id Prims.Cons.tl@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.Cons.tl@tok
@a0)
@x1)
(Prims.Cons.tl @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.Cons.tl@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Cons.tl@tok
Typ_fun_561))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_552 @a0)))
(HasType (Prims.Cons.tl @a0
@x1)
(Prims.list @a0)))
  
:pattern ((Prims.Cons.tl @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Cons.tl @a0
@x1)
(Prims.Cons_tl @x1))
  
:pattern ((Prims.Cons.tl @a0
@x1)))))

; </end encoding Prims.Cons.tl>

; encoding sigelt Prims.pattern, Prims.SMTPat, Prims.SMTPatT, Prims.SMTPatOr

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.pattern () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.SMTPat (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.SMTPat_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.SMTPat__1 (Term) Term)
;;;;;;;;;;;;;;;;(_1:a -> Tot pattern)
(declare-fun Typ_fun_593 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: SMTPat
(declare-fun Prims.SMTPat@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.SMTPatT (Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.SMTPatT_a (Term) Type)
;;;;;;;;;;;;;;;;(a:Type -> Tot pattern)
(declare-fun Typ_fun_599 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: SMTPatT
(declare-fun Prims.SMTPatT@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.SMTPatOr (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.SMTPatOr__0 (Term) Term)
;;;;;;;;;;;;;;;;(_0:(list (list pattern)) -> Tot pattern)
(declare-fun Typ_fun_605 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: SMTPatOr
(declare-fun Prims.SMTPatOr@tok () Term)

; <Start encoding Prims.pattern>

; <start constructor Prims.pattern>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 585
(Type_constr_id Prims.pattern)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.pattern ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
585)
(= @a0
Prims.pattern)))

; </end constructor Prims.pattern>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.pattern
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.pattern)
(= Prims.pattern
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.pattern)))))

; </end encoding Prims.pattern>

; <Start encoding Prims.SMTPat>

; <start constructor Prims.SMTPat>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 591
(Term_constr_id (Prims.SMTPat @a0
@x1)))
  
:pattern ((Prims.SMTPat @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.SMTPat_a (Prims.SMTPat @a0
@x1))
@a0)
  
:pattern ((Prims.SMTPat @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.SMTPat__1 (Prims.SMTPat @a0
@x1))
@x1)
  
:pattern ((Prims.SMTPat @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.SMTPat ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
591)
(= @x0
(Prims.SMTPat (Prims.SMTPat_a @x0)
(Prims.SMTPat__1 @x0)))))

; </end constructor Prims.SMTPat>
;;;;;;;;;;;;;;;;Typ_fun_593 kinding
(assert (HasKind Typ_fun_593
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_593)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_593)))))
;;;;;;;;;;;;;;;;Typ_fun_593 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_593)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.pattern))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_593)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 595
(Term_constr_id Prims.SMTPat@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.SMTPat@tok
Typ_fun_593))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.SMTPat@tok
@a0)
@x1)
(Prims.SMTPat @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.SMTPat@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1))
(HasTypeFuel @u0
(Prims.SMTPat @a1
@x2)
Prims.pattern))
  
:pattern ((HasTypeFuel @u0
(Prims.SMTPat @a1
@x2)
Prims.pattern)))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.SMTPat @a1
@x2)
Prims.pattern)
(and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.SMTPat @a1
@x2)
Prims.pattern)))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.SMTPat @a1
@x2)
Prims.pattern)
(Valid (Precedes @x2
(Prims.SMTPat @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.SMTPat @a1
@x2)
Prims.pattern)))))

; </end encoding Prims.SMTPat>

; <Start encoding Prims.SMTPatT>

; <start constructor Prims.SMTPatT>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 597
(Term_constr_id (Prims.SMTPatT @a0)))
  
:pattern ((Prims.SMTPatT @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.SMTPatT_a (Prims.SMTPatT @a0))
@a0)
  
:pattern ((Prims.SMTPatT @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.SMTPatT ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
597)
(= @x0
(Prims.SMTPatT (Prims.SMTPatT_a @x0)))))

; </end constructor Prims.SMTPatT>
;;;;;;;;;;;;;;;;Typ_fun_599 kinding
(assert (HasKind Typ_fun_599
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_599)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_599)))))
;;;;;;;;;;;;;;;;Typ_fun_599 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_599)
(forall ((@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasType (ApplyET @x0
@a1)
Prims.pattern))
  
:pattern ((ApplyET @x0
@a1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_599)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 601
(Term_constr_id Prims.SMTPatT@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.SMTPatT@tok
Typ_fun_599))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.SMTPatT@tok
@a0)
(Prims.SMTPatT @a0))
  
:pattern ((ApplyET Prims.SMTPatT@tok
@a0)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasTypeFuel @u0
(Prims.SMTPatT @a1)
Prims.pattern))
  
:pattern ((HasTypeFuel @u0
(Prims.SMTPatT @a1)
Prims.pattern)))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.SMTPatT @a1)
Prims.pattern)
(HasKind @a1
Kind_type))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.SMTPatT @a1)
Prims.pattern)))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.SMTPatT>

; <Start encoding Prims.SMTPatOr>

; <start constructor Prims.SMTPatOr>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@x0 Term))
 (! (= 603
(Term_constr_id (Prims.SMTPatOr @x0)))
  
:pattern ((Prims.SMTPatOr @x0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPatOr__0 (Prims.SMTPatOr @x0))
@x0)
  
:pattern ((Prims.SMTPatOr @x0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.SMTPatOr ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
603)
(= @x0
(Prims.SMTPatOr (Prims.SMTPatOr__0 @x0)))))

; </end constructor Prims.SMTPatOr>
;;;;;;;;;;;;;;;;Typ_fun_605 kinding
(assert (HasKind Typ_fun_605
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_605)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_605)))))
;;;;;;;;;;;;;;;;Typ_fun_605 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_605)
(forall ((@x1 Term))
 (! (implies (HasType @x1
(Prims.list (Prims.list Prims.pattern)))
(HasType (ApplyEE @x0
@x1)
Prims.pattern))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_605)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 607
(Term_constr_id Prims.SMTPatOr@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.SMTPatOr@tok
Typ_fun_605))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.SMTPatOr@tok
@x0)
(Prims.SMTPatOr @x0))
  
:pattern ((ApplyEE Prims.SMTPatOr@tok
@x0)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
(Prims.list (Prims.list Prims.pattern)))
(HasTypeFuel @u0
(Prims.SMTPatOr @x1)
Prims.pattern))
  
:pattern ((HasTypeFuel @u0
(Prims.SMTPatOr @x1)
Prims.pattern)))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.SMTPatOr @x1)
Prims.pattern)
(HasTypeFuel @u0
@x1
(Prims.list (Prims.list Prims.pattern))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.SMTPatOr @x1)
Prims.pattern)))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.SMTPatOr @x1)
Prims.pattern)
(Valid (Precedes @x1
(Prims.SMTPatOr @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.SMTPatOr @x1)
Prims.pattern)))))

; </end encoding Prims.SMTPatOr>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
Prims.pattern)
(or (is-Prims.SMTPat @x1)
(is-Prims.SMTPatT @x1)
(is-Prims.SMTPatOr @x1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
Prims.pattern)))))

; </end encoding >

; encoding sigelt Prims.is_SMTPat

; <Start encoding Prims.is_SMTPat>
(declare-fun Prims.is_SMTPat (Term) Term)
;;;;;;;;;;;;;;;;(pattern -> Tot bool)
(declare-fun Typ_fun_609 () Type)
;;;;;;;;;;;;;;;;Typ_fun_609 kinding
(assert (HasKind Typ_fun_609
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_609)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_609)))))
;;;;;;;;;;;;;;;;Typ_fun_609 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_609)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Prims.pattern)
(HasType (ApplyEE @x0
@x1)
Prims.bool))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_609)))))
(declare-fun Prims.is_SMTPat@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 611
(Term_constr_id Prims.is_SMTPat@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_SMTPat@tok
@x0)
(Prims.is_SMTPat @x0))
  
:pattern ((ApplyEE Prims.is_SMTPat@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_SMTPat@tok
Typ_fun_609))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.pattern)
(HasType (Prims.is_SMTPat @x0)
Prims.bool))
  
:pattern ((Prims.is_SMTPat @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (Prims.is_SMTPat @x0)
(BoxBool (is-Prims.SMTPat @x0)))
  
:pattern ((Prims.is_SMTPat @x0)))))

; </end encoding Prims.is_SMTPat>

; encoding sigelt Prims.is_SMTPatT

; <Start encoding Prims.is_SMTPatT>
(declare-fun Prims.is_SMTPatT (Term) Term)
(declare-fun Prims.is_SMTPatT@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 613
(Term_constr_id Prims.is_SMTPatT@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_SMTPatT@tok
@x0)
(Prims.is_SMTPatT @x0))
  
:pattern ((ApplyEE Prims.is_SMTPatT@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_SMTPatT@tok
Typ_fun_609))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.pattern)
(HasType (Prims.is_SMTPatT @x0)
Prims.bool))
  
:pattern ((Prims.is_SMTPatT @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (Prims.is_SMTPatT @x0)
(BoxBool (is-Prims.SMTPatT @x0)))
  
:pattern ((Prims.is_SMTPatT @x0)))))

; </end encoding Prims.is_SMTPatT>

; encoding sigelt Prims.is_SMTPatOr

; <Start encoding Prims.is_SMTPatOr>
(declare-fun Prims.is_SMTPatOr (Term) Term)
(declare-fun Prims.is_SMTPatOr@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 615
(Term_constr_id Prims.is_SMTPatOr@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_SMTPatOr@tok
@x0)
(Prims.is_SMTPatOr @x0))
  
:pattern ((ApplyEE Prims.is_SMTPatOr@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_SMTPatOr@tok
Typ_fun_609))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.pattern)
(HasType (Prims.is_SMTPatOr @x0)
Prims.bool))
  
:pattern ((Prims.is_SMTPatOr @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (Prims.is_SMTPatOr @x0)
(BoxBool (is-Prims.SMTPatOr @x0)))
  
:pattern ((Prims.is_SMTPatOr @x0)))))

; </end encoding Prims.is_SMTPatOr>

; encoding sigelt Prims.SMTPat.a

; <Start encoding Prims.SMTPat.a>
(declare-fun Prims.SMTPat.a (Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.SMTPat.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 619
(Type_constr_id Prims.SMTPat.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term))
 (! (= (ApplyTE Prims.SMTPat.a@tok
@x0)
(Prims.SMTPat.a @x0))
  
:pattern ((ApplyTE Prims.SMTPat.a@tok
@x0))

:pattern ((Prims.SMTPat.a @x0)))))
(declare-fun Typ_refine_617 () Type)
(assert (HasKind Typ_refine_617
Kind_type))
;;;;;;;;;;;;;;;;_0_147:pattern{(is_SMTPat _0_147)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_617)
(and (HasTypeFuel @u0
@x1
Prims.pattern)
(BoxBool_proj_0 (Prims.is_SMTPat @x1))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_617)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.SMTPat.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_617)
(HasKind (Prims.SMTPat.a @x0)
Kind_type))
  
:pattern ((Prims.SMTPat.a @x0)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPat.a @x0)
(Prims.SMTPat_a @x0))
  
:pattern ((Prims.SMTPat.a @x0)))))

; </end encoding Prims.SMTPat.a>

; encoding sigelt Prims.SMTPat._1

; <Start encoding Prims.SMTPat._1>
(declare-fun Prims.SMTPat._1 (Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_147:pattern{(is_SMTPat _0_147)} -> Tot (a projectee))
(declare-fun Typ_fun_625 () Type)
;;;;;;;;;;;;;;;;Typ_fun_625 kinding
(assert (HasKind Typ_fun_625
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_625)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_625)))))
;;;;;;;;;;;;;;;;Typ_fun_625 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_625)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Typ_refine_617)
(HasType (ApplyEE @x0
@x1)
(Prims.SMTPat.a @x1)))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_625)))))
(declare-fun Prims.SMTPat._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 627
(Term_constr_id Prims.SMTPat._1@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.SMTPat._1@tok
@x0)
(Prims.SMTPat._1 @x0))
  
:pattern ((ApplyEE Prims.SMTPat._1@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.SMTPat._1@tok
Typ_fun_625))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_617)
(HasType (Prims.SMTPat._1 @x0)
(Prims.SMTPat.a @x0)))
  
:pattern ((Prims.SMTPat._1 @x0)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPat._1 @x0)
(Prims.SMTPat__1 @x0))
  
:pattern ((Prims.SMTPat._1 @x0)))))

; </end encoding Prims.SMTPat._1>

; encoding sigelt Prims.SMTPatT.a

; <Start encoding Prims.SMTPatT.a>
(declare-fun Prims.SMTPatT.a (Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.SMTPatT.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 631
(Type_constr_id Prims.SMTPatT.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term))
 (! (= (ApplyTE Prims.SMTPatT.a@tok
@x0)
(Prims.SMTPatT.a @x0))
  
:pattern ((ApplyTE Prims.SMTPatT.a@tok
@x0))

:pattern ((Prims.SMTPatT.a @x0)))))
(declare-fun Typ_refine_629 () Type)
(assert (HasKind Typ_refine_629
Kind_type))
;;;;;;;;;;;;;;;;_0_149:pattern{(is_SMTPatT _0_149)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_629)
(and (HasTypeFuel @u0
@x1
Prims.pattern)
(BoxBool_proj_0 (Prims.is_SMTPatT @x1))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_629)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.SMTPatT.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_629)
(HasKind (Prims.SMTPatT.a @x0)
Kind_type))
  
:pattern ((Prims.SMTPatT.a @x0)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPatT.a @x0)
(Prims.SMTPatT_a @x0))
  
:pattern ((Prims.SMTPatT.a @x0)))))

; </end encoding Prims.SMTPatT.a>

; encoding sigelt Prims.SMTPatOr._0

; <Start encoding Prims.SMTPatOr._0>
(declare-fun Typ_refine_633 () Type)
(assert (HasKind Typ_refine_633
Kind_type))
;;;;;;;;;;;;;;;;_0_151:pattern{(is_SMTPatOr _0_151)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_633)
(and (HasTypeFuel @u0
@x1
Prims.pattern)
(BoxBool_proj_0 (Prims.is_SMTPatOr @x1))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_633)))))
(declare-fun Prims.SMTPatOr._0 (Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_151:pattern{(is_SMTPatOr _0_151)} -> Tot (list (list pattern)))
(declare-fun Typ_fun_636 () Type)
;;;;;;;;;;;;;;;;Typ_fun_636 kinding
(assert (HasKind Typ_fun_636
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_636)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_636)))))
;;;;;;;;;;;;;;;;Typ_fun_636 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_636)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Typ_refine_633)
(HasType (ApplyEE @x0
@x1)
(Prims.list (Prims.list Prims.pattern))))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_636)))))
(declare-fun Prims.SMTPatOr._0@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 638
(Term_constr_id Prims.SMTPatOr._0@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.SMTPatOr._0@tok
@x0)
(Prims.SMTPatOr._0 @x0))
  
:pattern ((ApplyEE Prims.SMTPatOr._0@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.SMTPatOr._0@tok
Typ_fun_636))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_633)
(HasType (Prims.SMTPatOr._0 @x0)
(Prims.list (Prims.list Prims.pattern))))
  
:pattern ((Prims.SMTPatOr._0 @x0)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPatOr._0 @x0)
(Prims.SMTPatOr__0 @x0))
  
:pattern ((Prims.SMTPatOr._0 @x0)))))

; </end encoding Prims.SMTPatOr._0>

; encoding sigelt Prims.decreases

; <Start encoding Prims.decreases>
(declare-fun Prims.decreases (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.decreases@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 640
(Type_constr_id Prims.decreases@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.decreases@tok
@a0)
@x1)
(Prims.decreases @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.decreases@tok
@a0)
@x1))

:pattern ((Prims.decreases @a0
@x1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.decreases@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(HasKind (Prims.decreases @a0
@x1)
Kind_type))
  
:pattern ((Prims.decreases @a0
@x1)))))

; </end encoding Prims.decreases>

; encoding sigelt Prims.Lemma

; <Skipped Prims.Lemma/>

; encoding sigelt Prims.option, Prims.None, Prims.Some

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.option (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.option@a0 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.option@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.None (Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.None_a (Term) Type)
;;;;;;;;;;;;;;;;( -> Tot (option a))
(declare-fun Typ_fun_666 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: None
(declare-fun Prims.None@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Some (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Some_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Some_v (Term) Term)
;;;;;;;;;;;;;;;;(v:a -> Tot (option a))
(declare-fun Typ_fun_672 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Some
(declare-fun Prims.Some@tok () Term)

; <Start encoding Prims.option>

; <start constructor Prims.option>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 657
(Type_constr_id (Prims.option @a0)))
  
:pattern ((Prims.option @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.option@a0 (Prims.option @a0))
@a0)
  
:pattern ((Prims.option @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.option ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
657)
(= @a0
(Prims.option (Prims.option@a0 @a0)))))

; </end constructor Prims.option>
;;;;;;;;;;;;;;;;fresh token
(assert (= 658
(Type_constr_id Prims.option@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.option@tok
@a0)
(Prims.option @a0))
  
:pattern ((ApplyTT Prims.option@tok
@a0))

:pattern ((Prims.option @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.option@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (Prims.option @a0)
Kind_type))
  
:pattern ((Prims.option @a0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.option @a2))
(= (Prims.option @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.option @a2))))))

; </end encoding Prims.option>

; <Start encoding Prims.None>

; <start constructor Prims.None>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 664
(Term_constr_id (Prims.None @a0)))
  
:pattern ((Prims.None @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.None_a (Prims.None @a0))
@a0)
  
:pattern ((Prims.None @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.None ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
664)
(= @x0
(Prims.None (Prims.None_a @x0)))))

; </end constructor Prims.None>
;;;;;;;;;;;;;;;;Typ_fun_666 kinding
(assert (HasKind Typ_fun_666
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_666)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_666)))))
;;;;;;;;;;;;;;;;Typ_fun_666 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_666)
(forall ((@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasType (ApplyET @x0
@a1)
(Prims.option @a1)))
  
:pattern ((ApplyET @x0
@a1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_666)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 668
(Term_constr_id Prims.None@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.None@tok
Typ_fun_666))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.None@tok
@a0)
(Prims.None @a0))
  
:pattern ((ApplyET Prims.None@tok
@a0)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasTypeFuel @u0
(Prims.None @a1)
(Prims.option @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.None @a1)
(Prims.option @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.None @a1)
(Prims.option @a2))
(and (= @a1
@a2)
(HasKind @a1
Kind_type)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.None @a1)
(Prims.option @a2))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.None>

; <Start encoding Prims.Some>

; <start constructor Prims.Some>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 670
(Term_constr_id (Prims.Some @a0
@x1)))
  
:pattern ((Prims.Some @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Some_a (Prims.Some @a0
@x1))
@a0)
  
:pattern ((Prims.Some @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Some_v (Prims.Some @a0
@x1))
@x1)
  
:pattern ((Prims.Some @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Some ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
670)
(= @x0
(Prims.Some (Prims.Some_a @x0)
(Prims.Some_v @x0)))))

; </end constructor Prims.Some>
;;;;;;;;;;;;;;;;Typ_fun_672 kinding
(assert (HasKind Typ_fun_672
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_672)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_672)))))
;;;;;;;;;;;;;;;;Typ_fun_672 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_672)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(Prims.option @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_672)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 674
(Term_constr_id Prims.Some@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Some@tok
Typ_fun_672))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.Some@tok
@a0)
@x1)
(Prims.Some @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.Some@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1))
(HasTypeFuel @u0
(Prims.Some @a1
@x2)
(Prims.option @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.Some @a1
@x2)
(Prims.option @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Some @a1
@x2)
(Prims.option @a3))
(and (= @a1
@a3)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Some @a1
@x2)
(Prims.option @a3))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Some @a1
@x2)
(Prims.option @a3))
(Valid (Precedes @x2
(Prims.Some @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Some @a1
@x2)
(Prims.option @a3))))))

; </end encoding Prims.Some>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.option @a2))
(or (and (is-Prims.None @x1)
(= @a2
(Prims.None_a @x1)))
(and (is-Prims.Some @x1)
(= @a2
(Prims.Some_a @x1)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.option @a2))))))

; </end encoding >

; encoding sigelt Prims.is_None

; <Start encoding Prims.is_None>
(declare-fun Prims.is_None (Type Term) Term)
;;;;;;;;;;;;;;;;((option a) -> Tot bool)
(declare-fun Typ_fun_676 () Type)
;;;;;;;;;;;;;;;;Typ_fun_676 kinding
(assert (HasKind Typ_fun_676
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_676)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_676)))))
;;;;;;;;;;;;;;;;Typ_fun_676 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_676)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Prims.option @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_676)))))
(declare-fun Prims.is_None@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 678
(Term_constr_id Prims.is_None@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_None@tok
@a0)
@x1)
(Prims.is_None @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_None@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_None@tok
Typ_fun_676))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.option @a0)))
(HasType (Prims.is_None @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_None @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_None @a0
@x1)
(BoxBool (is-Prims.None @x1)))
  
:pattern ((Prims.is_None @a0
@x1)))))

; </end encoding Prims.is_None>

; encoding sigelt Prims.is_Some

; <Start encoding Prims.is_Some>
(declare-fun Prims.is_Some (Type Term) Term)
(declare-fun Prims.is_Some@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 680
(Term_constr_id Prims.is_Some@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_Some@tok
@a0)
@x1)
(Prims.is_Some @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_Some@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Some@tok
Typ_fun_676))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.option @a0)))
(HasType (Prims.is_Some @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_Some @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_Some @a0
@x1)
(BoxBool (is-Prims.Some @x1)))
  
:pattern ((Prims.is_Some @a0
@x1)))))

; </end encoding Prims.is_Some>

; encoding sigelt Prims.Some.v

; <Start encoding Prims.Some.v>
(declare-fun Typ_refine_682 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_682 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_682 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_161:(option a){(is_Some _0_161)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_682 @a2))
(and (HasTypeFuel @u0
@x1
(Prims.option @a2))
(BoxBool_proj_0 (Prims.is_Some @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_682 @a2))))))
(declare-fun Prims.Some.v (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_161:(option a){(is_Some _0_161)} -> Tot a)
(declare-fun Typ_fun_685 () Type)
;;;;;;;;;;;;;;;;Typ_fun_685 kinding
(assert (HasKind Typ_fun_685
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_685)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_685)))))
;;;;;;;;;;;;;;;;Typ_fun_685 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_685)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_682 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
@a1))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_685)))))
(declare-fun Prims.Some.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 687
(Term_constr_id Prims.Some.v@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.Some.v@tok
@a0)
@x1)
(Prims.Some.v @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.Some.v@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Some.v@tok
Typ_fun_685))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_682 @a0)))
(HasType (Prims.Some.v @a0
@x1)
@a0))
  
:pattern ((Prims.Some.v @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Some.v @a0
@x1)
(Prims.Some_v @x1))
  
:pattern ((Prims.Some.v @a0
@x1)))))

; </end encoding Prims.Some.v>

; encoding sigelt Prims.either, Prims.Inl, Prims.Inr

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.either (Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.either@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.either@a1 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.either@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Inl (Type Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Inl__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Inl__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Inl_v (Term) Term)
;;;;;;;;;;;;;;;;(v:'a -> Tot (either 'a 'b))
(declare-fun Typ_fun_713 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Inl
(declare-fun Prims.Inl@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Inr (Type Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Inr__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Inr__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Inr_v (Term) Term)
;;;;;;;;;;;;;;;;(v:'b -> Tot (either 'a 'b))
(declare-fun Typ_fun_719 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Inr
(declare-fun Prims.Inr@tok () Term)

; <Start encoding Prims.either>

; <start constructor Prims.either>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 704
(Type_constr_id (Prims.either @a0
@a1)))
  
:pattern ((Prims.either @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.either@a0 (Prims.either @a0
@a1))
@a0)
  
:pattern ((Prims.either @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.either@a1 (Prims.either @a0
@a1))
@a1)
  
:pattern ((Prims.either @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.either ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
704)
(= @a0
(Prims.either (Prims.either@a0 @a0)
(Prims.either@a1 @a0)))))

; </end constructor Prims.either>
;;;;;;;;;;;;;;;;fresh token
(assert (= 705
(Type_constr_id Prims.either@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.either@tok
@a0)
@a1)
(Prims.either @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.either@tok
@a0)
@a1))

:pattern ((Prims.either @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.either@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.either @a0
@a1)
Kind_type))
  
:pattern ((Prims.either @a0
@a1)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.either @a2
@a3))
(= (Prims.either @a2
@a3)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.either @a2
@a3))))))

; </end encoding Prims.either>

; <Start encoding Prims.Inl>

; <start constructor Prims.Inl>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= 711
(Term_constr_id (Prims.Inl @a0
@a1
@x2)))
  
:pattern ((Prims.Inl @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inl__a (Prims.Inl @a0
@a1
@x2))
@a0)
  
:pattern ((Prims.Inl @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inl__b (Prims.Inl @a0
@a1
@x2))
@a1)
  
:pattern ((Prims.Inl @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inl_v (Prims.Inl @a0
@a1
@x2))
@x2)
  
:pattern ((Prims.Inl @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Inl ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
711)
(= @x0
(Prims.Inl (Prims.Inl__a @x0)
(Prims.Inl__b @x0)
(Prims.Inl_v @x0)))))

; </end constructor Prims.Inl>
;;;;;;;;;;;;;;;;Typ_fun_713 kinding
(assert (HasKind Typ_fun_713
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_713)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_713)))))
;;;;;;;;;;;;;;;;Typ_fun_713 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_713)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
@a1))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(Prims.either @a1
@a2)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_713)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 715
(Term_constr_id Prims.Inl@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Inl@tok
Typ_fun_713))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Inl@tok
@a0)
@a1)
@x2)
(Prims.Inl @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Inl@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1))
(HasTypeFuel @u0
(Prims.Inl @a1
@a2
@x3)
(Prims.either @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.Inl @a1
@a2
@x3)
(Prims.either @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Inl @a1
@a2
@x3)
(Prims.either @a4
@a5))
(and (= @a2
@a5)
(= @a1
@a4)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Inl @a1
@a2
@x3)
(Prims.either @a4
@a5))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Inl @a1
@a2
@x3)
(Prims.either @a4
@a5))
(Valid (Precedes @x3
(Prims.Inl @a1
@a2
@x3))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Inl @a1
@a2
@x3)
(Prims.either @a4
@a5))))))

; </end encoding Prims.Inl>

; <Start encoding Prims.Inr>

; <start constructor Prims.Inr>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= 717
(Term_constr_id (Prims.Inr @a0
@a1
@x2)))
  
:pattern ((Prims.Inr @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inr__a (Prims.Inr @a0
@a1
@x2))
@a0)
  
:pattern ((Prims.Inr @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inr__b (Prims.Inr @a0
@a1
@x2))
@a1)
  
:pattern ((Prims.Inr @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inr_v (Prims.Inr @a0
@a1
@x2))
@x2)
  
:pattern ((Prims.Inr @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Inr ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
717)
(= @x0
(Prims.Inr (Prims.Inr__a @x0)
(Prims.Inr__b @x0)
(Prims.Inr_v @x0)))))

; </end constructor Prims.Inr>
;;;;;;;;;;;;;;;;Typ_fun_719 kinding
(assert (HasKind Typ_fun_719
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_719)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_719)))))
;;;;;;;;;;;;;;;;Typ_fun_719 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_719)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
@a2))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(Prims.either @a1
@a2)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_719)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 721
(Term_constr_id Prims.Inr@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Inr@tok
Typ_fun_719))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Inr@tok
@a0)
@a1)
@x2)
(Prims.Inr @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Inr@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a2))
(HasTypeFuel @u0
(Prims.Inr @a1
@a2
@x3)
(Prims.either @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.Inr @a1
@a2
@x3)
(Prims.either @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Inr @a1
@a2
@x3)
(Prims.either @a4
@a5))
(and (= @a2
@a5)
(= @a1
@a4)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a2)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Inr @a1
@a2
@x3)
(Prims.either @a4
@a5))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Inr @a1
@a2
@x3)
(Prims.either @a4
@a5))
(Valid (Precedes @x3
(Prims.Inr @a1
@a2
@x3))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Inr @a1
@a2
@x3)
(Prims.either @a4
@a5))))))

; </end encoding Prims.Inr>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.either @a2
@a3))
(or (and (is-Prims.Inl @x1)
(= @a2
(Prims.Inl__a @x1))
(= @a3
(Prims.Inl__b @x1)))
(and (is-Prims.Inr @x1)
(= @a2
(Prims.Inr__a @x1))
(= @a3
(Prims.Inr__b @x1)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.either @a2
@a3))))))

; </end encoding >

; encoding sigelt Prims.is_Inl

; <Start encoding Prims.is_Inl>
(declare-fun Prims.is_Inl (Type Type Term) Term)
;;;;;;;;;;;;;;;;((either 'a 'b) -> Tot bool)
(declare-fun Typ_fun_723 () Type)
;;;;;;;;;;;;;;;;Typ_fun_723 kinding
(assert (HasKind Typ_fun_723
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_723)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_723)))))
;;;;;;;;;;;;;;;;Typ_fun_723 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_723)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.either @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_723)))))
(declare-fun Prims.is_Inl@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 725
(Term_constr_id Prims.is_Inl@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_Inl@tok
@a0)
@a1)
@x2)
(Prims.is_Inl @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_Inl@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Inl@tok
Typ_fun_723))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.either @a0
@a1)))
(HasType (Prims.is_Inl @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_Inl @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_Inl @a0
@a1
@x2)
(BoxBool (is-Prims.Inl @x2)))
  
:pattern ((Prims.is_Inl @a0
@a1
@x2)))))

; </end encoding Prims.is_Inl>

; encoding sigelt Prims.is_Inr

; <Start encoding Prims.is_Inr>
(declare-fun Prims.is_Inr (Type Type Term) Term)
(declare-fun Prims.is_Inr@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 727
(Term_constr_id Prims.is_Inr@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_Inr@tok
@a0)
@a1)
@x2)
(Prims.is_Inr @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_Inr@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Inr@tok
Typ_fun_723))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.either @a0
@a1)))
(HasType (Prims.is_Inr @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_Inr @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_Inr @a0
@a1
@x2)
(BoxBool (is-Prims.Inr @x2)))
  
:pattern ((Prims.is_Inr @a0
@a1
@x2)))))

; </end encoding Prims.is_Inr>

; encoding sigelt Prims.Inl.v

; <Start encoding Prims.Inl.v>
(declare-fun Typ_refine_729 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_729 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_729 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_167:(either 'a 'b){(is_Inl _0_167)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_729 @a2
@a3))
(and (HasTypeFuel @u0
@x1
(Prims.either @a3
@a2))
(BoxBool_proj_0 (Prims.is_Inl @a3
@a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_729 @a2
@a3))))))
(declare-fun Prims.Inl.v (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_167:(either 'a 'b){(is_Inl _0_167)} -> Tot 'a)
(declare-fun Typ_fun_732 () Type)
;;;;;;;;;;;;;;;;Typ_fun_732 kinding
(assert (HasKind Typ_fun_732
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_732)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_732)))))
;;;;;;;;;;;;;;;;Typ_fun_732 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_732)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_729 @a2
@a1)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_732)))))
(declare-fun Prims.Inl.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 734
(Term_constr_id Prims.Inl.v@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Inl.v@tok
@a0)
@a1)
@x2)
(Prims.Inl.v @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Inl.v@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Inl.v@tok
Typ_fun_732))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_729 @a1
@a0)))
(HasType (Prims.Inl.v @a0
@a1
@x2)
@a0))
  
:pattern ((Prims.Inl.v @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inl.v @a0
@a1
@x2)
(Prims.Inl_v @x2))
  
:pattern ((Prims.Inl.v @a0
@a1
@x2)))))

; </end encoding Prims.Inl.v>

; encoding sigelt Prims.Inr.v

; <Start encoding Prims.Inr.v>
(declare-fun Typ_refine_736 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_736 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_736 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_169:(either 'a 'b){(is_Inr _0_169)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_736 @a2
@a3))
(and (HasTypeFuel @u0
@x1
(Prims.either @a3
@a2))
(BoxBool_proj_0 (Prims.is_Inr @a3
@a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_736 @a2
@a3))))))
(declare-fun Prims.Inr.v (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_169:(either 'a 'b){(is_Inr _0_169)} -> Tot 'b)
(declare-fun Typ_fun_739 () Type)
;;;;;;;;;;;;;;;;Typ_fun_739 kinding
(assert (HasKind Typ_fun_739
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_739)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_739)))))
;;;;;;;;;;;;;;;;Typ_fun_739 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_739)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_736 @a2
@a1)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_739)))))
(declare-fun Prims.Inr.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 741
(Term_constr_id Prims.Inr.v@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.Inr.v@tok
@a0)
@a1)
@x2)
(Prims.Inr.v @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.Inr.v@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Inr.v@tok
Typ_fun_739))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_736 @a1
@a0)))
(HasType (Prims.Inr.v @a0
@a1
@x2)
@a1))
  
:pattern ((Prims.Inr.v @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inr.v @a0
@a1
@x2)
(Prims.Inr_v @x2))
  
:pattern ((Prims.Inr.v @a0
@a1
@x2)))))

; </end encoding Prims.Inr.v>

; encoding sigelt Prims.result, Prims.V, Prims.E, Prims.Err

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.result (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.result@a0 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.result@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.V (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.V_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.V_v (Term) Term)
;;;;;;;;;;;;;;;;(v:a -> Tot (result a))
(declare-fun Typ_fun_773 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: V
(declare-fun Prims.V@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.E (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.E_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.E_e (Term) Term)
;;;;;;;;;;;;;;;;(e:exn -> Tot (result a))
(declare-fun Typ_fun_779 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: E
(declare-fun Prims.E@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Err (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Err_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Err_msg (Term) Term)
;;;;;;;;;;;;;;;;(msg:string -> Tot (result a))
(declare-fun Typ_fun_785 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Err
(declare-fun Prims.Err@tok () Term)

; <Start encoding Prims.result>

; <start constructor Prims.result>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 764
(Type_constr_id (Prims.result @a0)))
  
:pattern ((Prims.result @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.result@a0 (Prims.result @a0))
@a0)
  
:pattern ((Prims.result @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.result ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
764)
(= @a0
(Prims.result (Prims.result@a0 @a0)))))

; </end constructor Prims.result>
;;;;;;;;;;;;;;;;fresh token
(assert (= 765
(Type_constr_id Prims.result@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.result@tok
@a0)
(Prims.result @a0))
  
:pattern ((ApplyTT Prims.result@tok
@a0))

:pattern ((Prims.result @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.result@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (Prims.result @a0)
Kind_type))
  
:pattern ((Prims.result @a0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.result @a2))
(= (Prims.result @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.result @a2))))))

; </end encoding Prims.result>

; <Start encoding Prims.V>

; <start constructor Prims.V>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 771
(Term_constr_id (Prims.V @a0
@x1)))
  
:pattern ((Prims.V @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.V_a (Prims.V @a0
@x1))
@a0)
  
:pattern ((Prims.V @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.V_v (Prims.V @a0
@x1))
@x1)
  
:pattern ((Prims.V @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.V ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
771)
(= @x0
(Prims.V (Prims.V_a @x0)
(Prims.V_v @x0)))))

; </end constructor Prims.V>
;;;;;;;;;;;;;;;;Typ_fun_773 kinding
(assert (HasKind Typ_fun_773
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_773)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_773)))))
;;;;;;;;;;;;;;;;Typ_fun_773 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_773)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(Prims.result @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_773)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 775
(Term_constr_id Prims.V@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.V@tok
Typ_fun_773))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.V@tok
@a0)
@x1)
(Prims.V @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.V@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1))
(HasTypeFuel @u0
(Prims.V @a1
@x2)
(Prims.result @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.V @a1
@x2)
(Prims.result @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.V @a1
@x2)
(Prims.result @a3))
(and (= @a1
@a3)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.V @a1
@x2)
(Prims.result @a3))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.V @a1
@x2)
(Prims.result @a3))
(Valid (Precedes @x2
(Prims.V @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.V @a1
@x2)
(Prims.result @a3))))))

; </end encoding Prims.V>

; <Start encoding Prims.E>

; <start constructor Prims.E>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 777
(Term_constr_id (Prims.E @a0
@x1)))
  
:pattern ((Prims.E @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.E_a (Prims.E @a0
@x1))
@a0)
  
:pattern ((Prims.E @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.E_e (Prims.E @a0
@x1))
@x1)
  
:pattern ((Prims.E @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.E ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
777)
(= @x0
(Prims.E (Prims.E_a @x0)
(Prims.E_e @x0)))))

; </end constructor Prims.E>
;;;;;;;;;;;;;;;;Typ_fun_779 kinding
(assert (HasKind Typ_fun_779
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_779)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_779)))))
;;;;;;;;;;;;;;;;Typ_fun_779 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_779)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
Prims.exn))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(Prims.result @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_779)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 781
(Term_constr_id Prims.E@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.E@tok
Typ_fun_779))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.E@tok
@a0)
@x1)
(Prims.E @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.E@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
Prims.exn))
(HasTypeFuel @u0
(Prims.E @a1
@x2)
(Prims.result @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.E @a1
@x2)
(Prims.result @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.E @a1
@x2)
(Prims.result @a3))
(and (= @a1
@a3)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
Prims.exn)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.E @a1
@x2)
(Prims.result @a3))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.E @a1
@x2)
(Prims.result @a3))
(Valid (Precedes @x2
(Prims.E @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.E @a1
@x2)
(Prims.result @a3))))))

; </end encoding Prims.E>

; <Start encoding Prims.Err>

; <start constructor Prims.Err>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 783
(Term_constr_id (Prims.Err @a0
@x1)))
  
:pattern ((Prims.Err @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Err_a (Prims.Err @a0
@x1))
@a0)
  
:pattern ((Prims.Err @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Err_msg (Prims.Err @a0
@x1))
@x1)
  
:pattern ((Prims.Err @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Err ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
783)
(= @x0
(Prims.Err (Prims.Err_a @x0)
(Prims.Err_msg @x0)))))

; </end constructor Prims.Err>
;;;;;;;;;;;;;;;;Typ_fun_785 kinding
(assert (HasKind Typ_fun_785
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_785)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_785)))))
;;;;;;;;;;;;;;;;Typ_fun_785 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_785)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
Prims.string))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(Prims.result @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_785)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 787
(Term_constr_id Prims.Err@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Err@tok
Typ_fun_785))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.Err@tok
@a0)
@x1)
(Prims.Err @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.Err@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
Prims.string))
(HasTypeFuel @u0
(Prims.Err @a1
@x2)
(Prims.result @a1)))
  
:pattern ((HasTypeFuel @u0
(Prims.Err @a1
@x2)
(Prims.result @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Err @a1
@x2)
(Prims.result @a3))
(and (= @a1
@a3)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
Prims.string)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Err @a1
@x2)
(Prims.result @a3))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Err @a1
@x2)
(Prims.result @a3))
(Valid (Precedes @x2
(Prims.Err @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Err @a1
@x2)
(Prims.result @a3))))))

; </end encoding Prims.Err>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.result @a2))
(or (and (is-Prims.V @x1)
(= @a2
(Prims.V_a @x1)))
(and (is-Prims.E @x1)
(= @a2
(Prims.E_a @x1)))
(and (is-Prims.Err @x1)
(= @a2
(Prims.Err_a @x1)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.result @a2))))))

; </end encoding >

; encoding sigelt Prims.is_V

; <Start encoding Prims.is_V>
(declare-fun Prims.is_V (Type Term) Term)
;;;;;;;;;;;;;;;;((result a) -> Tot bool)
(declare-fun Typ_fun_789 () Type)
;;;;;;;;;;;;;;;;Typ_fun_789 kinding
(assert (HasKind Typ_fun_789
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_789)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_789)))))
;;;;;;;;;;;;;;;;Typ_fun_789 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_789)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Prims.result @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_789)))))
(declare-fun Prims.is_V@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 791
(Term_constr_id Prims.is_V@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_V@tok
@a0)
@x1)
(Prims.is_V @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_V@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_V@tok
Typ_fun_789))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.result @a0)))
(HasType (Prims.is_V @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_V @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_V @a0
@x1)
(BoxBool (is-Prims.V @x1)))
  
:pattern ((Prims.is_V @a0
@x1)))))

; </end encoding Prims.is_V>

; encoding sigelt Prims.is_E

; <Start encoding Prims.is_E>
(declare-fun Prims.is_E (Type Term) Term)
(declare-fun Prims.is_E@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 793
(Term_constr_id Prims.is_E@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_E@tok
@a0)
@x1)
(Prims.is_E @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_E@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_E@tok
Typ_fun_789))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.result @a0)))
(HasType (Prims.is_E @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_E @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_E @a0
@x1)
(BoxBool (is-Prims.E @x1)))
  
:pattern ((Prims.is_E @a0
@x1)))))

; </end encoding Prims.is_E>

; encoding sigelt Prims.is_Err

; <Start encoding Prims.is_Err>
(declare-fun Prims.is_Err (Type Term) Term)
(declare-fun Prims.is_Err@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 795
(Term_constr_id Prims.is_Err@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.is_Err@tok
@a0)
@x1)
(Prims.is_Err @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.is_Err@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_Err@tok
Typ_fun_789))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.result @a0)))
(HasType (Prims.is_Err @a0
@x1)
Prims.bool))
  
:pattern ((Prims.is_Err @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.is_Err @a0
@x1)
(BoxBool (is-Prims.Err @x1)))
  
:pattern ((Prims.is_Err @a0
@x1)))))

; </end encoding Prims.is_Err>

; encoding sigelt Prims.V.v

; <Start encoding Prims.V.v>
(declare-fun Typ_refine_797 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_797 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_797 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_175:(result a){(is_V _0_175)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_797 @a2))
(and (HasTypeFuel @u0
@x1
(Prims.result @a2))
(BoxBool_proj_0 (Prims.is_V @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_797 @a2))))))
(declare-fun Prims.V.v (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_175:(result a){(is_V _0_175)} -> Tot a)
(declare-fun Typ_fun_800 () Type)
;;;;;;;;;;;;;;;;Typ_fun_800 kinding
(assert (HasKind Typ_fun_800
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_800)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_800)))))
;;;;;;;;;;;;;;;;Typ_fun_800 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_800)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_797 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
@a1))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_800)))))
(declare-fun Prims.V.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 802
(Term_constr_id Prims.V.v@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.V.v@tok
@a0)
@x1)
(Prims.V.v @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.V.v@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.V.v@tok
Typ_fun_800))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_797 @a0)))
(HasType (Prims.V.v @a0
@x1)
@a0))
  
:pattern ((Prims.V.v @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.V.v @a0
@x1)
(Prims.V_v @x1))
  
:pattern ((Prims.V.v @a0
@x1)))))

; </end encoding Prims.V.v>

; encoding sigelt Prims.E.e

; <Start encoding Prims.E.e>
(declare-fun Typ_refine_804 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_804 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_804 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_177:(result a){(is_E _0_177)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_804 @a2))
(and (HasTypeFuel @u0
@x1
(Prims.result @a2))
(BoxBool_proj_0 (Prims.is_E @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_804 @a2))))))
(declare-fun Prims.E.e (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_177:(result a){(is_E _0_177)} -> Tot exn)
(declare-fun Typ_fun_807 () Type)
;;;;;;;;;;;;;;;;Typ_fun_807 kinding
(assert (HasKind Typ_fun_807
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_807)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_807)))))
;;;;;;;;;;;;;;;;Typ_fun_807 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_807)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_804 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.exn))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_807)))))
(declare-fun Prims.E.e@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 809
(Term_constr_id Prims.E.e@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.E.e@tok
@a0)
@x1)
(Prims.E.e @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.E.e@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.E.e@tok
Typ_fun_807))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_804 @a0)))
(HasType (Prims.E.e @a0
@x1)
Prims.exn))
  
:pattern ((Prims.E.e @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.E.e @a0
@x1)
(Prims.E_e @x1))
  
:pattern ((Prims.E.e @a0
@x1)))))

; </end encoding Prims.E.e>

; encoding sigelt Prims.Err.msg

; <Start encoding Prims.Err.msg>
(declare-fun Typ_refine_811 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_811 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_811 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_179:(result a){(is_Err _0_179)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_811 @a2))
(and (HasTypeFuel @u0
@x1
(Prims.result @a2))
(BoxBool_proj_0 (Prims.is_Err @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_811 @a2))))))
(declare-fun Prims.Err.msg (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_179:(result a){(is_Err _0_179)} -> Tot string)
(declare-fun Typ_fun_814 () Type)
;;;;;;;;;;;;;;;;Typ_fun_814 kinding
(assert (HasKind Typ_fun_814
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_814)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_814)))))
;;;;;;;;;;;;;;;;Typ_fun_814 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_814)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_811 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.string))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_814)))))
(declare-fun Prims.Err.msg@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 816
(Term_constr_id Prims.Err.msg@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.Err.msg@tok
@a0)
@x1)
(Prims.Err.msg @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.Err.msg@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.Err.msg@tok
Typ_fun_814))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_811 @a0)))
(HasType (Prims.Err.msg @a0
@x1)
Prims.string))
  
:pattern ((Prims.Err.msg @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Err.msg @a0
@x1)
(Prims.Err_msg @x1))
  
:pattern ((Prims.Err.msg @a0
@x1)))))

; </end encoding Prims.Err.msg>

; encoding sigelt Prims.DIV

; <Skipped Prims.DIV/>

; encoding sigelt Prims.Div

; <Skipped Prims.Div/>

; encoding sigelt Prims.Dv

; <Skipped Prims.Dv/>

; encoding sigelt Prims.STPre_h

; <Skipped Prims.STPre_h/>

; encoding sigelt Prims.STPost_h

; <Skipped Prims.STPost_h/>

; encoding sigelt Prims.STWP_h

; <Skipped Prims.STWP_h/>

; encoding sigelt Prims.st_return

; <Skipped Prims.st_return/>

; encoding sigelt Prims.st_bind_wp

; <Skipped Prims.st_bind_wp/>

; encoding sigelt Prims.st_bind_wlp

; <Skipped Prims.st_bind_wlp/>

; encoding sigelt Prims.st_if_then_else

; <Skipped Prims.st_if_then_else/>

; encoding sigelt Prims.st_ite_wlp

; <Skipped Prims.st_ite_wlp/>

; encoding sigelt Prims.st_ite_wp

; <Skipped Prims.st_ite_wp/>

; encoding sigelt Prims.st_wp_binop

; <Skipped Prims.st_wp_binop/>

; encoding sigelt Prims.st_wp_as_type

; <Skipped Prims.st_wp_as_type/>

; encoding sigelt Prims.st_close_wp

; <Skipped Prims.st_close_wp/>

; encoding sigelt Prims.st_close_wp_t

; <Skipped Prims.st_close_wp_t/>

; encoding sigelt Prims.st_assert_p

; <Skipped Prims.st_assert_p/>

; encoding sigelt Prims.st_assume_p

; <Skipped Prims.st_assume_p/>

; encoding sigelt Prims.st_null_wp

; <Skipped Prims.st_null_wp/>

; encoding sigelt Prims.st_trivial

; <Skipped Prims.st_trivial/>

; encoding sigelt Prims.STATE_h

; <Skipped Prims.STATE_h/>

; encoding sigelt Prims.ExPre

; <Skipped Prims.ExPre/>

; encoding sigelt Prims.ExPost

; <Skipped Prims.ExPost/>

; encoding sigelt Prims.ExWP

; <Skipped Prims.ExWP/>

; encoding sigelt Prims.ex_return

; <Skipped Prims.ex_return/>

; encoding sigelt Prims.ex_bind_wlp

; <Skipped Prims.ex_bind_wlp/>

; encoding sigelt Prims.ex_bind_wp

; <Skipped Prims.ex_bind_wp/>

; encoding sigelt Prims.ex_if_then_else

; <Skipped Prims.ex_if_then_else/>

; encoding sigelt Prims.ex_ite_wlp

; <Skipped Prims.ex_ite_wlp/>

; encoding sigelt Prims.ex_ite_wp

; <Skipped Prims.ex_ite_wp/>

; encoding sigelt Prims.ex_wp_binop

; <Skipped Prims.ex_wp_binop/>

; encoding sigelt Prims.ex_wp_as_type

; <Skipped Prims.ex_wp_as_type/>

; encoding sigelt Prims.ex_close_wp

; <Skipped Prims.ex_close_wp/>

; encoding sigelt Prims.ex_close_wp_t

; <Skipped Prims.ex_close_wp_t/>

; encoding sigelt Prims.ex_assert_p

; <Skipped Prims.ex_assert_p/>

; encoding sigelt Prims.ex_assume_p

; <Skipped Prims.ex_assume_p/>

; encoding sigelt Prims.ex_null_wp

; <Skipped Prims.ex_null_wp/>

; encoding sigelt Prims.ex_trivial

; <Skipped Prims.ex_trivial/>

; encoding sigelt Prims.EXN

; <Skipped Prims.EXN/>

; encoding sigelt Prims.Exn

; <Skipped Prims.Exn/>

; encoding sigelt Prims.Ex

; <Skipped Prims.Ex/>

; encoding sigelt Prims.AllPre_h

; <Skipped Prims.AllPre_h/>

; encoding sigelt Prims.AllPost_h

; <Skipped Prims.AllPost_h/>

; encoding sigelt Prims.AllWP_h

; <Skipped Prims.AllWP_h/>

; encoding sigelt Prims.all_return

; <Skipped Prims.all_return/>

; encoding sigelt Prims.all_bind_wp

; <Skipped Prims.all_bind_wp/>

; encoding sigelt Prims.all_bind_wlp

; <Skipped Prims.all_bind_wlp/>

; encoding sigelt Prims.all_if_then_else

; <Skipped Prims.all_if_then_else/>

; encoding sigelt Prims.all_ite_wlp

; <Skipped Prims.all_ite_wlp/>

; encoding sigelt Prims.all_ite_wp

; <Skipped Prims.all_ite_wp/>

; encoding sigelt Prims.all_wp_binop

; <Skipped Prims.all_wp_binop/>

; encoding sigelt Prims.all_wp_as_type

; <Skipped Prims.all_wp_as_type/>

; encoding sigelt Prims.all_close_wp

; <Skipped Prims.all_close_wp/>

; encoding sigelt Prims.all_close_wp_t

; <Skipped Prims.all_close_wp_t/>

; encoding sigelt Prims.all_assert_p

; <Skipped Prims.all_assert_p/>

; encoding sigelt Prims.all_assume_p

; <Skipped Prims.all_assume_p/>

; encoding sigelt Prims.all_null_wp

; <Skipped Prims.all_null_wp/>

; encoding sigelt Prims.all_trivial

; <Skipped Prims.all_trivial/>

; encoding sigelt Prims.ALL_h

; <Skipped Prims.ALL_h/>

; encoding sigelt 

; <Skipped />

; encoding sigelt 

; <Skipped />

; encoding sigelt Prims.lex_t, Prims.LexTop, Prims.LexCons

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.lex_t () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.LexTop () Term)
;;;;;;;;;;;;;;;;data constructor proxy: LexTop
(declare-fun Prims.LexTop@tok () Term)

; <Start encoding Prims.lex_t>

; <start constructor Prims.lex_t>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 1499
(Type_constr_id Prims.lex_t)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.lex_t ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1499)
(= @a0
Prims.lex_t)))

; </end constructor Prims.lex_t>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.lex_t
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
Prims.lex_t)
(= Prims.lex_t
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
Prims.lex_t)))))

; </end encoding Prims.lex_t>

; <Start encoding Prims.LexTop>

; <start constructor Prims.LexTop>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 1505
(Term_constr_id Prims.LexTop)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.LexTop ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1505)
(= @x0
Prims.LexTop)))

; </end constructor Prims.LexTop>
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.LexTop@tok
Prims.lex_t))
;;;;;;;;;;;;;;;;equality for proxy
(assert (= Prims.LexTop@tok
Prims.LexTop))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel))
 (! (HasTypeFuel @u0
Prims.LexTop
Prims.lex_t)
  
:pattern ((HasTypeFuel @u0
Prims.LexTop
Prims.lex_t)))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert true)
;;;;;;;;;;;;;;;;lextop is top
(assert (forall ((@x0 Term))
 (! (implies (is-LexCons @x0)
(Valid (Precedes @x0
Prims.LexTop)))
  
:pattern ((Valid (Precedes @x0
Prims.LexTop))))))

; </end encoding Prims.LexTop>

; <Skipped Prims.LexCons/>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
Prims.lex_t)
(or (is-Prims.LexTop @x1)
(is-Prims.LexCons @x1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
Prims.lex_t)))))

; </end encoding >

; encoding sigelt Prims.is_LexTop

; <Start encoding Prims.is_LexTop>
(declare-fun Prims.is_LexTop (Term) Term)
;;;;;;;;;;;;;;;;(lex_t -> Tot bool)
(declare-fun Typ_fun_1508 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1508 kinding
(assert (HasKind Typ_fun_1508
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1508)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1508)))))
;;;;;;;;;;;;;;;;Typ_fun_1508 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1508)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Prims.lex_t)
(HasType (ApplyEE @x0
@x1)
Prims.bool))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1508)))))
(declare-fun Prims.is_LexTop@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1510
(Term_constr_id Prims.is_LexTop@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_LexTop@tok
@x0)
(Prims.is_LexTop @x0))
  
:pattern ((ApplyEE Prims.is_LexTop@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_LexTop@tok
Typ_fun_1508))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.lex_t)
(HasType (Prims.is_LexTop @x0)
Prims.bool))
  
:pattern ((Prims.is_LexTop @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (Prims.is_LexTop @x0)
(BoxBool (is-Prims.LexTop @x0)))
  
:pattern ((Prims.is_LexTop @x0)))))

; </end encoding Prims.is_LexTop>

; encoding sigelt Prims.is_LexCons

; <Start encoding Prims.is_LexCons>
(declare-fun Prims.is_LexCons (Term) Term)
(declare-fun Prims.is_LexCons@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1512
(Term_constr_id Prims.is_LexCons@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_LexCons@tok
@x0)
(Prims.is_LexCons @x0))
  
:pattern ((ApplyEE Prims.is_LexCons@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_LexCons@tok
Typ_fun_1508))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.lex_t)
(HasType (Prims.is_LexCons @x0)
Prims.bool))
  
:pattern ((Prims.is_LexCons @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (Prims.is_LexCons @x0)
(BoxBool (is-Prims.LexCons @x0)))
  
:pattern ((Prims.is_LexCons @x0)))))

; </end encoding Prims.is_LexCons>

; encoding sigelt Prims.Tuple2, Prims.MkTuple2

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple2 (Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple2@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple2@a1 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple2@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple2 (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple2__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple2__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple2__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple2__2 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> Tot (Tuple2 'a 'b))
(declare-fun Typ_fun_1532 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple2
(declare-fun Prims.MkTuple2@tok () Term)

; <Start encoding Prims.Tuple2>

; <start constructor Prims.Tuple2>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= 1523
(Type_constr_id (Prims.Tuple2 @a0
@a1)))
  
:pattern ((Prims.Tuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.Tuple2@a0 (Prims.Tuple2 @a0
@a1))
@a0)
  
:pattern ((Prims.Tuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.Tuple2@a1 (Prims.Tuple2 @a0
@a1))
@a1)
  
:pattern ((Prims.Tuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple2 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1523)
(= @a0
(Prims.Tuple2 (Prims.Tuple2@a0 @a0)
(Prims.Tuple2@a1 @a0)))))

; </end constructor Prims.Tuple2>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1524
(Type_constr_id Prims.Tuple2@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.Tuple2@tok
@a0)
@a1)
(Prims.Tuple2 @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.Tuple2@tok
@a0)
@a1))

:pattern ((Prims.Tuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple2@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(HasKind (Prims.Tuple2 @a0
@a1)
Kind_type))
  
:pattern ((Prims.Tuple2 @a0
@a1)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple2 @a2
@a3))
(= (Prims.Tuple2 @a2
@a3)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple2 @a2
@a3))))))

; </end encoding Prims.Tuple2>

; <Start encoding Prims.MkTuple2>

; <start constructor Prims.MkTuple2>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= 1530
(Term_constr_id (Prims.MkTuple2 @a0
@a1
@x2
@x3)))
  
:pattern ((Prims.MkTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkTuple2__a (Prims.MkTuple2 @a0
@a1
@x2
@x3))
@a0)
  
:pattern ((Prims.MkTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkTuple2__b (Prims.MkTuple2 @a0
@a1
@x2
@x3))
@a1)
  
:pattern ((Prims.MkTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkTuple2__1 (Prims.MkTuple2 @a0
@a1
@x2
@x3))
@x2)
  
:pattern ((Prims.MkTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (Prims.MkTuple2__2 (Prims.MkTuple2 @a0
@a1
@x2
@x3))
@x3)
  
:pattern ((Prims.MkTuple2 @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple2 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1530)
(= @x0
(Prims.MkTuple2 (Prims.MkTuple2__a @x0)
(Prims.MkTuple2__b @x0)
(Prims.MkTuple2__1 @x0)
(Prims.MkTuple2__2 @x0)))))

; </end constructor Prims.MkTuple2>
;;;;;;;;;;;;;;;;Typ_fun_1532 kinding
(assert (HasKind Typ_fun_1532
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1532)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1532)))))
;;;;;;;;;;;;;;;;Typ_fun_1532 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1532)
(forall ((@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
@a1)
(HasType @x4
@a2))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
(Prims.Tuple2 @a1
@a2)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1532)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1534
(Term_constr_id Prims.MkTuple2@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple2@tok
Typ_fun_1532))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET Prims.MkTuple2@tok
@a0)
@a1)
@x2)
@x3)
(Prims.MkTuple2 @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET Prims.MkTuple2@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1)
(HasTypeFuel @u0
@x4
@a2))
(HasTypeFuel @u0
(Prims.MkTuple2 @a1
@a2
@x3
@x4)
(Prims.Tuple2 @a1
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple2 @a1
@a2
@x3
@x4)
(Prims.Tuple2 @a1
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple2 @a1
@a2
@x3
@x4)
(Prims.Tuple2 @a5
@a6))
(and (= @a2
@a6)
(= @a1
@a5)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
@a1)
(HasTypeFuel @u0
@x4
@a2)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple2 @a1
@a2
@x3
@x4)
(Prims.Tuple2 @a5
@a6))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple2 @a1
@a2
@x3
@x4)
(Prims.Tuple2 @a5
@a6))
(and (Valid (Precedes @x3
(Prims.MkTuple2 @a1
@a2
@x3
@x4)))
(Valid (Precedes @x4
(Prims.MkTuple2 @a1
@a2
@x3
@x4)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple2 @a1
@a2
@x3
@x4)
(Prims.Tuple2 @a5
@a6))))))

; </end encoding Prims.MkTuple2>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple2 @a2
@a3))
(and (is-Prims.MkTuple2 @x1)
(= @a2
(Prims.MkTuple2__a @x1))
(= @a3
(Prims.MkTuple2__b @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple2 @a2
@a3))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple2

; <Start encoding Prims.is_MkTuple2>
(declare-fun Prims.is_MkTuple2 (Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple2 'a 'b) -> Tot bool)
(declare-fun Typ_fun_1536 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1536 kinding
(assert (HasKind Typ_fun_1536
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1536)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1536)))))
;;;;;;;;;;;;;;;;Typ_fun_1536 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1536)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1536)))))
(declare-fun Prims.is_MkTuple2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1538
(Term_constr_id Prims.is_MkTuple2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.is_MkTuple2@tok
@a0)
@a1)
@x2)
(Prims.is_MkTuple2 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.is_MkTuple2@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple2@tok
Typ_fun_1536))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.is_MkTuple2 @a0
@a1
@x2)
Prims.bool))
  
:pattern ((Prims.is_MkTuple2 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.is_MkTuple2 @a0
@a1
@x2)
(BoxBool (is-Prims.MkTuple2 @x2)))
  
:pattern ((Prims.is_MkTuple2 @a0
@a1
@x2)))))

; </end encoding Prims.is_MkTuple2>

; encoding sigelt Prims.MkTuple2._1

; <Start encoding Prims.MkTuple2._1>
(declare-fun Prims.MkTuple2._1 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple2 'a 'b) -> Tot 'a)
(declare-fun Typ_fun_1540 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1540 kinding
(assert (HasKind Typ_fun_1540
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1540)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1540)))))
;;;;;;;;;;;;;;;;Typ_fun_1540 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1540)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1540)))))
(declare-fun Prims.MkTuple2._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1542
(Term_constr_id Prims.MkTuple2._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.MkTuple2._1@tok
@a0)
@a1)
@x2)
(Prims.MkTuple2._1 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.MkTuple2._1@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple2._1@tok
Typ_fun_1540))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.MkTuple2._1 @a0
@a1
@x2)
@a0))
  
:pattern ((Prims.MkTuple2._1 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkTuple2._1 @a0
@a1
@x2)
(Prims.MkTuple2__1 @x2))
  
:pattern ((Prims.MkTuple2._1 @a0
@a1
@x2)))))

; </end encoding Prims.MkTuple2._1>

; encoding sigelt Prims.MkTuple2._2

; <Start encoding Prims.MkTuple2._2>
(declare-fun Prims.MkTuple2._2 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple2 'a 'b) -> Tot 'b)
(declare-fun Typ_fun_1544 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1544 kinding
(assert (HasKind Typ_fun_1544
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1544)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1544)))))
;;;;;;;;;;;;;;;;Typ_fun_1544 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1544)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1544)))))
(declare-fun Prims.MkTuple2._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1546
(Term_constr_id Prims.MkTuple2._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.MkTuple2._2@tok
@a0)
@a1)
@x2)
(Prims.MkTuple2._2 @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.MkTuple2._2@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple2._2@tok
Typ_fun_1544))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.MkTuple2._2 @a0
@a1
@x2)
@a1))
  
:pattern ((Prims.MkTuple2._2 @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkTuple2._2 @a0
@a1
@x2)
(Prims.MkTuple2__2 @x2))
  
:pattern ((Prims.MkTuple2._2 @a0
@a1
@x2)))))

; </end encoding Prims.MkTuple2._2>

; encoding sigelt Prims.Tuple3, Prims.MkTuple3

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple3 (Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple3@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple3@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple3@a2 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple3@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple3 (Type Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple3__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple3__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple3__c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple3__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple3__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple3__3 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> _3:'c -> Tot (Tuple3 'a 'b 'c))
(declare-fun Typ_fun_1566 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple3
(declare-fun Prims.MkTuple3@tok () Term)

; <Start encoding Prims.Tuple3>

; <start constructor Prims.Tuple3>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= 1557
(Type_constr_id (Prims.Tuple3 @a0
@a1
@a2)))
  
:pattern ((Prims.Tuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (Prims.Tuple3@a0 (Prims.Tuple3 @a0
@a1
@a2))
@a0)
  
:pattern ((Prims.Tuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (Prims.Tuple3@a1 (Prims.Tuple3 @a0
@a1
@a2))
@a1)
  
:pattern ((Prims.Tuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (Prims.Tuple3@a2 (Prims.Tuple3 @a0
@a1
@a2))
@a2)
  
:pattern ((Prims.Tuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple3 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1557)
(= @a0
(Prims.Tuple3 (Prims.Tuple3@a0 @a0)
(Prims.Tuple3@a1 @a0)
(Prims.Tuple3@a2 @a0)))))

; </end constructor Prims.Tuple3>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1558
(Type_constr_id Prims.Tuple3@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT Prims.Tuple3@tok
@a0)
@a1)
@a2)
(Prims.Tuple3 @a0
@a1
@a2))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT Prims.Tuple3@tok
@a0)
@a1)
@a2))

:pattern ((Prims.Tuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple3@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type))
(HasKind (Prims.Tuple3 @a0
@a1
@a2)
Kind_type))
  
:pattern ((Prims.Tuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple3 @a2
@a3
@a4))
(= (Prims.Tuple3 @a2
@a3
@a4)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple3 @a2
@a3
@a4))))))

; </end encoding Prims.Tuple3>

; <Start encoding Prims.MkTuple3>

; <start constructor Prims.MkTuple3>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= 1564
(Term_constr_id (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkTuple3__a (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@a0)
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkTuple3__b (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@a1)
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkTuple3__c (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@a2)
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkTuple3__1 (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@x3)
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkTuple3__2 (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@x4)
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkTuple3__3 (Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@x5)
  
:pattern ((Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple3 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1564)
(= @x0
(Prims.MkTuple3 (Prims.MkTuple3__a @x0)
(Prims.MkTuple3__b @x0)
(Prims.MkTuple3__c @x0)
(Prims.MkTuple3__1 @x0)
(Prims.MkTuple3__2 @x0)
(Prims.MkTuple3__3 @x0)))))

; </end constructor Prims.MkTuple3>
;;;;;;;;;;;;;;;;Typ_fun_1566 kinding
(assert (HasKind Typ_fun_1566
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1566)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1566)))))
;;;;;;;;;;;;;;;;Typ_fun_1566 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1566)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
@a1)
(HasType @x5
@a2)
(HasType @x6
@a3))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
(Prims.Tuple3 @a1
@a2
@a3)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1566)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1568
(Term_constr_id Prims.MkTuple3@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple3@tok
Typ_fun_1566))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3@tok
@a0)
@a1)
@a2)
@x3)
@x4)
@x5)
(Prims.MkTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3@tok
@a0)
@a1)
@a2)
@x3)
@x4)
@x5)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasTypeFuel @u0
@x4
@a1)
(HasTypeFuel @u0
@x5
@a2)
(HasTypeFuel @u0
@x6
@a3))
(HasTypeFuel @u0
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.Tuple3 @a1
@a2
@a3)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.Tuple3 @a1
@a2
@a3))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@a7 Type) (@a8 Type) (@a9 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.Tuple3 @a7
@a8
@a9))
(and (= @a3
@a9)
(= @a2
@a8)
(= @a1
@a7)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasTypeFuel @u0
@x4
@a1)
(HasTypeFuel @u0
@x5
@a2)
(HasTypeFuel @u0
@x6
@a3)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.Tuple3 @a7
@a8
@a9))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@a7 Type) (@a8 Type) (@a9 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.Tuple3 @a7
@a8
@a9))
(and (Valid (Precedes @x4
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)))
(Valid (Precedes @x5
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)))
(Valid (Precedes @x6
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.Tuple3 @a7
@a8
@a9))))))

; </end encoding Prims.MkTuple3>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple3 @a2
@a3
@a4))
(and (is-Prims.MkTuple3 @x1)
(= @a2
(Prims.MkTuple3__a @x1))
(= @a3
(Prims.MkTuple3__b @x1))
(= @a4
(Prims.MkTuple3__c @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple3 @a2
@a3
@a4))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple3

; <Start encoding Prims.is_MkTuple3>
(declare-fun Prims.is_MkTuple3 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple3 'a 'b 'c) -> Tot bool)
(declare-fun Typ_fun_1570 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1570 kinding
(assert (HasKind Typ_fun_1570
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1570)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1570)))))
;;;;;;;;;;;;;;;;Typ_fun_1570 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1570)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1570)))))
(declare-fun Prims.is_MkTuple3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1572
(Term_constr_id Prims.is_MkTuple3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.is_MkTuple3@tok
@a0)
@a1)
@a2)
@x3)
(Prims.is_MkTuple3 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.is_MkTuple3@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple3@tok
Typ_fun_1570))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.is_MkTuple3 @a0
@a1
@a2
@x3)
Prims.bool))
  
:pattern ((Prims.is_MkTuple3 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.is_MkTuple3 @a0
@a1
@a2
@x3)
(BoxBool (is-Prims.MkTuple3 @x3)))
  
:pattern ((Prims.is_MkTuple3 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.is_MkTuple3>

; encoding sigelt Prims.MkTuple3._1

; <Start encoding Prims.MkTuple3._1>
(declare-fun Prims.MkTuple3._1 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple3 'a 'b 'c) -> Tot 'a)
(declare-fun Typ_fun_1574 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1574 kinding
(assert (HasKind Typ_fun_1574
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1574)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1574)))))
;;;;;;;;;;;;;;;;Typ_fun_1574 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1574)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1574)))))
(declare-fun Prims.MkTuple3._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1576
(Term_constr_id Prims.MkTuple3._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3._1@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkTuple3._1 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3._1@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple3._1@tok
Typ_fun_1574))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.MkTuple3._1 @a0
@a1
@a2
@x3)
@a0))
  
:pattern ((Prims.MkTuple3._1 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkTuple3._1 @a0
@a1
@a2
@x3)
(Prims.MkTuple3__1 @x3))
  
:pattern ((Prims.MkTuple3._1 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkTuple3._1>

; encoding sigelt Prims.MkTuple3._2

; <Start encoding Prims.MkTuple3._2>
(declare-fun Prims.MkTuple3._2 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple3 'a 'b 'c) -> Tot 'b)
(declare-fun Typ_fun_1578 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1578 kinding
(assert (HasKind Typ_fun_1578
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1578)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1578)))))
;;;;;;;;;;;;;;;;Typ_fun_1578 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1578)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1578)))))
(declare-fun Prims.MkTuple3._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1580
(Term_constr_id Prims.MkTuple3._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3._2@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkTuple3._2 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3._2@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple3._2@tok
Typ_fun_1578))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.MkTuple3._2 @a0
@a1
@a2
@x3)
@a1))
  
:pattern ((Prims.MkTuple3._2 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkTuple3._2 @a0
@a1
@a2
@x3)
(Prims.MkTuple3__2 @x3))
  
:pattern ((Prims.MkTuple3._2 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkTuple3._2>

; encoding sigelt Prims.MkTuple3._3

; <Start encoding Prims.MkTuple3._3>
(declare-fun Prims.MkTuple3._3 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple3 'a 'b 'c) -> Tot 'c)
(declare-fun Typ_fun_1582 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1582 kinding
(assert (HasKind Typ_fun_1582
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1582)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1582)))))
;;;;;;;;;;;;;;;;Typ_fun_1582 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1582)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1582)))))
(declare-fun Prims.MkTuple3._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1584
(Term_constr_id Prims.MkTuple3._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3._3@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkTuple3._3 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkTuple3._3@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple3._3@tok
Typ_fun_1582))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.MkTuple3._3 @a0
@a1
@a2
@x3)
@a2))
  
:pattern ((Prims.MkTuple3._3 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkTuple3._3 @a0
@a1
@a2
@x3)
(Prims.MkTuple3__3 @x3))
  
:pattern ((Prims.MkTuple3._3 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkTuple3._3>

; encoding sigelt Prims.Tuple4, Prims.MkTuple4

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple4 (Type Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple4@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple4@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple4@a2 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple4@a3 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple4@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple4 (Type Type Type Type Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__d (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple4__4 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> _3:'c -> _4:'d -> Tot (Tuple4 'a 'b 'c 'd))
(declare-fun Typ_fun_1604 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple4
(declare-fun Prims.MkTuple4@tok () Term)

; <Start encoding Prims.Tuple4>

; <start constructor Prims.Tuple4>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= 1595
(Type_constr_id (Prims.Tuple4 @a0
@a1
@a2
@a3)))
  
:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.Tuple4@a0 (Prims.Tuple4 @a0
@a1
@a2
@a3))
@a0)
  
:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.Tuple4@a1 (Prims.Tuple4 @a0
@a1
@a2
@a3))
@a1)
  
:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.Tuple4@a2 (Prims.Tuple4 @a0
@a1
@a2
@a3))
@a2)
  
:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.Tuple4@a3 (Prims.Tuple4 @a0
@a1
@a2
@a3))
@a3)
  
:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple4 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1595)
(= @a0
(Prims.Tuple4 (Prims.Tuple4@a0 @a0)
(Prims.Tuple4@a1 @a0)
(Prims.Tuple4@a2 @a0)
(Prims.Tuple4@a3 @a0)))))

; </end constructor Prims.Tuple4>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1596
(Type_constr_id Prims.Tuple4@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple4@tok
@a0)
@a1)
@a2)
@a3)
(Prims.Tuple4 @a0
@a1
@a2
@a3))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple4@tok
@a0)
@a1)
@a2)
@a3))

:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple4@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type))
(HasKind (Prims.Tuple4 @a0
@a1
@a2
@a3)
Kind_type))
  
:pattern ((Prims.Tuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple4 @a2
@a3
@a4
@a5))
(= (Prims.Tuple4 @a2
@a3
@a4
@a5)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple4 @a2
@a3
@a4
@a5))))))

; </end encoding Prims.Tuple4>

; <Start encoding Prims.MkTuple4>

; <start constructor Prims.MkTuple4>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= 1602
(Term_constr_id (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__a (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a0)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__b (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a1)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__c (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a2)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__d (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a3)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__1 (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x4)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__2 (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x5)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__3 (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x6)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkTuple4__4 (Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x7)
  
:pattern ((Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple4 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1602)
(= @x0
(Prims.MkTuple4 (Prims.MkTuple4__a @x0)
(Prims.MkTuple4__b @x0)
(Prims.MkTuple4__c @x0)
(Prims.MkTuple4__d @x0)
(Prims.MkTuple4__1 @x0)
(Prims.MkTuple4__2 @x0)
(Prims.MkTuple4__3 @x0)
(Prims.MkTuple4__4 @x0)))))

; </end constructor Prims.MkTuple4>
;;;;;;;;;;;;;;;;Typ_fun_1604 kinding
(assert (HasKind Typ_fun_1604
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1604)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1604)))))
;;;;;;;;;;;;;;;;Typ_fun_1604 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1604)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
@a1)
(HasType @x6
@a2)
(HasType @x7
@a3)
(HasType @x8
@a4))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
@x8)
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1604)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1606
(Term_constr_id Prims.MkTuple4@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple4@tok
Typ_fun_1604))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
@x7)
(Prims.MkTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
@x7)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasTypeFuel @u0
@x5
@a1)
(HasTypeFuel @u0
@x6
@a2)
(HasTypeFuel @u0
@x7
@a3)
(HasTypeFuel @u0
@x8
@a4))
(HasTypeFuel @u0
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.Tuple4 @a1
@a2
@a3
@a4))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@a9 Type) (@a10 Type) (@a11 Type) (@a12 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.Tuple4 @a9
@a10
@a11
@a12))
(and (= @a4
@a12)
(= @a3
@a11)
(= @a2
@a10)
(= @a1
@a9)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasTypeFuel @u0
@x5
@a1)
(HasTypeFuel @u0
@x6
@a2)
(HasTypeFuel @u0
@x7
@a3)
(HasTypeFuel @u0
@x8
@a4)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.Tuple4 @a9
@a10
@a11
@a12))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@a9 Type) (@a10 Type) (@a11 Type) (@a12 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.Tuple4 @a9
@a10
@a11
@a12))
(and (Valid (Precedes @x5
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))
(Valid (Precedes @x6
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))
(Valid (Precedes @x7
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))
(Valid (Precedes @x8
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.Tuple4 @a9
@a10
@a11
@a12))))))

; </end encoding Prims.MkTuple4>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple4 @a2
@a3
@a4
@a5))
(and (is-Prims.MkTuple4 @x1)
(= @a2
(Prims.MkTuple4__a @x1))
(= @a3
(Prims.MkTuple4__b @x1))
(= @a4
(Prims.MkTuple4__c @x1))
(= @a5
(Prims.MkTuple4__d @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple4 @a2
@a3
@a4
@a5))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple4

; <Start encoding Prims.is_MkTuple4>
(declare-fun Prims.is_MkTuple4 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple4 'a 'b 'c 'd) -> Tot bool)
(declare-fun Typ_fun_1608 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1608 kinding
(assert (HasKind Typ_fun_1608
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1608)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1608)))))
;;;;;;;;;;;;;;;;Typ_fun_1608 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1608)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1608)))))
(declare-fun Prims.is_MkTuple4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1610
(Term_constr_id Prims.is_MkTuple4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.is_MkTuple4 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple4@tok
Typ_fun_1608))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.is_MkTuple4 @a0
@a1
@a2
@a3
@x4)
Prims.bool))
  
:pattern ((Prims.is_MkTuple4 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.is_MkTuple4 @a0
@a1
@a2
@a3
@x4)
(BoxBool (is-Prims.MkTuple4 @x4)))
  
:pattern ((Prims.is_MkTuple4 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.is_MkTuple4>

; encoding sigelt Prims.MkTuple4._1

; <Start encoding Prims.MkTuple4._1>
(declare-fun Prims.MkTuple4._1 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'a)
(declare-fun Typ_fun_1612 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1612 kinding
(assert (HasKind Typ_fun_1612
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1612)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1612)))))
;;;;;;;;;;;;;;;;Typ_fun_1612 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1612)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1612)))))
(declare-fun Prims.MkTuple4._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1614
(Term_constr_id Prims.MkTuple4._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._1@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._1 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._1@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple4._1@tok
Typ_fun_1612))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkTuple4._1 @a0
@a1
@a2
@a3
@x4)
@a0))
  
:pattern ((Prims.MkTuple4._1 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._1 @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__1 @x4))
  
:pattern ((Prims.MkTuple4._1 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4._1>

; encoding sigelt Prims.MkTuple4._2

; <Start encoding Prims.MkTuple4._2>
(declare-fun Prims.MkTuple4._2 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'b)
(declare-fun Typ_fun_1616 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1616 kinding
(assert (HasKind Typ_fun_1616
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1616)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1616)))))
;;;;;;;;;;;;;;;;Typ_fun_1616 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1616)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1616)))))
(declare-fun Prims.MkTuple4._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1618
(Term_constr_id Prims.MkTuple4._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._2@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._2 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._2@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple4._2@tok
Typ_fun_1616))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkTuple4._2 @a0
@a1
@a2
@a3
@x4)
@a1))
  
:pattern ((Prims.MkTuple4._2 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._2 @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__2 @x4))
  
:pattern ((Prims.MkTuple4._2 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4._2>

; encoding sigelt Prims.MkTuple4._3

; <Start encoding Prims.MkTuple4._3>
(declare-fun Prims.MkTuple4._3 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'c)
(declare-fun Typ_fun_1620 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1620 kinding
(assert (HasKind Typ_fun_1620
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1620)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1620)))))
;;;;;;;;;;;;;;;;Typ_fun_1620 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1620)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1620)))))
(declare-fun Prims.MkTuple4._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1622
(Term_constr_id Prims.MkTuple4._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._3@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._3 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._3@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple4._3@tok
Typ_fun_1620))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkTuple4._3 @a0
@a1
@a2
@a3
@x4)
@a2))
  
:pattern ((Prims.MkTuple4._3 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._3 @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__3 @x4))
  
:pattern ((Prims.MkTuple4._3 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4._3>

; encoding sigelt Prims.MkTuple4._4

; <Start encoding Prims.MkTuple4._4>
(declare-fun Prims.MkTuple4._4 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'd)
(declare-fun Typ_fun_1624 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1624 kinding
(assert (HasKind Typ_fun_1624
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1624)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1624)))))
;;;;;;;;;;;;;;;;Typ_fun_1624 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1624)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1624)))))
(declare-fun Prims.MkTuple4._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1626
(Term_constr_id Prims.MkTuple4._4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._4 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple4._4@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple4._4@tok
Typ_fun_1624))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkTuple4._4 @a0
@a1
@a2
@a3
@x4)
@a3))
  
:pattern ((Prims.MkTuple4._4 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._4 @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__4 @x4))
  
:pattern ((Prims.MkTuple4._4 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4._4>

; encoding sigelt Prims.Tuple5, Prims.MkTuple5

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple5 (Type Type Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple5@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple5@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple5@a2 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple5@a3 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple5@a4 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple5@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple5 (Type Type Type Type Type Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__d (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__e (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple5__5 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> _3:'c -> _4:'d -> _5:'e -> Tot (Tuple5 'a 'b 'c 'd 'e))
(declare-fun Typ_fun_1646 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple5
(declare-fun Prims.MkTuple5@tok () Term)

; <Start encoding Prims.Tuple5>

; <start constructor Prims.Tuple5>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= 1637
(Type_constr_id (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= (Prims.Tuple5@a0 (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4))
@a0)
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= (Prims.Tuple5@a1 (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4))
@a1)
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= (Prims.Tuple5@a2 (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4))
@a2)
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= (Prims.Tuple5@a3 (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4))
@a3)
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= (Prims.Tuple5@a4 (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4))
@a4)
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple5 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1637)
(= @a0
(Prims.Tuple5 (Prims.Tuple5@a0 @a0)
(Prims.Tuple5@a1 @a0)
(Prims.Tuple5@a2 @a0)
(Prims.Tuple5@a3 @a0)
(Prims.Tuple5@a4 @a0)))))

; </end constructor Prims.Tuple5>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1638
(Type_constr_id Prims.Tuple5@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple5@tok
@a0)
@a1)
@a2)
@a3)
@a4))

:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple5@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type))
(HasKind (Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)
Kind_type))
  
:pattern ((Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6))
(= (Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6))))))

; </end encoding Prims.Tuple5>

; <Start encoding Prims.MkTuple5>

; <start constructor Prims.MkTuple5>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= 1644
(Term_constr_id (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__a (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@a0)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__b (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@a1)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__c (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@a2)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__d (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@a3)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__e (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@a4)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__1 (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@x5)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__2 (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@x6)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__3 (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@x7)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__4 (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@x8)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (Prims.MkTuple5__5 (Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
@x9)
  
:pattern ((Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple5 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1644)
(= @x0
(Prims.MkTuple5 (Prims.MkTuple5__a @x0)
(Prims.MkTuple5__b @x0)
(Prims.MkTuple5__c @x0)
(Prims.MkTuple5__d @x0)
(Prims.MkTuple5__e @x0)
(Prims.MkTuple5__1 @x0)
(Prims.MkTuple5__2 @x0)
(Prims.MkTuple5__3 @x0)
(Prims.MkTuple5__4 @x0)
(Prims.MkTuple5__5 @x0)))))

; </end constructor Prims.MkTuple5>
;;;;;;;;;;;;;;;;Typ_fun_1646 kinding
(assert (HasKind Typ_fun_1646
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1646)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1646)))))
;;;;;;;;;;;;;;;;Typ_fun_1646 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1646)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
@a1)
(HasType @x7
@a2)
(HasType @x8
@a3)
(HasType @x9
@a4)
(HasType @x10
@a5))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)
@x10)
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)
@x10)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1646)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1648
(Term_constr_id Prims.MkTuple5@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple5@tok
Typ_fun_1646))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
@x8)
@x9)
(Prims.MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8
@x9))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
@x8)
@x9)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasTypeFuel @u0
@x6
@a1)
(HasTypeFuel @u0
@x7
@a2)
(HasTypeFuel @u0
@x8
@a3)
(HasTypeFuel @u0
@x9
@a4)
(HasTypeFuel @u0
@x10
@a5))
(HasTypeFuel @u0
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@a11 Type) (@a12 Type) (@a13 Type) (@a14 Type) (@a15 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)
(Prims.Tuple5 @a11
@a12
@a13
@a14
@a15))
(and (= @a5
@a15)
(= @a4
@a14)
(= @a3
@a13)
(= @a2
@a12)
(= @a1
@a11)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasTypeFuel @u0
@x6
@a1)
(HasTypeFuel @u0
@x7
@a2)
(HasTypeFuel @u0
@x8
@a3)
(HasTypeFuel @u0
@x9
@a4)
(HasTypeFuel @u0
@x10
@a5)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)
(Prims.Tuple5 @a11
@a12
@a13
@a14
@a15))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@a11 Type) (@a12 Type) (@a13 Type) (@a14 Type) (@a15 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)
(Prims.Tuple5 @a11
@a12
@a13
@a14
@a15))
(and (Valid (Precedes @x6
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)))
(Valid (Precedes @x7
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)))
(Valid (Precedes @x8
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)))
(Valid (Precedes @x9
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)))
(Valid (Precedes @x10
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple5 @a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10)
(Prims.Tuple5 @a11
@a12
@a13
@a14
@a15))))))

; </end encoding Prims.MkTuple5>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6))
(and (is-Prims.MkTuple5 @x1)
(= @a2
(Prims.MkTuple5__a @x1))
(= @a3
(Prims.MkTuple5__b @x1))
(= @a4
(Prims.MkTuple5__c @x1))
(= @a5
(Prims.MkTuple5__d @x1))
(= @a6
(Prims.MkTuple5__e @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple5

; <Start encoding Prims.is_MkTuple5>
(declare-fun Prims.is_MkTuple5 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple5 'a 'b 'c 'd 'e) -> Tot bool)
(declare-fun Typ_fun_1650 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1650 kinding
(assert (HasKind Typ_fun_1650
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1650)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1650)))))
;;;;;;;;;;;;;;;;Typ_fun_1650 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1650)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1650)))))
(declare-fun Prims.is_MkTuple5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1652
(Term_constr_id Prims.is_MkTuple5@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.is_MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple5@tok
Typ_fun_1650))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
(HasType (Prims.is_MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5)
Prims.bool))
  
:pattern ((Prims.is_MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.is_MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5)
(BoxBool (is-Prims.MkTuple5 @x5)))
  
:pattern ((Prims.is_MkTuple5 @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.is_MkTuple5>

; encoding sigelt Prims.MkTuple5._1

; <Start encoding Prims.MkTuple5._1>
(declare-fun Prims.MkTuple5._1 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'a)
(declare-fun Typ_fun_1654 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1654 kinding
(assert (HasKind Typ_fun_1654
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1654)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1654)))))
;;;;;;;;;;;;;;;;Typ_fun_1654 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1654)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1654)))))
(declare-fun Prims.MkTuple5._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1656
(Term_constr_id Prims.MkTuple5._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._1 @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple5._1@tok
Typ_fun_1654))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
(HasType (Prims.MkTuple5._1 @a0
@a1
@a2
@a3
@a4
@x5)
@a0))
  
:pattern ((Prims.MkTuple5._1 @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._1 @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__1 @x5))
  
:pattern ((Prims.MkTuple5._1 @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5._1>

; encoding sigelt Prims.MkTuple5._2

; <Start encoding Prims.MkTuple5._2>
(declare-fun Prims.MkTuple5._2 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'b)
(declare-fun Typ_fun_1658 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1658 kinding
(assert (HasKind Typ_fun_1658
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1658)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1658)))))
;;;;;;;;;;;;;;;;Typ_fun_1658 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1658)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1658)))))
(declare-fun Prims.MkTuple5._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1660
(Term_constr_id Prims.MkTuple5._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._2 @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple5._2@tok
Typ_fun_1658))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
(HasType (Prims.MkTuple5._2 @a0
@a1
@a2
@a3
@a4
@x5)
@a1))
  
:pattern ((Prims.MkTuple5._2 @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._2 @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__2 @x5))
  
:pattern ((Prims.MkTuple5._2 @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5._2>

; encoding sigelt Prims.MkTuple5._3

; <Start encoding Prims.MkTuple5._3>
(declare-fun Prims.MkTuple5._3 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'c)
(declare-fun Typ_fun_1662 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1662 kinding
(assert (HasKind Typ_fun_1662
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1662)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1662)))))
;;;;;;;;;;;;;;;;Typ_fun_1662 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1662)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1662)))))
(declare-fun Prims.MkTuple5._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1664
(Term_constr_id Prims.MkTuple5._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._3 @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple5._3@tok
Typ_fun_1662))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
(HasType (Prims.MkTuple5._3 @a0
@a1
@a2
@a3
@a4
@x5)
@a2))
  
:pattern ((Prims.MkTuple5._3 @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._3 @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__3 @x5))
  
:pattern ((Prims.MkTuple5._3 @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5._3>

; encoding sigelt Prims.MkTuple5._4

; <Start encoding Prims.MkTuple5._4>
(declare-fun Prims.MkTuple5._4 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'd)
(declare-fun Typ_fun_1666 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1666 kinding
(assert (HasKind Typ_fun_1666
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1666)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1666)))))
;;;;;;;;;;;;;;;;Typ_fun_1666 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1666)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1666)))))
(declare-fun Prims.MkTuple5._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1668
(Term_constr_id Prims.MkTuple5._4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._4 @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple5._4@tok
Typ_fun_1666))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
(HasType (Prims.MkTuple5._4 @a0
@a1
@a2
@a3
@a4
@x5)
@a3))
  
:pattern ((Prims.MkTuple5._4 @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._4 @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__4 @x5))
  
:pattern ((Prims.MkTuple5._4 @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5._4>

; encoding sigelt Prims.MkTuple5._5

; <Start encoding Prims.MkTuple5._5>
(declare-fun Prims.MkTuple5._5 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'e)
(declare-fun Typ_fun_1670 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1670 kinding
(assert (HasKind Typ_fun_1670
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1670)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1670)))))
;;;;;;;;;;;;;;;;Typ_fun_1670 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1670)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple5 @a1
@a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1670)))))
(declare-fun Prims.MkTuple5._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1672
(Term_constr_id Prims.MkTuple5._5@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._5 @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple5._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple5._5@tok
Typ_fun_1670))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple5 @a0
@a1
@a2
@a3
@a4)))
(HasType (Prims.MkTuple5._5 @a0
@a1
@a2
@a3
@a4
@x5)
@a4))
  
:pattern ((Prims.MkTuple5._5 @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._5 @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__5 @x5))
  
:pattern ((Prims.MkTuple5._5 @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5._5>

; encoding sigelt Prims.Tuple6, Prims.MkTuple6

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple6 (Type Type Type Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple6@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple6@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple6@a2 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple6@a3 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple6@a4 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple6@a5 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple6@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple6 (Type Type Type Type Type Type Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__d (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__e (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__f (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple6__6 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> _3:'c -> _4:'d -> _5:'e -> _6:'f -> Tot (Tuple6 'a 'b 'c 'd 'e 'f))
(declare-fun Typ_fun_1692 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple6
(declare-fun Prims.MkTuple6@tok () Term)

; <Start encoding Prims.Tuple6>

; <start constructor Prims.Tuple6>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= 1683
(Type_constr_id (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (Prims.Tuple6@a0 (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
@a0)
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (Prims.Tuple6@a1 (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
@a1)
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (Prims.Tuple6@a2 (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
@a2)
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (Prims.Tuple6@a3 (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
@a3)
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (Prims.Tuple6@a4 (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
@a4)
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (Prims.Tuple6@a5 (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
@a5)
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple6 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1683)
(= @a0
(Prims.Tuple6 (Prims.Tuple6@a0 @a0)
(Prims.Tuple6@a1 @a0)
(Prims.Tuple6@a2 @a0)
(Prims.Tuple6@a3 @a0)
(Prims.Tuple6@a4 @a0)
(Prims.Tuple6@a5 @a0)))))

; </end constructor Prims.Tuple6>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1684
(Type_constr_id Prims.Tuple6@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5))

:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple6@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type))
(HasKind (Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)
Kind_type))
  
:pattern ((Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7))
(= (Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7))))))

; </end encoding Prims.Tuple6>

; <Start encoding Prims.MkTuple6>

; <start constructor Prims.MkTuple6>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= 1690
(Term_constr_id (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__a (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@a0)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__b (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@a1)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__c (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@a2)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__d (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@a3)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__e (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@a4)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__f (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@a5)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__1 (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@x6)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__2 (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@x7)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__3 (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@x8)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__4 (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@x9)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__5 (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@x10)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (Prims.MkTuple6__6 (Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
@x11)
  
:pattern ((Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple6 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1690)
(= @x0
(Prims.MkTuple6 (Prims.MkTuple6__a @x0)
(Prims.MkTuple6__b @x0)
(Prims.MkTuple6__c @x0)
(Prims.MkTuple6__d @x0)
(Prims.MkTuple6__e @x0)
(Prims.MkTuple6__f @x0)
(Prims.MkTuple6__1 @x0)
(Prims.MkTuple6__2 @x0)
(Prims.MkTuple6__3 @x0)
(Prims.MkTuple6__4 @x0)
(Prims.MkTuple6__5 @x0)
(Prims.MkTuple6__6 @x0)))))

; </end constructor Prims.MkTuple6>
;;;;;;;;;;;;;;;;Typ_fun_1692 kinding
(assert (HasKind Typ_fun_1692
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1692)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1692)))))
;;;;;;;;;;;;;;;;Typ_fun_1692 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1692)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
@a1)
(HasType @x8
@a2)
(HasType @x9
@a3)
(HasType @x10
@a4)
(HasType @x11
@a5)
(HasType @x12
@a6))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@x8)
@x9)
@x10)
@x11)
@x12)
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@x8)
@x9)
@x10)
@x11)
@x12)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1692)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1694
(Term_constr_id Prims.MkTuple6@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple6@tok
Typ_fun_1692))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)
@x10)
@x11)
(Prims.MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6
@x7
@x8
@x9
@x10
@x11))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)
@x10)
@x11)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasTypeFuel @u0
@x7
@a1)
(HasTypeFuel @u0
@x8
@a2)
(HasTypeFuel @u0
@x9
@a3)
(HasTypeFuel @u0
@x10
@a4)
(HasTypeFuel @u0
@x11
@a5)
(HasTypeFuel @u0
@x12
@a6))
(HasTypeFuel @u0
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@a13 Type) (@a14 Type) (@a15 Type) (@a16 Type) (@a17 Type) (@a18 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)
(Prims.Tuple6 @a13
@a14
@a15
@a16
@a17
@a18))
(and (= @a6
@a18)
(= @a5
@a17)
(= @a4
@a16)
(= @a3
@a15)
(= @a2
@a14)
(= @a1
@a13)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasTypeFuel @u0
@x7
@a1)
(HasTypeFuel @u0
@x8
@a2)
(HasTypeFuel @u0
@x9
@a3)
(HasTypeFuel @u0
@x10
@a4)
(HasTypeFuel @u0
@x11
@a5)
(HasTypeFuel @u0
@x12
@a6)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)
(Prims.Tuple6 @a13
@a14
@a15
@a16
@a17
@a18))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@a13 Type) (@a14 Type) (@a15 Type) (@a16 Type) (@a17 Type) (@a18 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)
(Prims.Tuple6 @a13
@a14
@a15
@a16
@a17
@a18))
(and (Valid (Precedes @x7
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)))
(Valid (Precedes @x8
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)))
(Valid (Precedes @x9
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)))
(Valid (Precedes @x10
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)))
(Valid (Precedes @x11
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)))
(Valid (Precedes @x12
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple6 @a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12)
(Prims.Tuple6 @a13
@a14
@a15
@a16
@a17
@a18))))))

; </end encoding Prims.MkTuple6>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7))
(and (is-Prims.MkTuple6 @x1)
(= @a2
(Prims.MkTuple6__a @x1))
(= @a3
(Prims.MkTuple6__b @x1))
(= @a4
(Prims.MkTuple6__c @x1))
(= @a5
(Prims.MkTuple6__d @x1))
(= @a6
(Prims.MkTuple6__e @x1))
(= @a7
(Prims.MkTuple6__f @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple6

; <Start encoding Prims.is_MkTuple6>
(declare-fun Prims.is_MkTuple6 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple6 'a 'b 'c 'd 'e 'f) -> Tot bool)
(declare-fun Typ_fun_1696 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1696 kinding
(assert (HasKind Typ_fun_1696
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1696)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1696)))))
;;;;;;;;;;;;;;;;Typ_fun_1696 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1696)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1696)))))
(declare-fun Prims.is_MkTuple6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1698
(Term_constr_id Prims.is_MkTuple6@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.is_MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple6@tok
Typ_fun_1696))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.is_MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Prims.bool))
  
:pattern ((Prims.is_MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.is_MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(BoxBool (is-Prims.MkTuple6 @x6)))
  
:pattern ((Prims.is_MkTuple6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.is_MkTuple6>

; encoding sigelt Prims.MkTuple6._1

; <Start encoding Prims.MkTuple6._1>
(declare-fun Prims.MkTuple6._1 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'a)
(declare-fun Typ_fun_1700 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1700 kinding
(assert (HasKind Typ_fun_1700
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1700)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1700)))))
;;;;;;;;;;;;;;;;Typ_fun_1700 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1700)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1700)))))
(declare-fun Prims.MkTuple6._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1702
(Term_constr_id Prims.MkTuple6._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._1 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple6._1@tok
Typ_fun_1700))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.MkTuple6._1 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
@a0))
  
:pattern ((Prims.MkTuple6._1 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._1 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__1 @x6))
  
:pattern ((Prims.MkTuple6._1 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6._1>

; encoding sigelt Prims.MkTuple6._2

; <Start encoding Prims.MkTuple6._2>
(declare-fun Prims.MkTuple6._2 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'b)
(declare-fun Typ_fun_1704 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1704 kinding
(assert (HasKind Typ_fun_1704
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1704)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1704)))))
;;;;;;;;;;;;;;;;Typ_fun_1704 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1704)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1704)))))
(declare-fun Prims.MkTuple6._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1706
(Term_constr_id Prims.MkTuple6._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._2 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple6._2@tok
Typ_fun_1704))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.MkTuple6._2 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
@a1))
  
:pattern ((Prims.MkTuple6._2 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._2 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__2 @x6))
  
:pattern ((Prims.MkTuple6._2 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6._2>

; encoding sigelt Prims.MkTuple6._3

; <Start encoding Prims.MkTuple6._3>
(declare-fun Prims.MkTuple6._3 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'c)
(declare-fun Typ_fun_1708 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1708 kinding
(assert (HasKind Typ_fun_1708
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1708)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1708)))))
;;;;;;;;;;;;;;;;Typ_fun_1708 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1708)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1708)))))
(declare-fun Prims.MkTuple6._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1710
(Term_constr_id Prims.MkTuple6._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._3 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple6._3@tok
Typ_fun_1708))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.MkTuple6._3 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
@a2))
  
:pattern ((Prims.MkTuple6._3 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._3 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__3 @x6))
  
:pattern ((Prims.MkTuple6._3 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6._3>

; encoding sigelt Prims.MkTuple6._4

; <Start encoding Prims.MkTuple6._4>
(declare-fun Prims.MkTuple6._4 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'd)
(declare-fun Typ_fun_1712 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1712 kinding
(assert (HasKind Typ_fun_1712
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1712)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1712)))))
;;;;;;;;;;;;;;;;Typ_fun_1712 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1712)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1712)))))
(declare-fun Prims.MkTuple6._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1714
(Term_constr_id Prims.MkTuple6._4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._4 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple6._4@tok
Typ_fun_1712))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.MkTuple6._4 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
@a3))
  
:pattern ((Prims.MkTuple6._4 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._4 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__4 @x6))
  
:pattern ((Prims.MkTuple6._4 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6._4>

; encoding sigelt Prims.MkTuple6._5

; <Start encoding Prims.MkTuple6._5>
(declare-fun Prims.MkTuple6._5 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'e)
(declare-fun Typ_fun_1716 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1716 kinding
(assert (HasKind Typ_fun_1716
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1716)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1716)))))
;;;;;;;;;;;;;;;;Typ_fun_1716 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1716)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1716)))))
(declare-fun Prims.MkTuple6._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1718
(Term_constr_id Prims.MkTuple6._5@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._5 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple6._5@tok
Typ_fun_1716))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.MkTuple6._5 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
@a4))
  
:pattern ((Prims.MkTuple6._5 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._5 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__5 @x6))
  
:pattern ((Prims.MkTuple6._5 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6._5>

; encoding sigelt Prims.MkTuple6._6

; <Start encoding Prims.MkTuple6._6>
(declare-fun Prims.MkTuple6._6 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'f)
(declare-fun Typ_fun_1720 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1720 kinding
(assert (HasKind Typ_fun_1720
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1720)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1720)))))
;;;;;;;;;;;;;;;;Typ_fun_1720 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1720)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple6 @a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1720)))))
(declare-fun Prims.MkTuple6._6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1722
(Term_constr_id Prims.MkTuple6._6@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._6 @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple6._6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple6._6@tok
Typ_fun_1720))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple6 @a0
@a1
@a2
@a3
@a4
@a5)))
(HasType (Prims.MkTuple6._6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
@a5))
  
:pattern ((Prims.MkTuple6._6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__6 @x6))
  
:pattern ((Prims.MkTuple6._6 @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6._6>

; encoding sigelt Prims.Tuple7, Prims.MkTuple7

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple7 (Type Type Type Type Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a2 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a3 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a4 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a5 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple7@a6 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple7@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple7 (Type Type Type Type Type Type Type Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__d (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__e (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__f (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__g (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple7__7 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> _3:'c -> _4:'d -> _5:'e -> _6:'f -> _7:'g -> Tot (Tuple7 'a 'b 'c 'd 'e 'f 'g))
(declare-fun Typ_fun_1742 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple7
(declare-fun Prims.MkTuple7@tok () Term)

; <Start encoding Prims.Tuple7>

; <start constructor Prims.Tuple7>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= 1733
(Type_constr_id (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a0 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a0)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a1 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a1)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a2 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a2)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a3 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a3)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a4 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a4)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a5 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a5)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (Prims.Tuple7@a6 (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
@a6)
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple7 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1733)
(= @a0
(Prims.Tuple7 (Prims.Tuple7@a0 @a0)
(Prims.Tuple7@a1 @a0)
(Prims.Tuple7@a2 @a0)
(Prims.Tuple7@a3 @a0)
(Prims.Tuple7@a4 @a0)
(Prims.Tuple7@a5 @a0)
(Prims.Tuple7@a6 @a0)))))

; </end constructor Prims.Tuple7>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1734
(Type_constr_id Prims.Tuple7@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6))

:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple7@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type))
(HasKind (Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)
Kind_type))
  
:pattern ((Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8))
(= (Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8))))))

; </end encoding Prims.Tuple7>

; <Start encoding Prims.MkTuple7>

; <start constructor Prims.MkTuple7>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= 1740
(Term_constr_id (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__a (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a0)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__b (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a1)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__c (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a2)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__d (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a3)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__e (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a4)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__f (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a5)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__g (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@a6)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__1 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x7)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__2 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x8)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__3 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x9)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__4 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x10)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__5 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x11)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__6 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x12)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (Prims.MkTuple7__7 (Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
@x13)
  
:pattern ((Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple7 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1740)
(= @x0
(Prims.MkTuple7 (Prims.MkTuple7__a @x0)
(Prims.MkTuple7__b @x0)
(Prims.MkTuple7__c @x0)
(Prims.MkTuple7__d @x0)
(Prims.MkTuple7__e @x0)
(Prims.MkTuple7__f @x0)
(Prims.MkTuple7__g @x0)
(Prims.MkTuple7__1 @x0)
(Prims.MkTuple7__2 @x0)
(Prims.MkTuple7__3 @x0)
(Prims.MkTuple7__4 @x0)
(Prims.MkTuple7__5 @x0)
(Prims.MkTuple7__6 @x0)
(Prims.MkTuple7__7 @x0)))))

; </end constructor Prims.MkTuple7>
;;;;;;;;;;;;;;;;Typ_fun_1742 kinding
(assert (HasKind Typ_fun_1742
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1742)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1742)))))
;;;;;;;;;;;;;;;;Typ_fun_1742 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1742)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
@a1)
(HasType @x9
@a2)
(HasType @x10
@a3)
(HasType @x11
@a4)
(HasType @x12
@a5)
(HasType @x13
@a6)
(HasType @x14
@a7))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@x9)
@x10)
@x11)
@x12)
@x13)
@x14)
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@x9)
@x10)
@x11)
@x12)
@x13)
@x14)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1742)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1744
(Term_constr_id Prims.MkTuple7@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple7@tok
Typ_fun_1742))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@x8)
@x9)
@x10)
@x11)
@x12)
@x13)
(Prims.MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7
@x8
@x9
@x10
@x11
@x12
@x13))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@x8)
@x9)
@x10)
@x11)
@x12)
@x13)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasTypeFuel @u0
@x8
@a1)
(HasTypeFuel @u0
@x9
@a2)
(HasTypeFuel @u0
@x10
@a3)
(HasTypeFuel @u0
@x11
@a4)
(HasTypeFuel @u0
@x12
@a5)
(HasTypeFuel @u0
@x13
@a6)
(HasTypeFuel @u0
@x14
@a7))
(HasTypeFuel @u0
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@a15 Type) (@a16 Type) (@a17 Type) (@a18 Type) (@a19 Type) (@a20 Type) (@a21 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)
(Prims.Tuple7 @a15
@a16
@a17
@a18
@a19
@a20
@a21))
(and (= @a7
@a21)
(= @a6
@a20)
(= @a5
@a19)
(= @a4
@a18)
(= @a3
@a17)
(= @a2
@a16)
(= @a1
@a15)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasTypeFuel @u0
@x8
@a1)
(HasTypeFuel @u0
@x9
@a2)
(HasTypeFuel @u0
@x10
@a3)
(HasTypeFuel @u0
@x11
@a4)
(HasTypeFuel @u0
@x12
@a5)
(HasTypeFuel @u0
@x13
@a6)
(HasTypeFuel @u0
@x14
@a7)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)
(Prims.Tuple7 @a15
@a16
@a17
@a18
@a19
@a20
@a21))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@a15 Type) (@a16 Type) (@a17 Type) (@a18 Type) (@a19 Type) (@a20 Type) (@a21 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)
(Prims.Tuple7 @a15
@a16
@a17
@a18
@a19
@a20
@a21))
(and (Valid (Precedes @x8
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))
(Valid (Precedes @x9
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))
(Valid (Precedes @x10
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))
(Valid (Precedes @x11
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))
(Valid (Precedes @x12
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))
(Valid (Precedes @x13
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))
(Valid (Precedes @x14
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14)
(Prims.Tuple7 @a15
@a16
@a17
@a18
@a19
@a20
@a21))))))

; </end encoding Prims.MkTuple7>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8))
(and (is-Prims.MkTuple7 @x1)
(= @a2
(Prims.MkTuple7__a @x1))
(= @a3
(Prims.MkTuple7__b @x1))
(= @a4
(Prims.MkTuple7__c @x1))
(= @a5
(Prims.MkTuple7__d @x1))
(= @a6
(Prims.MkTuple7__e @x1))
(= @a7
(Prims.MkTuple7__f @x1))
(= @a8
(Prims.MkTuple7__g @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple7

; <Start encoding Prims.is_MkTuple7>
(declare-fun Prims.is_MkTuple7 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot bool)
(declare-fun Typ_fun_1746 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1746 kinding
(assert (HasKind Typ_fun_1746
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1746)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1746)))))
;;;;;;;;;;;;;;;;Typ_fun_1746 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1746)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1746)))))
(declare-fun Prims.is_MkTuple7@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1748
(Term_constr_id Prims.is_MkTuple7@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.is_MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple7@tok
Typ_fun_1746))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.is_MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Prims.bool))
  
:pattern ((Prims.is_MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.is_MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(BoxBool (is-Prims.MkTuple7 @x7)))
  
:pattern ((Prims.is_MkTuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.is_MkTuple7>

; encoding sigelt Prims.MkTuple7._1

; <Start encoding Prims.MkTuple7._1>
(declare-fun Prims.MkTuple7._1 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'a)
(declare-fun Typ_fun_1750 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1750 kinding
(assert (HasKind Typ_fun_1750
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1750)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1750)))))
;;;;;;;;;;;;;;;;Typ_fun_1750 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1750)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1750)))))
(declare-fun Prims.MkTuple7._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1752
(Term_constr_id Prims.MkTuple7._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._1@tok
Typ_fun_1750))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a0))
  
:pattern ((Prims.MkTuple7._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__1 @x7))
  
:pattern ((Prims.MkTuple7._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._1>

; encoding sigelt Prims.MkTuple7._2

; <Start encoding Prims.MkTuple7._2>
(declare-fun Prims.MkTuple7._2 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'b)
(declare-fun Typ_fun_1754 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1754 kinding
(assert (HasKind Typ_fun_1754
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1754)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1754)))))
;;;;;;;;;;;;;;;;Typ_fun_1754 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1754)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1754)))))
(declare-fun Prims.MkTuple7._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1756
(Term_constr_id Prims.MkTuple7._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._2@tok
Typ_fun_1754))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a1))
  
:pattern ((Prims.MkTuple7._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__2 @x7))
  
:pattern ((Prims.MkTuple7._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._2>

; encoding sigelt Prims.MkTuple7._3

; <Start encoding Prims.MkTuple7._3>
(declare-fun Prims.MkTuple7._3 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'c)
(declare-fun Typ_fun_1758 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1758 kinding
(assert (HasKind Typ_fun_1758
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1758)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1758)))))
;;;;;;;;;;;;;;;;Typ_fun_1758 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1758)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1758)))))
(declare-fun Prims.MkTuple7._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1760
(Term_constr_id Prims.MkTuple7._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._3@tok
Typ_fun_1758))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a2))
  
:pattern ((Prims.MkTuple7._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__3 @x7))
  
:pattern ((Prims.MkTuple7._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._3>

; encoding sigelt Prims.MkTuple7._4

; <Start encoding Prims.MkTuple7._4>
(declare-fun Prims.MkTuple7._4 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'd)
(declare-fun Typ_fun_1762 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1762 kinding
(assert (HasKind Typ_fun_1762
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1762)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1762)))))
;;;;;;;;;;;;;;;;Typ_fun_1762 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1762)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1762)))))
(declare-fun Prims.MkTuple7._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1764
(Term_constr_id Prims.MkTuple7._4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._4@tok
Typ_fun_1762))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a3))
  
:pattern ((Prims.MkTuple7._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__4 @x7))
  
:pattern ((Prims.MkTuple7._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._4>

; encoding sigelt Prims.MkTuple7._5

; <Start encoding Prims.MkTuple7._5>
(declare-fun Prims.MkTuple7._5 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'e)
(declare-fun Typ_fun_1766 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1766 kinding
(assert (HasKind Typ_fun_1766
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1766)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1766)))))
;;;;;;;;;;;;;;;;Typ_fun_1766 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1766)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1766)))))
(declare-fun Prims.MkTuple7._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1768
(Term_constr_id Prims.MkTuple7._5@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._5@tok
Typ_fun_1766))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a4))
  
:pattern ((Prims.MkTuple7._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__5 @x7))
  
:pattern ((Prims.MkTuple7._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._5>

; encoding sigelt Prims.MkTuple7._6

; <Start encoding Prims.MkTuple7._6>
(declare-fun Prims.MkTuple7._6 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'f)
(declare-fun Typ_fun_1770 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1770 kinding
(assert (HasKind Typ_fun_1770
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1770)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1770)))))
;;;;;;;;;;;;;;;;Typ_fun_1770 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1770)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1770)))))
(declare-fun Prims.MkTuple7._6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1772
(Term_constr_id Prims.MkTuple7._6@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._6@tok
Typ_fun_1770))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a5))
  
:pattern ((Prims.MkTuple7._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__6 @x7))
  
:pattern ((Prims.MkTuple7._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._6>

; encoding sigelt Prims.MkTuple7._7

; <Start encoding Prims.MkTuple7._7>
(declare-fun Prims.MkTuple7._7 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'g)
(declare-fun Typ_fun_1774 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1774 kinding
(assert (HasKind Typ_fun_1774
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1774)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1774)))))
;;;;;;;;;;;;;;;;Typ_fun_1774 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1774)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple7 @a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1774)))))
(declare-fun Prims.MkTuple7._7@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1776
(Term_constr_id Prims.MkTuple7._7@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple7._7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple7._7@tok
Typ_fun_1774))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasType @x7
(Prims.Tuple7 @a0
@a1
@a2
@a3
@a4
@a5
@a6)))
(HasType (Prims.MkTuple7._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
@a6))
  
:pattern ((Prims.MkTuple7._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__7 @x7))
  
:pattern ((Prims.MkTuple7._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7._7>

; encoding sigelt Prims.Tuple8, Prims.MkTuple8

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Tuple8 (Type Type Type Type Type Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a2 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a3 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a4 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a5 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a6 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Tuple8@a7 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Tuple8@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkTuple8 (Type Type Type Type Type Type Type Type Term Term Term Term Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__d (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__e (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__f (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__g (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__h (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__4 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__5 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__6 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__7 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkTuple8__8 (Term) Term)
;;;;;;;;;;;;;;;;(_1:'a -> _2:'b -> _3:'c -> _4:'d -> _5:'e -> _6:'f -> _7:'g -> _8:'h -> Tot (Tuple8 'a 'b 'c 'd 'e 'f 'g 'h))
(declare-fun Typ_fun_1796 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple8
(declare-fun Prims.MkTuple8@tok () Term)

; <Start encoding Prims.Tuple8>

; <start constructor Prims.Tuple8>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= 1787
(Type_constr_id (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a0 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a0)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a1 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a1)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a2 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a2)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a3 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a3)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a4 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a4)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a5 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a5)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a6 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a6)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (Prims.Tuple8@a7 (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
@a7)
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Tuple8 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1787)
(= @a0
(Prims.Tuple8 (Prims.Tuple8@a0 @a0)
(Prims.Tuple8@a1 @a0)
(Prims.Tuple8@a2 @a0)
(Prims.Tuple8@a3 @a0)
(Prims.Tuple8@a4 @a0)
(Prims.Tuple8@a5 @a0)
(Prims.Tuple8@a6 @a0)
(Prims.Tuple8@a7 @a0)))))

; </end constructor Prims.Tuple8>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1788
(Type_constr_id Prims.Tuple8@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.Tuple8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7))

:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Tuple8@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type))
(HasKind (Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)
Kind_type))
  
:pattern ((Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9))
(= (Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9))))))

; </end encoding Prims.Tuple8>

; <Start encoding Prims.MkTuple8>

; <start constructor Prims.MkTuple8>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= 1794
(Term_constr_id (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__a (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a0)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__b (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a1)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__c (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a2)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__d (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a3)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__e (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a4)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__f (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a5)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__g (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a6)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__h (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@a7)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__1 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x8)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__2 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x9)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__3 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x10)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__4 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x11)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__5 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x12)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__6 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x13)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__7 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x14)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (Prims.MkTuple8__8 (Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
@x15)
  
:pattern ((Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkTuple8 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1794)
(= @x0
(Prims.MkTuple8 (Prims.MkTuple8__a @x0)
(Prims.MkTuple8__b @x0)
(Prims.MkTuple8__c @x0)
(Prims.MkTuple8__d @x0)
(Prims.MkTuple8__e @x0)
(Prims.MkTuple8__f @x0)
(Prims.MkTuple8__g @x0)
(Prims.MkTuple8__h @x0)
(Prims.MkTuple8__1 @x0)
(Prims.MkTuple8__2 @x0)
(Prims.MkTuple8__3 @x0)
(Prims.MkTuple8__4 @x0)
(Prims.MkTuple8__5 @x0)
(Prims.MkTuple8__6 @x0)
(Prims.MkTuple8__7 @x0)
(Prims.MkTuple8__8 @x0)))))

; </end constructor Prims.MkTuple8>
;;;;;;;;;;;;;;;;Typ_fun_1796 kinding
(assert (HasKind Typ_fun_1796
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1796)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1796)))))
;;;;;;;;;;;;;;;;Typ_fun_1796 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1796)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term) (@x16 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
@a1)
(HasType @x10
@a2)
(HasType @x11
@a3)
(HasType @x12
@a4)
(HasType @x13
@a5)
(HasType @x14
@a6)
(HasType @x15
@a7)
(HasType @x16
@a8))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@x10)
@x11)
@x12)
@x13)
@x14)
@x15)
@x16)
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@x10)
@x11)
@x12)
@x13)
@x14)
@x15)
@x16)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1796)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1798
(Term_constr_id Prims.MkTuple8@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple8@tok
Typ_fun_1796))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@x9)
@x10)
@x11)
@x12)
@x13)
@x14)
@x15)
(Prims.MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8
@x9
@x10
@x11
@x12
@x13
@x14
@x15))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@x9)
@x10)
@x11)
@x12)
@x13)
@x14)
@x15)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term) (@x16 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasTypeFuel @u0
@x9
@a1)
(HasTypeFuel @u0
@x10
@a2)
(HasTypeFuel @u0
@x11
@a3)
(HasTypeFuel @u0
@x12
@a4)
(HasTypeFuel @u0
@x13
@a5)
(HasTypeFuel @u0
@x14
@a6)
(HasTypeFuel @u0
@x15
@a7)
(HasTypeFuel @u0
@x16
@a8))
(HasTypeFuel @u0
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term) (@x16 Term) (@a17 Type) (@a18 Type) (@a19 Type) (@a20 Type) (@a21 Type) (@a22 Type) (@a23 Type) (@a24 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)
(Prims.Tuple8 @a17
@a18
@a19
@a20
@a21
@a22
@a23
@a24))
(and (= @a8
@a24)
(= @a7
@a23)
(= @a6
@a22)
(= @a5
@a21)
(= @a4
@a20)
(= @a3
@a19)
(= @a2
@a18)
(= @a1
@a17)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasTypeFuel @u0
@x9
@a1)
(HasTypeFuel @u0
@x10
@a2)
(HasTypeFuel @u0
@x11
@a3)
(HasTypeFuel @u0
@x12
@a4)
(HasTypeFuel @u0
@x13
@a5)
(HasTypeFuel @u0
@x14
@a6)
(HasTypeFuel @u0
@x15
@a7)
(HasTypeFuel @u0
@x16
@a8)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)
(Prims.Tuple8 @a17
@a18
@a19
@a20
@a21
@a22
@a23
@a24))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term) (@x16 Term) (@a17 Type) (@a18 Type) (@a19 Type) (@a20 Type) (@a21 Type) (@a22 Type) (@a23 Type) (@a24 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)
(Prims.Tuple8 @a17
@a18
@a19
@a20
@a21
@a22
@a23
@a24))
(and (Valid (Precedes @x9
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x10
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x11
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x12
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x13
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x14
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x15
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))
(Valid (Precedes @x16
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkTuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8
@x9
@x10
@x11
@x12
@x13
@x14
@x15
@x16)
(Prims.Tuple8 @a17
@a18
@a19
@a20
@a21
@a22
@a23
@a24))))))

; </end encoding Prims.MkTuple8>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9))
(and (is-Prims.MkTuple8 @x1)
(= @a2
(Prims.MkTuple8__a @x1))
(= @a3
(Prims.MkTuple8__b @x1))
(= @a4
(Prims.MkTuple8__c @x1))
(= @a5
(Prims.MkTuple8__d @x1))
(= @a6
(Prims.MkTuple8__e @x1))
(= @a7
(Prims.MkTuple8__f @x1))
(= @a8
(Prims.MkTuple8__g @x1))
(= @a9
(Prims.MkTuple8__h @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9))))))

; </end encoding >

; encoding sigelt Prims.is_MkTuple8

; <Start encoding Prims.is_MkTuple8>
(declare-fun Prims.is_MkTuple8 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot bool)
(declare-fun Typ_fun_1800 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1800 kinding
(assert (HasKind Typ_fun_1800
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1800)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1800)))))
;;;;;;;;;;;;;;;;Typ_fun_1800 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1800)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1800)))))
(declare-fun Prims.is_MkTuple8@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1802
(Term_constr_id Prims.is_MkTuple8@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.is_MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkTuple8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkTuple8@tok
Typ_fun_1800))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.is_MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Prims.bool))
  
:pattern ((Prims.is_MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.is_MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(BoxBool (is-Prims.MkTuple8 @x8)))
  
:pattern ((Prims.is_MkTuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.is_MkTuple8>

; encoding sigelt Prims.MkTuple8._1

; <Start encoding Prims.MkTuple8._1>
(declare-fun Prims.MkTuple8._1 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'a)
(declare-fun Typ_fun_1804 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1804 kinding
(assert (HasKind Typ_fun_1804
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1804)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1804)))))
;;;;;;;;;;;;;;;;Typ_fun_1804 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1804)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1804)))))
(declare-fun Prims.MkTuple8._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1806
(Term_constr_id Prims.MkTuple8._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._1@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._1@tok
Typ_fun_1804))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a0))
  
:pattern ((Prims.MkTuple8._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__1 @x8))
  
:pattern ((Prims.MkTuple8._1 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._1>

; encoding sigelt Prims.MkTuple8._2

; <Start encoding Prims.MkTuple8._2>
(declare-fun Prims.MkTuple8._2 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'b)
(declare-fun Typ_fun_1808 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1808 kinding
(assert (HasKind Typ_fun_1808
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1808)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1808)))))
;;;;;;;;;;;;;;;;Typ_fun_1808 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1808)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1808)))))
(declare-fun Prims.MkTuple8._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1810
(Term_constr_id Prims.MkTuple8._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._2@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._2@tok
Typ_fun_1808))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a1))
  
:pattern ((Prims.MkTuple8._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__2 @x8))
  
:pattern ((Prims.MkTuple8._2 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._2>

; encoding sigelt Prims.MkTuple8._3

; <Start encoding Prims.MkTuple8._3>
(declare-fun Prims.MkTuple8._3 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'c)
(declare-fun Typ_fun_1812 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1812 kinding
(assert (HasKind Typ_fun_1812
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1812)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1812)))))
;;;;;;;;;;;;;;;;Typ_fun_1812 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1812)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1812)))))
(declare-fun Prims.MkTuple8._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1814
(Term_constr_id Prims.MkTuple8._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._3@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._3@tok
Typ_fun_1812))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a2))
  
:pattern ((Prims.MkTuple8._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__3 @x8))
  
:pattern ((Prims.MkTuple8._3 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._3>

; encoding sigelt Prims.MkTuple8._4

; <Start encoding Prims.MkTuple8._4>
(declare-fun Prims.MkTuple8._4 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'd)
(declare-fun Typ_fun_1816 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1816 kinding
(assert (HasKind Typ_fun_1816
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1816)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1816)))))
;;;;;;;;;;;;;;;;Typ_fun_1816 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1816)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1816)))))
(declare-fun Prims.MkTuple8._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1818
(Term_constr_id Prims.MkTuple8._4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._4@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._4@tok
Typ_fun_1816))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a3))
  
:pattern ((Prims.MkTuple8._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__4 @x8))
  
:pattern ((Prims.MkTuple8._4 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._4>

; encoding sigelt Prims.MkTuple8._5

; <Start encoding Prims.MkTuple8._5>
(declare-fun Prims.MkTuple8._5 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'e)
(declare-fun Typ_fun_1820 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1820 kinding
(assert (HasKind Typ_fun_1820
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1820)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1820)))))
;;;;;;;;;;;;;;;;Typ_fun_1820 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1820)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1820)))))
(declare-fun Prims.MkTuple8._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1822
(Term_constr_id Prims.MkTuple8._5@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._5@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._5@tok
Typ_fun_1820))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a4))
  
:pattern ((Prims.MkTuple8._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__5 @x8))
  
:pattern ((Prims.MkTuple8._5 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._5>

; encoding sigelt Prims.MkTuple8._6

; <Start encoding Prims.MkTuple8._6>
(declare-fun Prims.MkTuple8._6 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'f)
(declare-fun Typ_fun_1824 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1824 kinding
(assert (HasKind Typ_fun_1824
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1824)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1824)))))
;;;;;;;;;;;;;;;;Typ_fun_1824 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1824)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1824)))))
(declare-fun Prims.MkTuple8._6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1826
(Term_constr_id Prims.MkTuple8._6@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._6@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._6@tok
Typ_fun_1824))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a5))
  
:pattern ((Prims.MkTuple8._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__6 @x8))
  
:pattern ((Prims.MkTuple8._6 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._6>

; encoding sigelt Prims.MkTuple8._7

; <Start encoding Prims.MkTuple8._7>
(declare-fun Prims.MkTuple8._7 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'g)
(declare-fun Typ_fun_1828 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1828 kinding
(assert (HasKind Typ_fun_1828
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1828)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1828)))))
;;;;;;;;;;;;;;;;Typ_fun_1828 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1828)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1828)))))
(declare-fun Prims.MkTuple8._7@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1830
(Term_constr_id Prims.MkTuple8._7@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._7@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._7@tok
Typ_fun_1828))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a6))
  
:pattern ((Prims.MkTuple8._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__7 @x8))
  
:pattern ((Prims.MkTuple8._7 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._7>

; encoding sigelt Prims.MkTuple8._8

; <Start encoding Prims.MkTuple8._8>
(declare-fun Prims.MkTuple8._8 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'h)
(declare-fun Typ_fun_1832 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1832 kinding
(assert (HasKind Typ_fun_1832
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1832)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1832)))))
;;;;;;;;;;;;;;;;Typ_fun_1832 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1832)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasKind @a8
Kind_type)
(HasType @x9
(Prims.Tuple8 @a1
@a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1832)))))
(declare-fun Prims.MkTuple8._8@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1834
(Term_constr_id Prims.MkTuple8._8@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkTuple8._8@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkTuple8._8@tok
Typ_fun_1832))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasKind @a6
Kind_type)
(HasKind @a7
Kind_type)
(HasType @x8
(Prims.Tuple8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (Prims.MkTuple8._8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
@a7))
  
:pattern ((Prims.MkTuple8._8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__8 @x8))
  
:pattern ((Prims.MkTuple8._8 @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8._8>

; encoding sigelt Prims.DTuple3, Prims.MkDTuple3

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.DTuple3 (Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple3@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple3@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple3@a2 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.DTuple3@tok () Type)
;;;;;;;;;;;;;;;;(x:a -> (b x) -> Type)
(declare-fun Kind_arrow_1858 (Type Type) Kind)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkDTuple3 (Type Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple3_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple3_b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple3_c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple3__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple3__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple3__3 (Term) Term)
;;;;;;;;;;;;;;;;(_1:a -> _2:(b _1) -> _3:(c _1 _2) -> Tot (DTuple3 a b c))
(declare-fun Typ_fun_1872 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkDTuple3
(declare-fun Prims.MkDTuple3@tok () Term)

; <Start encoding Prims.DTuple3>

; <start constructor Prims.DTuple3>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= 1859
(Type_constr_id (Prims.DTuple3 @a0
@a1
@a2)))
  
:pattern ((Prims.DTuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (Prims.DTuple3@a0 (Prims.DTuple3 @a0
@a1
@a2))
@a0)
  
:pattern ((Prims.DTuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (Prims.DTuple3@a1 (Prims.DTuple3 @a0
@a1
@a2))
@a1)
  
:pattern ((Prims.DTuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (Prims.DTuple3@a2 (Prims.DTuple3 @a0
@a1
@a2))
@a2)
  
:pattern ((Prims.DTuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.DTuple3 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1859)
(= @a0
(Prims.DTuple3 (Prims.DTuple3@a0 @a0)
(Prims.DTuple3@a1 @a0)
(Prims.DTuple3@a2 @a0)))))

; </end constructor Prims.DTuple3>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1860
(Type_constr_id Prims.DTuple3@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT Prims.DTuple3@tok
@a0)
@a1)
@a2)
(Prims.DTuple3 @a0
@a1
@a2))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT Prims.DTuple3@tok
@a0)
@a1)
@a2))

:pattern ((Prims.DTuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;Kind_arrow_1858 interpretation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (iff (HasKind @a0
(Kind_arrow_1858 @a1
@a2))
(and (is-Kind_arrow (PreKind @a0))
(forall ((@x3 Term))
 (! (implies (HasType @x3
@a2)
(and (is-Kind_arrow (PreKind (ApplyTE @a0
@x3)))
(forall ((@x4 Term))
 (! (implies (HasType @x4
(ApplyTE @a1
@x3))
(HasKind (ApplyTE (ApplyTE @a0
@x3)
@x4)
Kind_type))
  
:pattern ((ApplyTE (ApplyTE @a0
@x3)
@x4))))))
  
:pattern ((ApplyTE @a0
@x3))))))
  
:pattern ((HasKind @a0
(Kind_arrow_1858 @a1
@a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.DTuple3@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0)))
(HasKind (Prims.DTuple3 @a0
@a1
@a2)
Kind_type))
  
:pattern ((Prims.DTuple3 @a0
@a1
@a2)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.DTuple3 @a2
@a3
@a4))
(= (Prims.DTuple3 @a2
@a3
@a4)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.DTuple3 @a2
@a3
@a4))))))

; </end encoding Prims.DTuple3>

; <Start encoding Prims.MkDTuple3>

; <start constructor Prims.MkDTuple3>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= 1868
(Term_constr_id (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3_a (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@a0)
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3_b (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@a1)
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3_c (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@a2)
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3__1 (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@x3)
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3__2 (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@x4)
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3__3 (Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
@x5)
  
:pattern ((Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkDTuple3 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1868)
(= @x0
(Prims.MkDTuple3 (Prims.MkDTuple3_a @x0)
(Prims.MkDTuple3_b @x0)
(Prims.MkDTuple3_c @x0)
(Prims.MkDTuple3__1 @x0)
(Prims.MkDTuple3__2 @x0)
(Prims.MkDTuple3__3 @x0)))))

; </end constructor Prims.MkDTuple3>
;;;;;;;;;;;;;;;;Typ_fun_1872 kinding
(assert (HasKind Typ_fun_1872
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1872)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1872)))))
;;;;;;;;;;;;;;;;Typ_fun_1872 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1872)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasType @x4
@a1)
(HasType @x5
(ApplyTE @a2
@x4))
(HasType @x6
(ApplyTE (ApplyTE @a3
@x4)
@x5)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
(Prims.DTuple3 @a1
@a2
@a3)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1872)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1876
(Term_constr_id Prims.MkDTuple3@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkDTuple3@tok
Typ_fun_1872))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3@tok
@a0)
@a1)
@a2)
@x3)
@x4)
@x5)
(Prims.MkDTuple3 @a0
@a1
@a2
@x3
@x4
@x5))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3@tok
@a0)
@a1)
@a2)
@x3)
@x4)
@x5)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasTypeFuel @u0
@x4
@a1)
(HasTypeFuel @u0
@x5
(ApplyTE @a2
@x4))
(HasTypeFuel @u0
@x6
(ApplyTE (ApplyTE @a3
@x4)
@x5)))
(HasTypeFuel @u0
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.DTuple3 @a1
@a2
@a3)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.DTuple3 @a1
@a2
@a3))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@a7 Type) (@a8 Type) (@a9 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.DTuple3 @a7
@a8
@a9))
(and (= @a3
@a9)
(= @a2
@a8)
(= @a1
@a7)
(HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasTypeFuel @u0
@x4
@a1)
(HasTypeFuel @u0
@x5
(ApplyTE @a2
@x4))
(HasTypeFuel @u0
@x6
(ApplyTE (ApplyTE @a3
@x4)
@x5))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.DTuple3 @a7
@a8
@a9))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@a7 Type) (@a8 Type) (@a9 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.DTuple3 @a7
@a8
@a9))
(and (Valid (Precedes @x4
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)))
(Valid (Precedes @x5
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)))
(Valid (Precedes @x6
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkDTuple3 @a1
@a2
@a3
@x4
@x5
@x6)
(Prims.DTuple3 @a7
@a8
@a9))))))

; </end encoding Prims.MkDTuple3>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.DTuple3 @a2
@a3
@a4))
(and (is-Prims.MkDTuple3 @x1)
(= @a2
(Prims.MkDTuple3_a @x1))
(= @a3
(Prims.MkDTuple3_b @x1))
(= @a4
(Prims.MkDTuple3_c @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.DTuple3 @a2
@a3
@a4))))))

; </end encoding >

; encoding sigelt Prims.is_MkDTuple3

; <Start encoding Prims.is_MkDTuple3>
(declare-fun Prims.is_MkDTuple3 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((DTuple3 a b c) -> Tot bool)
(declare-fun Typ_fun_1884 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1884 kinding
(assert (HasKind Typ_fun_1884
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1884)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1884)))))
;;;;;;;;;;;;;;;;Typ_fun_1884 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1884)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasType @x4
(Prims.DTuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1884)))))
(declare-fun Prims.is_MkDTuple3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1886
(Term_constr_id Prims.is_MkDTuple3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.is_MkDTuple3@tok
@a0)
@a1)
@a2)
@x3)
(Prims.is_MkDTuple3 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.is_MkDTuple3@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkDTuple3@tok
Typ_fun_1884))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.is_MkDTuple3 @a0
@a1
@a2
@x3)
Prims.bool))
  
:pattern ((Prims.is_MkDTuple3 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.is_MkDTuple3 @a0
@a1
@a2
@x3)
(BoxBool (is-Prims.MkDTuple3 @x3)))
  
:pattern ((Prims.is_MkDTuple3 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.is_MkDTuple3>

; encoding sigelt Prims.MkDTuple3.a

; <Start encoding Prims.MkDTuple3.a>
(declare-fun Prims.MkDTuple3.a (Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple3.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1892
(Type_constr_id Prims.MkDTuple3.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple3.a@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkDTuple3.a @a0
@a1
@a2
@x3))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple3.a@tok
@a0)
@a1)
@a2)
@x3))

:pattern ((Prims.MkDTuple3.a @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple3.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasKind (Prims.MkDTuple3.a @a0
@a1
@a2
@x3)
Kind_type))
  
:pattern ((Prims.MkDTuple3.a @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkDTuple3.a @a0
@a1
@a2
@x3)
(Prims.MkDTuple3_a @x3))
  
:pattern ((Prims.MkDTuple3.a @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkDTuple3.a>

; encoding sigelt Prims.MkDTuple3.b

; <Start encoding Prims.MkDTuple3.b>
(declare-fun Prims.MkDTuple3.b (Type Type Type Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple3.b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1901
(Type_constr_id Prims.MkDTuple3.b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple3.b@tok
@a0)
@a1)
@a2)
@x3)
@x4)
(Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple3.b@tok
@a0)
@a1)
@a2)
@x3)
@x4))

:pattern ((Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple3.b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2))
(HasType @x4
(Prims.MkDTuple3.a @a0
@a1
@a2
@x3)))
(HasKind (Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4)
Kind_type))
  
:pattern ((Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (= (Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4)
(ApplyTE (Prims.MkDTuple3_b @x3)
@x4))
  
:pattern ((Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4)))))

; </end encoding Prims.MkDTuple3.b>

; encoding sigelt Prims.MkDTuple3.c

; <Start encoding Prims.MkDTuple3.c>
(declare-fun Prims.MkDTuple3.c (Type Type Type Term Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple3.c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1912
(Type_constr_id Prims.MkDTuple3.c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple3.c@tok
@a0)
@a1)
@a2)
@x3)
@x4)
@x5)
(Prims.MkDTuple3.c @a0
@a1
@a2
@x3
@x4
@x5))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple3.c@tok
@a0)
@a1)
@a2)
@x3)
@x4)
@x5))

:pattern ((Prims.MkDTuple3.c @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple3.c@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2))
(HasType @x4
(Prims.MkDTuple3.a @a0
@a1
@a2
@x3))
(HasType @x5
(Prims.MkDTuple3.b @a0
@a1
@a2
@x3
@x4)))
(HasKind (Prims.MkDTuple3.c @a0
@a1
@a2
@x3
@x4
@x5)
Kind_type))
  
:pattern ((Prims.MkDTuple3.c @a0
@a1
@a2
@x3
@x4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple3.c @a0
@a1
@a2
@x3
@x4
@x5)
(ApplyTE (ApplyTE (Prims.MkDTuple3_c @x3)
@x4)
@x5))
  
:pattern ((Prims.MkDTuple3.c @a0
@a1
@a2
@x3
@x4
@x5)))))

; </end encoding Prims.MkDTuple3.c>

; encoding sigelt Prims.MkDTuple3._1

; <Start encoding Prims.MkDTuple3._1>
(declare-fun Prims.MkDTuple3._1 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple3 a b c) -> Tot (a projectee))
(declare-fun Typ_fun_1923 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1923 kinding
(assert (HasKind Typ_fun_1923
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1923)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1923)))))
;;;;;;;;;;;;;;;;Typ_fun_1923 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1923)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasType @x4
(Prims.DTuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple3.a @a1
@a2
@a3
@x4)))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1923)))))
(declare-fun Prims.MkDTuple3._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1925
(Term_constr_id Prims.MkDTuple3._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3._1@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkDTuple3._1 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3._1@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple3._1@tok
Typ_fun_1923))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.MkDTuple3._1 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3.a @a0
@a1
@a2
@x3)))
  
:pattern ((Prims.MkDTuple3._1 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkDTuple3._1 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3__1 @x3))
  
:pattern ((Prims.MkDTuple3._1 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkDTuple3._1>

; encoding sigelt Prims.MkDTuple3._2

; <Start encoding Prims.MkDTuple3._2>
(declare-fun Prims.MkDTuple3._2 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple3 a b c) -> Tot (b projectee (_1 projectee)))
(declare-fun Typ_fun_1938 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1938 kinding
(assert (HasKind Typ_fun_1938
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1938)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1938)))))
;;;;;;;;;;;;;;;;Typ_fun_1938 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1938)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasType @x4
(Prims.DTuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple3.b @a1
@a2
@a3
@x4
(Prims.MkDTuple3._1 @a1
@a2
@a3
@x4))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1938)))))
(declare-fun Prims.MkDTuple3._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1940
(Term_constr_id Prims.MkDTuple3._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3._2@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkDTuple3._2 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3._2@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple3._2@tok
Typ_fun_1938))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.MkDTuple3._2 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3.b @a0
@a1
@a2
@x3
(Prims.MkDTuple3._1 @a0
@a1
@a2
@x3))))
  
:pattern ((Prims.MkDTuple3._2 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkDTuple3._2 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3__2 @x3))
  
:pattern ((Prims.MkDTuple3._2 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkDTuple3._2>

; encoding sigelt Prims.MkDTuple3._3

; <Start encoding Prims.MkDTuple3._3>
(declare-fun Prims.MkDTuple3._3 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple3 a b c) -> Tot (c projectee (_1 projectee) (_2 projectee)))
(declare-fun Typ_fun_1955 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1955 kinding
(assert (HasKind Typ_fun_1955
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_1955)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1955)))))
;;;;;;;;;;;;;;;;Typ_fun_1955 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_1955)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasType @x4
(Prims.DTuple3 @a1
@a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple3.c @a1
@a2
@a3
@x4
(Prims.MkDTuple3._1 @a1
@a2
@a3
@x4)
(Prims.MkDTuple3._2 @a1
@a2
@a3
@x4))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_1955)))))
(declare-fun Prims.MkDTuple3._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1957
(Term_constr_id Prims.MkDTuple3._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3._3@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkDTuple3._3 @a0
@a1
@a2
@x3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET Prims.MkDTuple3._3@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple3._3@tok
Typ_fun_1955))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.MkDTuple3._3 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3.c @a0
@a1
@a2
@x3
(Prims.MkDTuple3._1 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3._2 @a0
@a1
@a2
@x3))))
  
:pattern ((Prims.MkDTuple3._3 @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkDTuple3._3 @a0
@a1
@a2
@x3)
(Prims.MkDTuple3__3 @x3))
  
:pattern ((Prims.MkDTuple3._3 @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkDTuple3._3>

; encoding sigelt Prims.DTuple4, Prims.MkDTuple4

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.DTuple4 (Type Type Type Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple4@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple4@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple4@a2 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.DTuple4@a3 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.DTuple4@tok () Type)
;;;;;;;;;;;;;;;;(x:a -> y:(b x) -> z:(c x y) -> Type)
(declare-fun Kind_arrow_1987 (Type Type Type) Kind)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.MkDTuple4 (Type Type Type Type Term Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4_b (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4_c (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4_d (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4__2 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4__3 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.MkDTuple4__4 (Term) Term)
;;;;;;;;;;;;;;;;(_1:a -> _2:(b _1) -> _3:(c _1 _2) -> _4:(d _1 _2 _3) -> Tot (DTuple4 a b c d))
(declare-fun Typ_fun_2003 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkDTuple4
(declare-fun Prims.MkDTuple4@tok () Term)

; <Start encoding Prims.DTuple4>

; <start constructor Prims.DTuple4>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= 1988
(Type_constr_id (Prims.DTuple4 @a0
@a1
@a2
@a3)))
  
:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.DTuple4@a0 (Prims.DTuple4 @a0
@a1
@a2
@a3))
@a0)
  
:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.DTuple4@a1 (Prims.DTuple4 @a0
@a1
@a2
@a3))
@a1)
  
:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.DTuple4@a2 (Prims.DTuple4 @a0
@a1
@a2
@a3))
@a2)
  
:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (Prims.DTuple4@a3 (Prims.DTuple4 @a0
@a1
@a2
@a3))
@a3)
  
:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.DTuple4 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1988)
(= @a0
(Prims.DTuple4 (Prims.DTuple4@a0 @a0)
(Prims.DTuple4@a1 @a0)
(Prims.DTuple4@a2 @a0)
(Prims.DTuple4@a3 @a0)))))

; </end constructor Prims.DTuple4>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1989
(Type_constr_id Prims.DTuple4@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (= (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.DTuple4@tok
@a0)
@a1)
@a2)
@a3)
(Prims.DTuple4 @a0
@a1
@a2
@a3))
  
:pattern ((ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.DTuple4@tok
@a0)
@a1)
@a2)
@a3))

:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;Kind_arrow_1987 interpretation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (iff (HasKind @a0
(Kind_arrow_1987 @a1
@a2
@a3))
(and (is-Kind_arrow (PreKind @a0))
(forall ((@x4 Term))
 (! (implies (HasType @x4
@a3)
(and (is-Kind_arrow (PreKind (ApplyTE @a0
@x4)))
(forall ((@x5 Term))
 (! (implies (HasType @x5
(ApplyTE @a2
@x4))
(and (is-Kind_arrow (PreKind (ApplyTE (ApplyTE @a0
@x4)
@x5)))
(forall ((@x6 Term))
 (! (implies (HasType @x6
(ApplyTE (ApplyTE @a1
@x4)
@x5))
(HasKind (ApplyTE (ApplyTE (ApplyTE @a0
@x4)
@x5)
@x6)
Kind_type))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE @a0
@x4)
@x5)
@x6))))))
  
:pattern ((ApplyTE (ApplyTE @a0
@x4)
@x5))))))
  
:pattern ((ApplyTE @a0
@x4))))))
  
:pattern ((HasKind @a0
(Kind_arrow_1987 @a1
@a2
@a3))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.DTuple4@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0)))
(HasKind (Prims.DTuple4 @a0
@a1
@a2
@a3)
Kind_type))
  
:pattern ((Prims.DTuple4 @a0
@a1
@a2
@a3)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel @u1
@x0
(Prims.DTuple4 @a2
@a3
@a4
@a5))
(= (Prims.DTuple4 @a2
@a3
@a4
@a5)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(Prims.DTuple4 @a2
@a3
@a4
@a5))))))

; </end encoding Prims.DTuple4>

; <Start encoding Prims.MkDTuple4>

; <start constructor Prims.MkDTuple4>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= 1998
(Term_constr_id (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4_a (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a0)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4_b (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a1)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4_c (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a2)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4_d (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@a3)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4__1 (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x4)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4__2 (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x5)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4__3 (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x6)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4__4 (Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
@x7)
  
:pattern ((Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.MkDTuple4 ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1998)
(= @x0
(Prims.MkDTuple4 (Prims.MkDTuple4_a @x0)
(Prims.MkDTuple4_b @x0)
(Prims.MkDTuple4_c @x0)
(Prims.MkDTuple4_d @x0)
(Prims.MkDTuple4__1 @x0)
(Prims.MkDTuple4__2 @x0)
(Prims.MkDTuple4__3 @x0)
(Prims.MkDTuple4__4 @x0)))))

; </end constructor Prims.MkDTuple4>
;;;;;;;;;;;;;;;;Typ_fun_2003 kinding
(assert (HasKind Typ_fun_2003
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2003)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2003)))))
;;;;;;;;;;;;;;;;Typ_fun_2003 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2003)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasType @x5
@a1)
(HasType @x6
(ApplyTE @a2
@x5))
(HasType @x7
(ApplyTE (ApplyTE @a3
@x5)
@x6))
(HasType @x8
(ApplyTE (ApplyTE (ApplyTE @a4
@x5)
@x6)
@x7)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
@x8)
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
@x8)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2003)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2008
(Term_constr_id Prims.MkDTuple4@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkDTuple4@tok
Typ_fun_2003))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
@x7)
(Prims.MkDTuple4 @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
@x7)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasTypeFuel @u0
@x5
@a1)
(HasTypeFuel @u0
@x6
(ApplyTE @a2
@x5))
(HasTypeFuel @u0
@x7
(ApplyTE (ApplyTE @a3
@x5)
@x6))
(HasTypeFuel @u0
@x8
(ApplyTE (ApplyTE (ApplyTE @a4
@x5)
@x6)
@x7)))
(HasTypeFuel @u0
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
  
:pattern ((HasTypeFuel @u0
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.DTuple4 @a1
@a2
@a3
@a4))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@a9 Type) (@a10 Type) (@a11 Type) (@a12 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.DTuple4 @a9
@a10
@a11
@a12))
(and (= @a4
@a12)
(= @a3
@a11)
(= @a2
@a10)
(= @a1
@a9)
(HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasTypeFuel @u0
@x5
@a1)
(HasTypeFuel @u0
@x6
(ApplyTE @a2
@x5))
(HasTypeFuel @u0
@x7
(ApplyTE (ApplyTE @a3
@x5)
@x6))
(HasTypeFuel @u0
@x8
(ApplyTE (ApplyTE (ApplyTE @a4
@x5)
@x6)
@x7))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.DTuple4 @a9
@a10
@a11
@a12))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term) (@x8 Term) (@a9 Type) (@a10 Type) (@a11 Type) (@a12 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.DTuple4 @a9
@a10
@a11
@a12))
(and (Valid (Precedes @x5
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))
(Valid (Precedes @x6
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))
(Valid (Precedes @x7
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))
(Valid (Precedes @x8
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.MkDTuple4 @a1
@a2
@a3
@a4
@x5
@x6
@x7
@x8)
(Prims.DTuple4 @a9
@a10
@a11
@a12))))))

; </end encoding Prims.MkDTuple4>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.DTuple4 @a2
@a3
@a4
@a5))
(and (is-Prims.MkDTuple4 @x1)
(= @a2
(Prims.MkDTuple4_a @x1))
(= @a3
(Prims.MkDTuple4_b @x1))
(= @a4
(Prims.MkDTuple4_c @x1))
(= @a5
(Prims.MkDTuple4_d @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(Prims.DTuple4 @a2
@a3
@a4
@a5))))))

; </end encoding >

; encoding sigelt Prims.is_MkDTuple4

; <Start encoding Prims.is_MkDTuple4>
(declare-fun Prims.is_MkDTuple4 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;((DTuple4 a b c d) -> Tot bool)
(declare-fun Typ_fun_2019 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2019 kinding
(assert (HasKind Typ_fun_2019
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2019)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2019)))))
;;;;;;;;;;;;;;;;Typ_fun_2019 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2019)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasType @x5
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2019)))))
(declare-fun Prims.is_MkDTuple4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2021
(Term_constr_id Prims.is_MkDTuple4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkDTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.is_MkDTuple4 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.is_MkDTuple4@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_MkDTuple4@tok
Typ_fun_2019))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.is_MkDTuple4 @a0
@a1
@a2
@a3
@x4)
Prims.bool))
  
:pattern ((Prims.is_MkDTuple4 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.is_MkDTuple4 @a0
@a1
@a2
@a3
@x4)
(BoxBool (is-Prims.MkDTuple4 @x4)))
  
:pattern ((Prims.is_MkDTuple4 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.is_MkDTuple4>

; encoding sigelt Prims.MkDTuple4.a

; <Start encoding Prims.MkDTuple4.a>
(declare-fun Prims.MkDTuple4.a (Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple4.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2029
(Type_constr_id Prims.MkDTuple4.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.a@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.a@tok
@a0)
@a1)
@a2)
@a3)
@x4))

:pattern ((Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasKind (Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)
Kind_type))
  
:pattern ((Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4_a @x4))
  
:pattern ((Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkDTuple4.a>

; encoding sigelt Prims.MkDTuple4.b

; <Start encoding Prims.MkDTuple4.b>
(declare-fun Prims.MkDTuple4.b (Type Type Type Type Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple4.b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2041
(Type_constr_id Prims.MkDTuple4.b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.b@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
(Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.b@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5))

:pattern ((Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3))
(HasType @x5
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)))
(HasKind (Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5)
Kind_type))
  
:pattern ((Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (= (Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5)
(ApplyTE (Prims.MkDTuple4_b @x4)
@x5))
  
:pattern ((Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5)))))

; </end encoding Prims.MkDTuple4.b>

; encoding sigelt Prims.MkDTuple4.c

; <Start encoding Prims.MkDTuple4.c>
(declare-fun Prims.MkDTuple4.c (Type Type Type Type Term Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple4.c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2055
(Type_constr_id Prims.MkDTuple4.c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.c@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
(Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.c@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6))

:pattern ((Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.c@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3))
(HasType @x5
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4))
(HasType @x6
(Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5)))
(HasKind (Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6)
Kind_type))
  
:pattern ((Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (= (Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6)
(ApplyTE (ApplyTE (Prims.MkDTuple4_c @x4)
@x5)
@x6))
  
:pattern ((Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6)))))

; </end encoding Prims.MkDTuple4.c>

; encoding sigelt Prims.MkDTuple4.d

; <Start encoding Prims.MkDTuple4.d>
(declare-fun Prims.MkDTuple4.d (Type Type Type Type Term Term Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkDTuple4.d@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2072
(Type_constr_id Prims.MkDTuple4.d@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.d@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
@x7)
(Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkDTuple4.d@tok
@a0)
@a1)
@a2)
@a3)
@x4)
@x5)
@x6)
@x7))

:pattern ((Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.d@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3))
(HasType @x5
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4))
(HasType @x6
(Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
@x5))
(HasType @x7
(Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
@x5
@x6)))
(HasKind (Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)
Kind_type))
  
:pattern ((Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (= (Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)
(ApplyTE (ApplyTE (ApplyTE (Prims.MkDTuple4_d @x4)
@x5)
@x6)
@x7))
  
:pattern ((Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
@x5
@x6
@x7)))))

; </end encoding Prims.MkDTuple4.d>

; encoding sigelt Prims.MkDTuple4._1

; <Start encoding Prims.MkDTuple4._1>
(declare-fun Prims.MkDTuple4._1 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (a projectee))
(declare-fun Typ_fun_2087 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2087 kinding
(assert (HasKind Typ_fun_2087
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2087)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2087)))))
;;;;;;;;;;;;;;;;Typ_fun_2087 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2087)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasType @x5
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple4.a @a1
@a2
@a3
@a4
@x5)))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2087)))))
(declare-fun Prims.MkDTuple4._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2089
(Term_constr_id Prims.MkDTuple4._1@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._1@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._1@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple4._1@tok
Typ_fun_2087))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)))
  
:pattern ((Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4__1 @x4))
  
:pattern ((Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkDTuple4._1>

; encoding sigelt Prims.MkDTuple4._2

; <Start encoding Prims.MkDTuple4._2>
(declare-fun Prims.MkDTuple4._2 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (b projectee (_1 projectee)))
(declare-fun Typ_fun_2106 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2106 kinding
(assert (HasKind Typ_fun_2106
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2106)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2106)))))
;;;;;;;;;;;;;;;;Typ_fun_2106 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2106)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasType @x5
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple4.b @a1
@a2
@a3
@a4
@x5
(Prims.MkDTuple4._1 @a1
@a2
@a3
@a4
@x5))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2106)))))
(declare-fun Prims.MkDTuple4._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2108
(Term_constr_id Prims.MkDTuple4._2@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._2@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._2@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple4._2@tok
Typ_fun_2106))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
(Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4))))
  
:pattern ((Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4__2 @x4))
  
:pattern ((Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkDTuple4._2>

; encoding sigelt Prims.MkDTuple4._3

; <Start encoding Prims.MkDTuple4._3>
(declare-fun Prims.MkDTuple4._3 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (c projectee (_1 projectee) (_2 projectee)))
(declare-fun Typ_fun_2127 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2127 kinding
(assert (HasKind Typ_fun_2127
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2127)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2127)))))
;;;;;;;;;;;;;;;;Typ_fun_2127 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2127)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasType @x5
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple4.c @a1
@a2
@a3
@a4
@x5
(Prims.MkDTuple4._1 @a1
@a2
@a3
@a4
@x5)
(Prims.MkDTuple4._2 @a1
@a2
@a3
@a4
@x5))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2127)))))
(declare-fun Prims.MkDTuple4._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2129
(Term_constr_id Prims.MkDTuple4._3@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._3@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple4._3 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._3@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple4._3@tok
Typ_fun_2127))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4._3 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4.c @a0
@a1
@a2
@a3
@x4
(Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4))))
  
:pattern ((Prims.MkDTuple4._3 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkDTuple4._3 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4__3 @x4))
  
:pattern ((Prims.MkDTuple4._3 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkDTuple4._3>

; encoding sigelt Prims.MkDTuple4._4

; <Start encoding Prims.MkDTuple4._4>
(declare-fun Prims.MkDTuple4._4 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (d projectee (_1 projectee) (_2 projectee) (_3 projectee)))
(declare-fun Typ_fun_2150 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2150 kinding
(assert (HasKind Typ_fun_2150
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2150)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2150)))))
;;;;;;;;;;;;;;;;Typ_fun_2150 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2150)
(forall ((@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasKind @a3
(Kind_arrow_1858 @a2
@a1))
(HasKind @a4
(Kind_arrow_1987 @a3
@a2
@a1))
(HasType @x5
(Prims.DTuple4 @a1
@a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple4.d @a1
@a2
@a3
@a4
@x5
(Prims.MkDTuple4._1 @a1
@a2
@a3
@a4
@x5)
(Prims.MkDTuple4._2 @a1
@a2
@a3
@a4
@x5)
(Prims.MkDTuple4._3 @a1
@a2
@a3
@a4
@x5))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x0
@a1)
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2150)))))
(declare-fun Prims.MkDTuple4._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2152
(Term_constr_id Prims.MkDTuple4._4@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._4@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkDTuple4._4 @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET Prims.MkDTuple4._4@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.MkDTuple4._4@tok
Typ_fun_2150))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasKind @a2
(Kind_arrow_1858 @a1
@a0))
(HasKind @a3
(Kind_arrow_1987 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4._4 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4.d @a0
@a1
@a2
@a3
@x4
(Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4._2 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4._3 @a0
@a1
@a2
@a3
@x4))))
  
:pattern ((Prims.MkDTuple4._4 @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkDTuple4._4 @a0
@a1
@a2
@a3
@x4)
(Prims.MkDTuple4__4 @x4))
  
:pattern ((Prims.MkDTuple4._4 @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkDTuple4._4>

; encoding sigelt Prims.as_requires

; <Start encoding Prims.as_requires>
;;;;;;;;;;;;;;;;((a -> Type) -> Type)
(declare-fun Kind_arrow_2158 (Type) Kind)
;;;;;;;;;;;;;;;;Kind_arrow_2158 interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (HasKind @a0
(Kind_arrow_2158 @a1))
(and (is-Kind_arrow (PreKind @a0))
(forall ((@a2 Type))
 (! (implies (HasKind @a2
(Kind_arrow_136 @a1))
(HasKind (ApplyTT @a0
@a2)
Kind_type))
  
:pattern ((ApplyTT @a0
@a2))))))
  
:pattern ((HasKind @a0
(Kind_arrow_2158 @a1))))))
(declare-fun Prims.as_requires (Type Type) Type)
(declare-fun Prims.as_requires@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2159
(Type_constr_id Prims.as_requires@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyTT (ApplyTT Prims.as_requires@tok
@a0)
@a1)
(Prims.as_requires @a0
@a1))
  
:pattern ((ApplyTT (ApplyTT Prims.as_requires@tok
@a0)
@a1)))))
(declare-fun Typ_lam_2160 (Type) Type)
;;;;;;;;;;;;;;;;Typ_lam interpretation
(assert (forall ((@x0 Term) (@a1 Type))
 (! (implies (HasType @x0
@a1)
(= (ApplyTE (Typ_lam_2160 @a1)
@x0)
Prims.True))
  
:pattern ((ApplyTE (Typ_lam_2160 @a1)
@x0)))))
;;;;;;;;;;;;;;;;Typ_lam kinding
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_lam_2160 @a0)
(Kind_arrow_136 @a0))
  
:pattern ((Typ_lam_2160 @a0)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2158 @a0)))
(= (Prims.as_requires @a0
@a1)
(ApplyTT @a1
(Typ_lam_2160 @a0))))
  
:pattern ((Prims.as_requires @a0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2158 @a0)))
(HasKind (Prims.as_requires @a0
@a1)
Kind_type))
  
:pattern ((Prims.as_requires @a0
@a1)))))

; </end encoding Prims.as_requires>

; encoding sigelt Prims.as_ensures

; <Start encoding Prims.as_ensures>
(declare-fun Prims.as_ensures (Type Type Term) Type)
(declare-fun Prims.as_ensures@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2166
(Type_constr_id Prims.as_ensures@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.as_ensures@tok
@a0)
@a1)
@x2)
(Prims.as_ensures @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.as_ensures@tok
@a0)
@a1)
@x2)))))
(declare-fun Typ_lam_2167 (Term Type) Type)
;;;;;;;;;;;;;;;;Typ_lam interpretation
(assert (forall ((@x0 Term) (@x1 Term) (@a2 Type))
 (! (implies (HasType @x0
@a2)
(= (ApplyTE (Typ_lam_2167 @x1
@a2)
@x0)
(Prims.l_not (Prims.b2t (Prims.op_Equality @a2
@x0
@x1)))))
  
:pattern ((ApplyTE (Typ_lam_2167 @x1
@a2)
@x0)))))
;;;;;;;;;;;;;;;;Typ_lam kinding
(assert (forall ((@x0 Term) (@a1 Type))
 (! (HasKind (Typ_lam_2167 @x0
@a1)
(Kind_arrow_136 @a1))
  
:pattern ((Typ_lam_2167 @x0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2158 @a0))
(HasType @x2
@a0))
(= (Valid (Prims.as_ensures @a0
@a1
@x2))
(not (Valid (ApplyTT @a1
(Typ_lam_2167 @x2
@a0))))))
  
:pattern ((Valid (Prims.as_ensures @a0
@a1
@x2))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2158 @a0))
(HasType @x2
@a0))
(HasKind (Prims.as_ensures @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.as_ensures @a0
@a1
@x2)))))

; </end encoding Prims.as_ensures>

; encoding sigelt Prims.fst

; <Skipped Prims.fst/>

; encoding sigelt let Prims.fst : ((Tuple2 'a 'b) -> Tot 'a)

; <Start encoding Prims.fst>
(declare-fun Prims.fst (Type Type Term) Term)
(declare-fun Prims.fst@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2170
(Term_constr_id Prims.fst@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.fst@tok
@a0)
@a1)
@x2)
(Prims.fst @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.fst@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.fst@tok
Typ_fun_1540))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.fst @a0
@a1
@x2)
@a0))
  
:pattern ((Prims.fst @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for Prims.fst
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(= (Prims.fst @a0
@a1
@x2)
(Prims.MkTuple2._1 @a0
@a1
@x2)))
  
:pattern ((Prims.fst @a0
@a1
@x2)))))

; </end encoding Prims.fst>

; encoding sigelt Prims.snd

; <Skipped Prims.snd/>

; encoding sigelt let Prims.snd : ((Tuple2 'a 'b) -> Tot 'b)

; <Start encoding Prims.snd>
(declare-fun Prims.snd (Type Type Term) Term)
(declare-fun Prims.snd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2172
(Term_constr_id Prims.snd@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.snd@tok
@a0)
@a1)
@x2)
(Prims.snd @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.snd@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.snd@tok
Typ_fun_1544))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.snd @a0
@a1
@x2)
@a1))
  
:pattern ((Prims.snd @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for Prims.snd
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(= (Prims.snd @a0
@a1
@x2)
(Prims.MkTuple2._2 @a0
@a1
@x2)))
  
:pattern ((Prims.snd @a0
@a1
@x2)))))

; </end encoding Prims.snd>

; encoding sigelt Prims.dfst

; <Skipped Prims.dfst/>

; encoding sigelt let Prims.dfst : ((DTuple2 a b) -> Tot a)

; <Start encoding Prims.dfst>
(declare-fun Prims.dfst (Type Type Term) Term)
;;;;;;;;;;;;;;;;((DTuple2 a b) -> Tot a)
(declare-fun Typ_fun_2180 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2180 kinding
(assert (HasKind Typ_fun_2180
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2180)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2180)))))
;;;;;;;;;;;;;;;;Typ_fun_2180 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2180)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasType @x3
(Prims.DTuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@a1))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2180)))))
(declare-fun Prims.dfst@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2182
(Term_constr_id Prims.dfst@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.dfst@tok
@a0)
@a1)
@x2)
(Prims.dfst @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.dfst@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.dfst@tok
Typ_fun_2180))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.dfst @a0
@a1
@x2)
@a0))
  
:pattern ((Prims.dfst @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for Prims.dfst
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(= (Prims.dfst @a0
@a1
@x2)
(Prims.MkDTuple2._1 @a0
@a1
@x2)))
  
:pattern ((Prims.dfst @a0
@a1
@x2)))))

; </end encoding Prims.dfst>

; encoding sigelt Prims.dsnd

; <Skipped Prims.dsnd/>

; encoding sigelt let Prims.dsnd : (t:(DTuple2 a b) -> Tot (b (_1 t)))

; <Start encoding Prims.dsnd>
(declare-fun Prims.dsnd (Type Type Term) Term)
;;;;;;;;;;;;;;;;(t:(DTuple2 a b) -> Tot (b (_1 t)))
(declare-fun Typ_fun_2194 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2194 kinding
(assert (HasKind Typ_fun_2194
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2194)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2194)))))
;;;;;;;;;;;;;;;;Typ_fun_2194 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2194)
(forall ((@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
(Kind_arrow_136 @a1))
(HasType @x3
(Prims.DTuple2 @a1
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
(ApplyTE @a2
(Prims.MkDTuple2._1 @a1
@a2
@x3))))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2194)))))
(declare-fun Prims.dsnd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2196
(Term_constr_id Prims.dsnd@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyET Prims.dsnd@tok
@a0)
@a1)
@x2)
(Prims.dsnd @a0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyET Prims.dsnd@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.dsnd@tok
Typ_fun_2194))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.dsnd @a0
@a1
@x2)
(ApplyTE @a1
(Prims.MkDTuple2._1 @a0
@a1
@x2))))
  
:pattern ((Prims.dsnd @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for Prims.dsnd
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_136 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(= (Prims.dsnd @a0
@a1
@x2)
(Prims.MkDTuple2._2 @a0
@a1
@x2)))
  
:pattern ((Prims.dsnd @a0
@a1
@x2)))))

; </end encoding Prims.dsnd>

; encoding sigelt Prims.Let

; <Start encoding Prims.Let>
(declare-fun Prims.Let (Type Term Type) Type)
(declare-fun Prims.Let@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2199
(Type_constr_id Prims.Let@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term) (@a2 Type))
 (! (= (ApplyTT (ApplyTE (ApplyTT Prims.Let@tok
@a0)
@x1)
@a2)
(Prims.Let @a0
@x1
@a2))
  
:pattern ((ApplyTT (ApplyTE (ApplyTT Prims.Let@tok
@a0)
@x1)
@a2)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@x1 Term) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasKind @a2
(Kind_arrow_136 @a0)))
(= (Prims.Let @a0
@x1
@a2)
(ApplyTE @a2
@x1)))
  
:pattern ((Prims.Let @a0
@x1
@a2)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@x1 Term) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasKind @a2
(Kind_arrow_136 @a0)))
(HasKind (Prims.Let @a0
@x1
@a2)
Kind_type))
  
:pattern ((Prims.Let @a0
@x1
@a2)))))

; </end encoding Prims.Let>

; encoding sigelt Prims.InductionHyp

; <Start encoding Prims.InductionHyp>
(declare-fun Prims.InductionHyp (Type Term Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.InductionHyp@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2201
(Type_constr_id Prims.InductionHyp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term) (@a2 Type))
 (! (= (ApplyTT (ApplyTE (ApplyTT Prims.InductionHyp@tok
@a0)
@x1)
@a2)
(Prims.InductionHyp @a0
@x1
@a2))
  
:pattern ((ApplyTT (ApplyTE (ApplyTT Prims.InductionHyp@tok
@a0)
@x1)
@a2))

:pattern ((Prims.InductionHyp @a0
@x1
@a2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.InductionHyp@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasKind @a2
Kind_type))
(HasKind (Prims.InductionHyp @a0
@x1
@a2)
Kind_type))
  
:pattern ((Prims.InductionHyp @a0
@x1
@a2)))))

; </end encoding Prims.InductionHyp>

; encoding sigelt Prims.by_induction_on

; <Start encoding Prims.by_induction_on>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.by_induction_on (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.by_induction_on@tok () Term)

; </end encoding Prims.by_induction_on>

; encoding sigelt Prims.Using

; <Start encoding Prims.Using>
(declare-fun Prims.Using (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Using@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2203
(Type_constr_id Prims.Using@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Using@tok
@a0)
@a1)
@x2)
(Prims.Using @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Using@tok
@a0)
@a1)
@x2))

:pattern ((Prims.Using @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Using@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
@a0))
(HasKind (Prims.Using @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Using @a0
@a1
@x2)))))

; </end encoding Prims.Using>

; encoding sigelt Prims.using

; <Start encoding Prims.using>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.using (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.using@tok () Term)

; </end encoding Prims.using>

; encoding sigelt Prims._assume

; <Start encoding Prims._assume>
(declare-fun Prims._assume (Type Term) Term)
(declare-fun Non_total_Typ_fun_2204 () Type)
(assert (HasKind Non_total_Typ_fun_2204
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Non_total_Typ_fun_2204)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2204)))))
(declare-fun Prims._assume@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2206
(Term_constr_id Prims._assume@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims._assume@tok
@a0)
@x1)
(Prims._assume @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims._assume@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims._assume@tok
Non_total_Typ_fun_2204))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
Prims.unit))
(HasType (Prims._assume @a0
@x1)
Prims.unit))
  
:pattern ((Prims._assume @a0
@x1)))))

; </end encoding Prims._assume>

; encoding sigelt Prims.admit

; <Start encoding Prims.admit>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.admit (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.admit@tok () Term)

; </end encoding Prims.admit>

; encoding sigelt Prims.magic

; <Start encoding Prims.magic>
(declare-fun Prims.magic (Type Term) Term)
;;;;;;;;;;;;;;;;(unit -> Tot a)
(declare-fun Typ_fun_2208 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2208 kinding
(assert (HasKind Typ_fun_2208
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2208)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2208)))))
;;;;;;;;;;;;;;;;Typ_fun_2208 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2208)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
Prims.unit))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
@a1))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2208)))))
(declare-fun Prims.magic@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2210
(Term_constr_id Prims.magic@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.magic@tok
@a0)
@x1)
(Prims.magic @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.magic@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.magic@tok
Typ_fun_2208))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
Prims.unit))
(HasType (Prims.magic @a0
@x1)
@a0))
  
:pattern ((Prims.magic @a0
@x1)))))

; </end encoding Prims.magic>

; encoding sigelt Prims.admitP

; <Start encoding Prims.admitP>
(declare-fun Prims.admitP (Type) Term)
(declare-fun Non_total_Typ_fun_2211 () Type)
(assert (HasKind Non_total_Typ_fun_2211
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Non_total_Typ_fun_2211)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2211)))))
(declare-fun Prims.admitP@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2213
(Term_constr_id Prims.admitP@tok)))
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.admitP@tok
@a0)
(Prims.admitP @a0))
  
:pattern ((ApplyET Prims.admitP@tok
@a0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.admitP@tok
Non_total_Typ_fun_2211))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasType (Prims.admitP @a0)
Prims.unit))
  
:pattern ((Prims.admitP @a0)))))

; </end encoding Prims.admitP>

; encoding sigelt Prims._assert

; <Start encoding Prims._assert>
(declare-fun Prims._assert (Type Term) Term)
(declare-fun Non_total_Typ_fun_2214 () Type)
(assert (HasKind Non_total_Typ_fun_2214
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Non_total_Typ_fun_2214)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2214)))))
(declare-fun Prims._assert@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2216
(Term_constr_id Prims._assert@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims._assert@tok
@a0)
@x1)
(Prims._assert @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims._assert@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims._assert@tok
Non_total_Typ_fun_2214))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
Prims.unit))
(HasType (Prims._assert @a0
@x1)
Prims.unit))
  
:pattern ((Prims._assert @a0
@x1)))))

; </end encoding Prims._assert>

; encoding sigelt Prims.cut

; <Start encoding Prims.cut>
(declare-fun Prims.cut (Type) Term)
(declare-fun Non_total_Typ_fun_2217 () Type)
(assert (HasKind Non_total_Typ_fun_2217
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Non_total_Typ_fun_2217)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2217)))))
(declare-fun Prims.cut@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2219
(Term_constr_id Prims.cut@tok)))
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.cut@tok
@a0)
(Prims.cut @a0))
  
:pattern ((ApplyET Prims.cut@tok
@a0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.cut@tok
Non_total_Typ_fun_2217))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasType (Prims.cut @a0)
Prims.unit))
  
:pattern ((Prims.cut @a0)))))

; </end encoding Prims.cut>

; encoding sigelt Prims.qintro

; <Start encoding Prims.qintro>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.qintro (Type Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.qintro@tok () Term)

; </end encoding Prims.qintro>

; encoding sigelt Prims.ghost_lemma

; <Start encoding Prims.ghost_lemma>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.ghost_lemma (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.ghost_lemma@tok () Term)

; </end encoding Prims.ghost_lemma>

; encoding sigelt Prims.raise

; <Start encoding Prims.raise>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.raise (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.raise@tok () Term)

; </end encoding Prims.raise>

; encoding sigelt Prims.ignore

; <Skipped Prims.ignore/>

; encoding sigelt let Prims.ignore : ('a -> Tot unit)

; <Start encoding Prims.ignore>
(declare-fun Prims.ignore (Type Term) Term)
;;;;;;;;;;;;;;;;('a -> Tot unit)
(declare-fun Typ_fun_2238 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2238 kinding
(assert (HasKind Typ_fun_2238
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2238)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2238)))))
;;;;;;;;;;;;;;;;Typ_fun_2238 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2238)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.unit))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2238)))))
(declare-fun Prims.ignore@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2240
(Term_constr_id Prims.ignore@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.ignore@tok
@a0)
@x1)
(Prims.ignore @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.ignore@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.ignore@tok
Typ_fun_2238))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(HasType (Prims.ignore @a0
@x1)
Prims.unit))
  
:pattern ((Prims.ignore @a0
@x1)))))
;;;;;;;;;;;;;;;;Equation for Prims.ignore
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(= (Prims.ignore @a0
@x1)
Term_unit))
  
:pattern ((Prims.ignore @a0
@x1)))))

; </end encoding Prims.ignore>

; encoding sigelt Prims.nat

; <Start encoding Prims.nat>
(declare-fun Prims.nat () Type)
(declare-fun Prims.nat@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.nat@tok
Prims.nat))
(declare-fun Typ_refine_2242 () Type)
(assert (HasKind Typ_refine_2242
Kind_type))
;;;;;;;;;;;;;;;;i:int{(i >= 0)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_2242)
(and (HasTypeFuel @u0
@x1
Prims.int)
(>= (BoxInt_proj_0 @x1)
(BoxInt_proj_0 (BoxInt 0)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2242)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.nat
Typ_refine_2242))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.nat
Kind_type))

; </end encoding Prims.nat>

; encoding sigelt Prims.pos

; <Start encoding Prims.pos>
(declare-fun Prims.pos () Type)
(declare-fun Prims.pos@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.pos@tok
Prims.pos))
(declare-fun Typ_refine_2244 () Type)
(assert (HasKind Typ_refine_2244
Kind_type))
;;;;;;;;;;;;;;;;i:int{(i > 0)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_2244)
(and (HasTypeFuel @u0
@x1
Prims.int)
(> (BoxInt_proj_0 @x1)
(BoxInt_proj_0 (BoxInt 0)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2244)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.pos
Typ_refine_2244))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.pos
Kind_type))

; </end encoding Prims.pos>

; encoding sigelt Prims.nonzero

; <Start encoding Prims.nonzero>
(declare-fun Prims.nonzero () Type)
(declare-fun Prims.nonzero@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.nonzero@tok
Prims.nonzero))
(declare-fun Typ_refine_2246 () Type)
(assert (HasKind Typ_refine_2246
Kind_type))
;;;;;;;;;;;;;;;;i:int{(i <> 0)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_2246)
(and (HasTypeFuel @u0
@x1
Prims.int)
(not (= @x1
(BoxInt 0)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2246)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.nonzero
Typ_refine_2246))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (HasKind Prims.nonzero
Kind_type))

; </end encoding Prims.nonzero>

; encoding sigelt Prims.op_Modulus

; <Start encoding Prims.op_Modulus>
(declare-fun Prims.op_Modulus (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Modulus @x0
@x1)
(BoxInt (mod (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_Modulus @x0
@x1)))))

; </end encoding Prims.op_Modulus>

; encoding sigelt Prims.op_Division

; <Start encoding Prims.op_Division>
(declare-fun Prims.op_Division (Term Term) Term)
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (Prims.op_Division @x0
@x1)
(BoxInt (div (BoxInt_proj_0 @x0)
(BoxInt_proj_0 @x1))))
  
:pattern ((Prims.op_Division @x0
@x1)))))

; </end encoding Prims.op_Division>

; encoding sigelt Prims.string_of_bool

; <Start encoding Prims.string_of_bool>
(declare-fun Prims.string_of_bool (Term) Term)
;;;;;;;;;;;;;;;;(bool -> Tot string)
(declare-fun Typ_fun_2248 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2248 kinding
(assert (HasKind Typ_fun_2248
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2248)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2248)))))
;;;;;;;;;;;;;;;;Typ_fun_2248 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2248)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Prims.bool)
(HasType (ApplyEE @x0
@x1)
Prims.string))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2248)))))
(declare-fun Prims.string_of_bool@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2250
(Term_constr_id Prims.string_of_bool@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.string_of_bool@tok
@x0)
(Prims.string_of_bool @x0))
  
:pattern ((ApplyEE Prims.string_of_bool@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.string_of_bool@tok
Typ_fun_2248))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.bool)
(HasType (Prims.string_of_bool @x0)
Prims.string))
  
:pattern ((Prims.string_of_bool @x0)))))

; </end encoding Prims.string_of_bool>

; encoding sigelt Prims.string_of_int

; <Start encoding Prims.string_of_int>
(declare-fun Prims.string_of_int (Term) Term)
;;;;;;;;;;;;;;;;(int -> Tot string)
(declare-fun Typ_fun_2252 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2252 kinding
(assert (HasKind Typ_fun_2252
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2252)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2252)))))
;;;;;;;;;;;;;;;;Typ_fun_2252 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2252)
(forall ((@x1 Term))
 (! (implies (HasType @x1
Prims.int)
(HasType (ApplyEE @x0
@x1)
Prims.string))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2252)))))
(declare-fun Prims.string_of_int@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2254
(Term_constr_id Prims.string_of_int@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.string_of_int@tok
@x0)
(Prims.string_of_int @x0))
  
:pattern ((ApplyEE Prims.string_of_int@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.string_of_int@tok
Typ_fun_2252))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Prims.int)
(HasType (Prims.string_of_int @x0)
Prims.string))
  
:pattern ((Prims.string_of_int @x0)))))

; </end encoding Prims.string_of_int>

; Externals for interface FStar.Set

; <Skipped />

; <Start encoding FStar.Set.set>

; <start constructor FStar.Set.set>
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Set.set (Type) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 2289
(Type_constr_id (FStar.Set.set @a0)))
  
:pattern ((FStar.Set.set @a0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Set.set@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (FStar.Set.set@a0 (FStar.Set.set @a0))
@a0)
  
:pattern ((FStar.Set.set @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Set.set ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2289)
(= @a0
(FStar.Set.set (FStar.Set.set@a0 @a0)))))

; </end constructor FStar.Set.set>
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Set.set@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2290
(Type_constr_id FStar.Set.set@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT FStar.Set.set@tok
@a0)
(FStar.Set.set @a0))
  
:pattern ((ApplyTT FStar.Set.set@tok
@a0))

:pattern ((FStar.Set.set @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind FStar.Set.set@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (FStar.Set.set @a0)
Kind_type))
  
:pattern ((FStar.Set.set @a0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(FStar.Set.set @a2))
(= (FStar.Set.set @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(FStar.Set.set @a2))))))

; </end encoding FStar.Set.set>

; <Start encoding FStar.Set.mem>
(declare-fun FStar.Set.mem (Type Term Term) Term)
;;;;;;;;;;;;;;;;(a -> (set a) -> Tot bool)
(declare-fun Typ_fun_2294 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2294 kinding
(assert (HasKind Typ_fun_2294
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2294)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2294)))))
;;;;;;;;;;;;;;;;Typ_fun_2294 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2294)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1)
(HasType @x3
(FStar.Set.set @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2294)))))
(declare-fun FStar.Set.mem@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2296
(Term_constr_id FStar.Set.mem@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Set.mem@tok
@a0)
@x1)
@x2)
(FStar.Set.mem @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Set.mem@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.mem@tok
Typ_fun_2294))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasType @x2
(FStar.Set.set @a0)))
(HasType (FStar.Set.mem @a0
@x1
@x2)
Prims.bool))
  
:pattern ((FStar.Set.mem @a0
@x1
@x2)))))

; </end encoding FStar.Set.mem>

; <Start encoding FStar.Set.empty>
(declare-fun FStar.Set.empty (Type) Term)
;;;;;;;;;;;;;;;;( -> Tot (set a))
(declare-fun Typ_fun_2298 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2298 kinding
(assert (HasKind Typ_fun_2298
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2298)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2298)))))
;;;;;;;;;;;;;;;;Typ_fun_2298 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2298)
(forall ((@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasType (ApplyET @x0
@a1)
(FStar.Set.set @a1)))
  
:pattern ((ApplyET @x0
@a1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2298)))))
(declare-fun FStar.Set.empty@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2300
(Term_constr_id FStar.Set.empty@tok)))
(assert (forall ((@a0 Type))
 (! (= (ApplyET FStar.Set.empty@tok
@a0)
(FStar.Set.empty @a0))
  
:pattern ((ApplyET FStar.Set.empty@tok
@a0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.empty@tok
Typ_fun_2298))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasType (FStar.Set.empty @a0)
(FStar.Set.set @a0)))
  
:pattern ((FStar.Set.empty @a0)))))

; </end encoding FStar.Set.empty>

; <Start encoding FStar.Set.singleton>
(declare-fun FStar.Set.singleton (Type Term) Term)
;;;;;;;;;;;;;;;;(a -> Tot (set a))
(declare-fun Typ_fun_2302 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2302 kinding
(assert (HasKind Typ_fun_2302
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2302)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2302)))))
;;;;;;;;;;;;;;;;Typ_fun_2302 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2302)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(FStar.Set.set @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2302)))))
(declare-fun FStar.Set.singleton@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2304
(Term_constr_id FStar.Set.singleton@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET FStar.Set.singleton@tok
@a0)
@x1)
(FStar.Set.singleton @a0
@x1))
  
:pattern ((ApplyEE (ApplyET FStar.Set.singleton@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.singleton@tok
Typ_fun_2302))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(HasType (FStar.Set.singleton @a0
@x1)
(FStar.Set.set @a0)))
  
:pattern ((FStar.Set.singleton @a0
@x1)))))

; </end encoding FStar.Set.singleton>

; <Start encoding FStar.Set.union>
(declare-fun FStar.Set.union (Type Term Term) Term)
;;;;;;;;;;;;;;;;((set a) -> (set a) -> Tot (set a))
(declare-fun Typ_fun_2306 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2306 kinding
(assert (HasKind Typ_fun_2306
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2306)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2306)))))
;;;;;;;;;;;;;;;;Typ_fun_2306 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2306)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Set.set @a1))
(HasType @x3
(FStar.Set.set @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
(FStar.Set.set @a1)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2306)))))
(declare-fun FStar.Set.union@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2308
(Term_constr_id FStar.Set.union@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Set.union@tok
@a0)
@x1)
@x2)
(FStar.Set.union @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Set.union@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.union@tok
Typ_fun_2306))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(HasType (FStar.Set.union @a0
@x1
@x2)
(FStar.Set.set @a0)))
  
:pattern ((FStar.Set.union @a0
@x1
@x2)))))

; </end encoding FStar.Set.union>

; <Start encoding FStar.Set.intersect>
(declare-fun FStar.Set.intersect (Type Term Term) Term)
(declare-fun FStar.Set.intersect@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2310
(Term_constr_id FStar.Set.intersect@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Set.intersect@tok
@a0)
@x1)
@x2)
(FStar.Set.intersect @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Set.intersect@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.intersect@tok
Typ_fun_2306))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(HasType (FStar.Set.intersect @a0
@x1
@x2)
(FStar.Set.set @a0)))
  
:pattern ((FStar.Set.intersect @a0
@x1
@x2)))))

; </end encoding FStar.Set.intersect>

; <Start encoding FStar.Set.complement>
(declare-fun FStar.Set.complement (Type Term) Term)
;;;;;;;;;;;;;;;;((set a) -> Tot (set a))
(declare-fun Typ_fun_2312 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2312 kinding
(assert (HasKind Typ_fun_2312
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2312)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2312)))))
;;;;;;;;;;;;;;;;Typ_fun_2312 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2312)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Set.set @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(FStar.Set.set @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2312)))))
(declare-fun FStar.Set.complement@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2314
(Term_constr_id FStar.Set.complement@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET FStar.Set.complement@tok
@a0)
@x1)
(FStar.Set.complement @a0
@x1))
  
:pattern ((ApplyEE (ApplyET FStar.Set.complement@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.complement@tok
Typ_fun_2312))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0)))
(HasType (FStar.Set.complement @a0
@x1)
(FStar.Set.set @a0)))
  
:pattern ((FStar.Set.complement @a0
@x1)))))

; </end encoding FStar.Set.complement>

; <Start encoding FStar.Set.subset>
(declare-fun FStar.Set.subset (Type Term Term) Term)
;;;;;;;;;;;;;;;;((set a) -> (set a) -> Tot bool)
(declare-fun Typ_fun_2316 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2316 kinding
(assert (HasKind Typ_fun_2316
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2316)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2316)))))
;;;;;;;;;;;;;;;;Typ_fun_2316 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2316)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Set.set @a1))
(HasType @x3
(FStar.Set.set @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2316)))))
(declare-fun FStar.Set.subset@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2318
(Term_constr_id FStar.Set.subset@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Set.subset@tok
@a0)
@x1)
@x2)
(FStar.Set.subset @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Set.subset@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Set.subset@tok
Typ_fun_2316))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(HasType (FStar.Set.subset @a0
@x1
@x2)
Prims.bool))
  
:pattern ((FStar.Set.subset @a0
@x1
@x2)))))

; </end encoding FStar.Set.subset>

; <Start encoding FStar.Set.mem_empty>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.mem_empty (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.mem_empty@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.mem_empty
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(not (BoxBool_proj_0 (FStar.Set.mem @a0
@x1
(FStar.Set.empty @a0)))))
  
:pattern ((FStar.Set.mem @a0
@x1
(FStar.Set.empty @a0))))))

; </end encoding FStar.Set.mem_empty>

; <Start encoding FStar.Set.mem_singleton>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.mem_singleton (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.mem_singleton@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.mem_singleton
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasType @x2
@a0))
(= (FStar.Set.mem @a0
@x2
(FStar.Set.singleton @a0
@x1))
(Prims.op_Equality @a0
@x1
@x2)))
  
:pattern ((FStar.Set.mem @a0
@x2
(FStar.Set.singleton @a0
@x1))))))

; </end encoding FStar.Set.mem_singleton>

; <Start encoding FStar.Set.mem_union>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.mem_union (Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.mem_union@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.mem_union
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasType @x2
(FStar.Set.set @a0))
(HasType @x3
(FStar.Set.set @a0)))
(= (FStar.Set.mem @a0
@x1
(FStar.Set.union @a0
@x2
@x3))
(Prims.op_BarBar (FStar.Set.mem @a0
@x1
@x2)
(FStar.Set.mem @a0
@x1
@x3))))
  
:pattern ((FStar.Set.mem @a0
@x1
(FStar.Set.union @a0
@x2
@x3))))))

; </end encoding FStar.Set.mem_union>

; <Start encoding FStar.Set.mem_intersect>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.mem_intersect (Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.mem_intersect@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.mem_intersect
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasType @x2
(FStar.Set.set @a0))
(HasType @x3
(FStar.Set.set @a0)))
(= (FStar.Set.mem @a0
@x1
(FStar.Set.intersect @a0
@x2
@x3))
(Prims.op_AmpAmp (FStar.Set.mem @a0
@x1
@x2)
(FStar.Set.mem @a0
@x1
@x3))))
  
:pattern ((FStar.Set.mem @a0
@x1
(FStar.Set.intersect @a0
@x2
@x3))))))

; </end encoding FStar.Set.mem_intersect>

; <Start encoding FStar.Set.mem_complement>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.mem_complement (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.mem_complement@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.mem_complement
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasType @x2
(FStar.Set.set @a0)))
(= (FStar.Set.mem @a0
@x1
(FStar.Set.complement @a0
@x2))
(Prims.op_Negation (FStar.Set.mem @a0
@x1
@x2))))
  
:pattern ((FStar.Set.mem @a0
@x1
(FStar.Set.complement @a0
@x2))))))

; </end encoding FStar.Set.mem_complement>

; <Start encoding FStar.Set.mem_subset>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.mem_subset (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.mem_subset@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.mem_subset
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (forall ((@x3 Term))
 (implies (and (HasType @x3
@a0)
(BoxBool_proj_0 (FStar.Set.mem @a0
@x3
@x1)))
(BoxBool_proj_0 (FStar.Set.mem @a0
@x3
@x2))));;no pats

(HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(BoxBool_proj_0 (FStar.Set.subset @a0
@x1
@x2)))
  
:pattern ((FStar.Set.subset @a0
@x1
@x2)))))

; </end encoding FStar.Set.mem_subset>

; <Start encoding FStar.Set.subset_mem>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.subset_mem (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.subset_mem@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.subset_mem
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (BoxBool_proj_0 (FStar.Set.subset @a0
@x1
@x2))
(HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(forall ((@x3 Term))
 (implies (and (HasType @x3
@a0)
(BoxBool_proj_0 (FStar.Set.mem @a0
@x3
@x1)))
(BoxBool_proj_0 (FStar.Set.mem @a0
@x3
@x2))));;no pats
)
  
:pattern ((FStar.Set.subset @a0
@x1
@x2)))))

; </end encoding FStar.Set.subset_mem>

; <Start encoding FStar.Set.Equal>

; <start constructor FStar.Set.Equal>
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Set.Equal (Type Term Term) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= 2319
(Type_constr_id (FStar.Set.Equal @a0
@x1
@x2)))
  
:pattern ((FStar.Set.Equal @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Set.Equal@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (FStar.Set.Equal@a0 (FStar.Set.Equal @a0
@x1
@x2))
@a0)
  
:pattern ((FStar.Set.Equal @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Set.Equal@x1 (Type) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (FStar.Set.Equal@x1 (FStar.Set.Equal @a0
@x1
@x2))
@x1)
  
:pattern ((FStar.Set.Equal @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Set.Equal@x2 (Type) Term)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (FStar.Set.Equal@x2 (FStar.Set.Equal @a0
@x1
@x2))
@x2)
  
:pattern ((FStar.Set.Equal @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Set.Equal ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2319)
(= @a0
(FStar.Set.Equal (FStar.Set.Equal@a0 @a0)
(FStar.Set.Equal@x1 @a0)
(FStar.Set.Equal@x2 @a0)))))

; </end constructor FStar.Set.Equal>
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Set.Equal@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2320
(Type_constr_id FStar.Set.Equal@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT FStar.Set.Equal@tok
@a0)
@x1)
@x2)
(FStar.Set.Equal @a0
@x1
@x2))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT FStar.Set.Equal@tok
@a0)
@x1)
@x2))

:pattern ((FStar.Set.Equal @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind FStar.Set.Equal@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(HasKind (FStar.Set.Equal @a0
@x1
@x2)
Kind_type))
  
:pattern ((FStar.Set.Equal @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (HasTypeFuel @u1
@x0
(FStar.Set.Equal @a2
@x3
@x4))
(= (FStar.Set.Equal @a2
@x3
@x4)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(FStar.Set.Equal @a2
@x3
@x4))))))

; </end encoding FStar.Set.Equal>

; <Start encoding FStar.Set.lemma_equal_intro>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.lemma_equal_intro (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.lemma_equal_intro@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.lemma_equal_intro
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (forall ((@x3 Term))
 (implies (HasType @x3
@a0)
(= (FStar.Set.mem @a0
@x3
@x1)
(FStar.Set.mem @a0
@x3
@x2))));;no pats

(HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(Valid (FStar.Set.Equal @a0
@x1
@x2)))
  
:pattern ((Valid (FStar.Set.Equal @a0
@x1
@x2))))))

; </end encoding FStar.Set.lemma_equal_intro>

; <Start encoding FStar.Set.lemma_equal_elim>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.lemma_equal_elim (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.lemma_equal_elim@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.lemma_equal_elim
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (Valid (FStar.Set.Equal @a0
@x1
@x2))
(HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(= @x1
@x2))
  
:pattern ((Valid (FStar.Set.Equal @a0
@x1
@x2))))))

; </end encoding FStar.Set.lemma_equal_elim>

; <Start encoding FStar.Set.lemma_equal_refl>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.Set.lemma_equal_refl (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.Set.lemma_equal_refl@tok () Term)
;;;;;;;;;;;;;;;;Lemma: FStar.Set.lemma_equal_refl
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (= @x1
@x2)
(HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set @a0))
(HasType @x2
(FStar.Set.set @a0)))
(Valid (FStar.Set.Equal @a0
@x1
@x2)))
  
:pattern ((Valid (FStar.Set.Equal @a0
@x1
@x2))))))

; </end encoding FStar.Set.lemma_equal_refl>

; End Externals for interface FStar.Set

; Externals for module FStar.Heap

; <Skipped />

; <Start encoding FStar.Heap.heap>

; <start constructor FStar.Heap.heap>
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Heap.heap () Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 2415
(Type_constr_id FStar.Heap.heap)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Heap.heap ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2415)
(= @a0
FStar.Heap.heap)))

; </end constructor FStar.Heap.heap>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind FStar.Heap.heap
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
FStar.Heap.heap)
(= FStar.Heap.heap
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
FStar.Heap.heap)))))

; </end encoding FStar.Heap.heap>

; <Start encoding FStar.Heap.ref>

; <start constructor FStar.Heap.ref>
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Heap.ref (Type) Type)
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 2418
(Type_constr_id (FStar.Heap.ref @a0)))
  
:pattern ((FStar.Heap.ref @a0)))))
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Heap.ref@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (FStar.Heap.ref@a0 (FStar.Heap.ref @a0))
@a0)
  
:pattern ((FStar.Heap.ref @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Heap.ref ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2418)
(= @a0
(FStar.Heap.ref (FStar.Heap.ref@a0 @a0)))))

; </end constructor FStar.Heap.ref>
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Heap.ref@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2419
(Type_constr_id FStar.Heap.ref@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT FStar.Heap.ref@tok
@a0)
(FStar.Heap.ref @a0))
  
:pattern ((ApplyTT FStar.Heap.ref@tok
@a0))

:pattern ((FStar.Heap.ref @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind FStar.Heap.ref@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (FStar.Heap.ref @a0)
Kind_type))
  
:pattern ((FStar.Heap.ref @a0)))))
;;;;;;;;;;;;;;;;ref inversion
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasTypeFuel @u0
@x1
(FStar.Heap.ref @a2))
(is-BoxRef @x1))
  
:pattern ((HasTypeFuel @u0
@x1
(FStar.Heap.ref @a2))))))
;;;;;;;;;;;;;;;;ref typing is injective
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (and (HasTypeFuel @u0
@x1
(FStar.Heap.ref @a2))
(HasTypeFuel @u0
@x1
(FStar.Heap.ref @a3)))
(= @a2
@a3))
  
:pattern ((HasTypeFuel @u0
@x1
(FStar.Heap.ref @a2)) (HasTypeFuel @u0
@x1
(FStar.Heap.ref @a3))))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(FStar.Heap.ref @a2))
(= (FStar.Heap.ref @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(FStar.Heap.ref @a2))))))

; </end encoding FStar.Heap.ref>

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Heap.aref () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun FStar.Heap.Ref (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Heap.Ref_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun FStar.Heap.Ref_r (Term) Term)
;;;;;;;;;;;;;;;;(r:(ref a) -> Tot aref)
(declare-fun Typ_fun_2432 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Ref
(declare-fun FStar.Heap.Ref@tok () Term)

; <Start encoding FStar.Heap.aref>

; <start constructor FStar.Heap.aref>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 2424
(Type_constr_id FStar.Heap.aref)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Heap.aref ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2424)
(= @a0
FStar.Heap.aref)))

; </end constructor FStar.Heap.aref>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind FStar.Heap.aref
Kind_type))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel))
 (! (implies (HasTypeFuel @u1
@x0
FStar.Heap.aref)
(= FStar.Heap.aref
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
FStar.Heap.aref)))))

; </end encoding FStar.Heap.aref>

; <Start encoding FStar.Heap.Ref>

; <start constructor FStar.Heap.Ref>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 2430
(Term_constr_id (FStar.Heap.Ref @a0
@x1)))
  
:pattern ((FStar.Heap.Ref @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (FStar.Heap.Ref_a (FStar.Heap.Ref @a0
@x1))
@a0)
  
:pattern ((FStar.Heap.Ref @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (FStar.Heap.Ref_r (FStar.Heap.Ref @a0
@x1))
@x1)
  
:pattern ((FStar.Heap.Ref @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-FStar.Heap.Ref ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
2430)
(= @x0
(FStar.Heap.Ref (FStar.Heap.Ref_a @x0)
(FStar.Heap.Ref_r @x0)))))

; </end constructor FStar.Heap.Ref>
;;;;;;;;;;;;;;;;Typ_fun_2432 kinding
(assert (HasKind Typ_fun_2432
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2432)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2432)))))
;;;;;;;;;;;;;;;;Typ_fun_2432 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2432)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Heap.ref @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
FStar.Heap.aref))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2432)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2434
(Term_constr_id FStar.Heap.Ref@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType FStar.Heap.Ref@tok
Typ_fun_2432))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET FStar.Heap.Ref@tok
@a0)
@x1)
(FStar.Heap.Ref @a0
@x1))
  
:pattern ((ApplyEE (ApplyET FStar.Heap.Ref@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
(FStar.Heap.ref @a1)))
(HasTypeFuel @u0
(FStar.Heap.Ref @a1
@x2)
FStar.Heap.aref))
  
:pattern ((HasTypeFuel @u0
(FStar.Heap.Ref @a1
@x2)
FStar.Heap.aref)))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(FStar.Heap.Ref @a1
@x2)
FStar.Heap.aref)
(and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
(FStar.Heap.ref @a1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(FStar.Heap.Ref @a1
@x2)
FStar.Heap.aref)))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(FStar.Heap.Ref @a1
@x2)
FStar.Heap.aref)
(Valid (Precedes @x2
(FStar.Heap.Ref @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(FStar.Heap.Ref @a1
@x2)
FStar.Heap.aref)))))

; </end encoding FStar.Heap.Ref>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
FStar.Heap.aref)
(is-FStar.Heap.Ref @x1))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
FStar.Heap.aref)))))

; </end encoding >

; <Start encoding FStar.Heap.is_Ref>
(declare-fun FStar.Heap.is_Ref (Term) Term)
;;;;;;;;;;;;;;;;(aref -> Tot bool)
(declare-fun Typ_fun_2436 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2436 kinding
(assert (HasKind Typ_fun_2436
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2436)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2436)))))
;;;;;;;;;;;;;;;;Typ_fun_2436 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2436)
(forall ((@x1 Term))
 (! (implies (HasType @x1
FStar.Heap.aref)
(HasType (ApplyEE @x0
@x1)
Prims.bool))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2436)))))
(declare-fun FStar.Heap.is_Ref@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2438
(Term_constr_id FStar.Heap.is_Ref@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE FStar.Heap.is_Ref@tok
@x0)
(FStar.Heap.is_Ref @x0))
  
:pattern ((ApplyEE FStar.Heap.is_Ref@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.is_Ref@tok
Typ_fun_2436))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
FStar.Heap.aref)
(HasType (FStar.Heap.is_Ref @x0)
Prims.bool))
  
:pattern ((FStar.Heap.is_Ref @x0)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@x0 Term))
 (! (= (FStar.Heap.is_Ref @x0)
(BoxBool (is-FStar.Heap.Ref @x0)))
  
:pattern ((FStar.Heap.is_Ref @x0)))))

; </end encoding FStar.Heap.is_Ref>

; <Start encoding FStar.Heap.Ref.a>
(declare-fun FStar.Heap.Ref.a (Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun FStar.Heap.Ref.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2440
(Type_constr_id FStar.Heap.Ref.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term))
 (! (= (ApplyTE FStar.Heap.Ref.a@tok
@x0)
(FStar.Heap.Ref.a @x0))
  
:pattern ((ApplyTE FStar.Heap.Ref.a@tok
@x0))

:pattern ((FStar.Heap.Ref.a @x0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind FStar.Heap.Ref.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
FStar.Heap.aref)
(HasKind (FStar.Heap.Ref.a @x0)
Kind_type))
  
:pattern ((FStar.Heap.Ref.a @x0)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@x0 Term))
 (! (= (FStar.Heap.Ref.a @x0)
(FStar.Heap.Ref_a @x0))
  
:pattern ((FStar.Heap.Ref.a @x0)))))

; </end encoding FStar.Heap.Ref.a>

; <Start encoding FStar.Heap.Ref.r>
(declare-fun FStar.Heap.Ref.r (Term) Term)
;;;;;;;;;;;;;;;;(projectee:aref -> Tot (ref (a projectee)))
(declare-fun Typ_fun_2442 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2442 kinding
(assert (HasKind Typ_fun_2442
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2442)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2442)))))
;;;;;;;;;;;;;;;;Typ_fun_2442 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2442)
(forall ((@x1 Term))
 (! (implies (HasType @x1
FStar.Heap.aref)
(HasType (ApplyEE @x0
@x1)
(FStar.Heap.ref (FStar.Heap.Ref.a @x1))))
  
:pattern ((ApplyEE @x0
@x1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2442)))))
(declare-fun FStar.Heap.Ref.r@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2444
(Term_constr_id FStar.Heap.Ref.r@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE FStar.Heap.Ref.r@tok
@x0)
(FStar.Heap.Ref.r @x0))
  
:pattern ((ApplyEE FStar.Heap.Ref.r@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.Ref.r@tok
Typ_fun_2442))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
FStar.Heap.aref)
(HasType (FStar.Heap.Ref.r @x0)
(FStar.Heap.ref (FStar.Heap.Ref.a @x0))))
  
:pattern ((FStar.Heap.Ref.r @x0)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@x0 Term))
 (! (= (FStar.Heap.Ref.r @x0)
(FStar.Heap.Ref_r @x0))
  
:pattern ((FStar.Heap.Ref.r @x0)))))

; </end encoding FStar.Heap.Ref.r>

; <Skipped />

; <Start encoding FStar.Heap.sel>
(declare-fun FStar.Heap.sel (Type Term Term) Term)
;;;;;;;;;;;;;;;;(heap -> (ref a) -> Tot a)
(declare-fun Typ_fun_2446 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2446 kinding
(assert (HasKind Typ_fun_2446
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2446)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2446)))))
;;;;;;;;;;;;;;;;Typ_fun_2446 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2446)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
@a1))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2446)))))
(declare-fun FStar.Heap.sel@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2448
(Term_constr_id FStar.Heap.sel@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Heap.sel@tok
@a0)
@x1)
@x2)
(FStar.Heap.sel @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Heap.sel@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.sel@tok
Typ_fun_2446))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Heap.ref @a0)))
(HasType (FStar.Heap.sel @a0
@x1
@x2)
@a0))
  
:pattern ((FStar.Heap.sel @a0
@x1
@x2)))))

; </end encoding FStar.Heap.sel>

; <Start encoding FStar.Heap.upd>
(declare-fun FStar.Heap.upd (Type Term Term Term) Term)
;;;;;;;;;;;;;;;;(heap -> (ref a) -> a -> Tot heap)
(declare-fun Typ_fun_2450 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2450 kinding
(assert (HasKind Typ_fun_2450
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2450)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2450)))))
;;;;;;;;;;;;;;;;Typ_fun_2450 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2450)
(forall ((@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a1))
(HasType @x4
@a1))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
@x4)
FStar.Heap.heap))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2450)))))
(declare-fun FStar.Heap.upd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2452
(Term_constr_id FStar.Heap.upd@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET FStar.Heap.upd@tok
@a0)
@x1)
@x2)
@x3)
(FStar.Heap.upd @a0
@x1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET FStar.Heap.upd@tok
@a0)
@x1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.upd@tok
Typ_fun_2450))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Heap.ref @a0))
(HasType @x3
@a0))
(HasType (FStar.Heap.upd @a0
@x1
@x2
@x3)
FStar.Heap.heap))
  
:pattern ((FStar.Heap.upd @a0
@x1
@x2
@x3)))))

; </end encoding FStar.Heap.upd>

; <Start encoding FStar.Heap.emp>
(declare-fun FStar.Heap.emp () Term)
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.emp
FStar.Heap.heap))
;;;;;;;;;;;;;;;;free var typing
(assert (HasType FStar.Heap.emp
FStar.Heap.heap))

; </end encoding FStar.Heap.emp>

; <Start encoding FStar.Heap.contains>
(declare-fun FStar.Heap.contains (Type Term Term) Term)
;;;;;;;;;;;;;;;;(heap -> (ref a) -> Tot bool)
(declare-fun Typ_fun_2454 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2454 kinding
(assert (HasKind Typ_fun_2454
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2454)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2454)))))
;;;;;;;;;;;;;;;;Typ_fun_2454 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2454)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2454)))))
(declare-fun FStar.Heap.contains@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2456
(Term_constr_id FStar.Heap.contains@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Heap.contains@tok
@a0)
@x1)
@x2)
(FStar.Heap.contains @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Heap.contains@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.contains@tok
Typ_fun_2454))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Heap.ref @a0)))
(HasType (FStar.Heap.contains @a0
@x1
@x2)
Prims.bool))
  
:pattern ((FStar.Heap.contains @a0
@x1
@x2)))))

; </end encoding FStar.Heap.contains>

; <Start encoding FStar.Heap.equal>
(declare-fun FStar.Heap.equal (Term Term) Term)
;;;;;;;;;;;;;;;;(heap -> heap -> Tot bool)
(declare-fun Typ_fun_2458 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2458 kinding
(assert (HasKind Typ_fun_2458
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2458)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2458)))))
;;;;;;;;;;;;;;;;Typ_fun_2458 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2458)
(forall ((@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(HasType (ApplyEE (ApplyEE @x0
@x1)
@x2)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE @x0
@x1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2458)))))
(declare-fun FStar.Heap.equal@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2460
(Term_constr_id FStar.Heap.equal@tok)))
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (ApplyEE (ApplyEE FStar.Heap.equal@tok
@x0)
@x1)
(FStar.Heap.equal @x0
@x1))
  
:pattern ((ApplyEE (ApplyEE FStar.Heap.equal@tok
@x0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.equal@tok
Typ_fun_2458))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
FStar.Heap.heap)
(HasType @x1
FStar.Heap.heap))
(HasType (FStar.Heap.equal @x0
@x1)
Prims.bool))
  
:pattern ((FStar.Heap.equal @x0
@x1)))))

; </end encoding FStar.Heap.equal>

; <Start encoding FStar.Heap.restrict>
(declare-fun FStar.Heap.restrict (Term Term) Term)
;;;;;;;;;;;;;;;;(heap -> (set aref) -> Tot heap)
(declare-fun Typ_fun_2462 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2462 kinding
(assert (HasKind Typ_fun_2462
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2462)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2462)))))
;;;;;;;;;;;;;;;;Typ_fun_2462 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2462)
(forall ((@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Set.set FStar.Heap.aref)))
(HasType (ApplyEE (ApplyEE @x0
@x1)
@x2)
FStar.Heap.heap))
  
:pattern ((ApplyEE (ApplyEE @x0
@x1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2462)))))
(declare-fun FStar.Heap.restrict@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2464
(Term_constr_id FStar.Heap.restrict@tok)))
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (ApplyEE (ApplyEE FStar.Heap.restrict@tok
@x0)
@x1)
(FStar.Heap.restrict @x0
@x1))
  
:pattern ((ApplyEE (ApplyEE FStar.Heap.restrict@tok
@x0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.restrict@tok
Typ_fun_2462))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
FStar.Heap.heap)
(HasType @x1
(FStar.Set.set FStar.Heap.aref)))
(HasType (FStar.Heap.restrict @x0
@x1)
FStar.Heap.heap))
  
:pattern ((FStar.Heap.restrict @x0
@x1)))))

; </end encoding FStar.Heap.restrict>

; <Start encoding FStar.Heap.concat>
(declare-fun FStar.Heap.concat (Term Term) Term)
;;;;;;;;;;;;;;;;(heap -> heap -> Tot heap)
(declare-fun Typ_fun_2466 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2466 kinding
(assert (HasKind Typ_fun_2466
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2466)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2466)))))
;;;;;;;;;;;;;;;;Typ_fun_2466 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2466)
(forall ((@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(HasType (ApplyEE (ApplyEE @x0
@x1)
@x2)
FStar.Heap.heap))
  
:pattern ((ApplyEE (ApplyEE @x0
@x1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2466)))))
(declare-fun FStar.Heap.concat@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2468
(Term_constr_id FStar.Heap.concat@tok)))
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (ApplyEE (ApplyEE FStar.Heap.concat@tok
@x0)
@x1)
(FStar.Heap.concat @x0
@x1))
  
:pattern ((ApplyEE (ApplyEE FStar.Heap.concat@tok
@x0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.concat@tok
Typ_fun_2466))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
FStar.Heap.heap)
(HasType @x1
FStar.Heap.heap))
(HasType (FStar.Heap.concat @x0
@x1)
FStar.Heap.heap))
  
:pattern ((FStar.Heap.concat @x0
@x1)))))

; </end encoding FStar.Heap.concat>

; <Start encoding FStar.Heap.SelUpd1>
;;;;;;;;;;;;;;;;Assumption: SelUpd1
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Heap.ref @a0))
(HasType @x3
@a0))
(= (FStar.Heap.sel @a0
(FStar.Heap.upd @a0
@x1
@x2
@x3)
@x2)
@x3))
  
:pattern ((FStar.Heap.sel @a0
(FStar.Heap.upd @a0
@x1
@x2
@x3)
@x2)))))

; </end encoding FStar.Heap.SelUpd1>

; <Start encoding FStar.Heap.SelUpd2>
;;;;;;;;;;;;;;;;Assumption: SelUpd2
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a0))
(HasType @x4
(FStar.Heap.ref @a1))
(HasType @x5
@a1)
(not (= @x4
@x3)))
(= (FStar.Heap.sel @a0
(FStar.Heap.upd @a1
@x2
@x4
@x5)
@x3)
(FStar.Heap.sel @a0
@x2
@x3)))
  
:pattern ((FStar.Heap.sel @a0
(FStar.Heap.upd @a1
@x2
@x4
@x5)
@x3)))))

; </end encoding FStar.Heap.SelUpd2>

; <Start encoding FStar.Heap.ContainsUpd>
;;;;;;;;;;;;;;;;Assumption: ContainsUpd
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a0))
(HasType @x4
(FStar.Heap.ref @a1))
(HasType @x5
@a0))
(iff (BoxBool_proj_0 (FStar.Heap.contains @a1
(FStar.Heap.upd @a0
@x2
@x3
@x5)
@x4))
(or (= @x3
@x4)
(BoxBool_proj_0 (FStar.Heap.contains @a1
@x2
@x4)))))
  
:pattern ((FStar.Heap.contains @a1
(FStar.Heap.upd @a0
@x2
@x3
@x5)
@x4)))))

; </end encoding FStar.Heap.ContainsUpd>

; <Start encoding FStar.Heap.InDomEmp>
;;;;;;;;;;;;;;;;Assumption: InDomEmp
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Heap.ref @a0)))
(not (BoxBool_proj_0 (FStar.Heap.contains @a0
FStar.Heap.emp
@x1))))
  
:pattern ((FStar.Heap.contains @a0
FStar.Heap.emp
@x1)))))

; </end encoding FStar.Heap.InDomEmp>

; <Start encoding FStar.Heap.Extensional>
;;;;;;;;;;;;;;;;Assumption: Extensional
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
FStar.Heap.heap)
(HasType @x1
FStar.Heap.heap))
(iff (BoxBool_proj_0 (FStar.Heap.equal @x0
@x1))
(= @x0
@x1)))
  
:pattern ((FStar.Heap.equal @x0
@x1)))))

; </end encoding FStar.Heap.Extensional>

; <Start encoding FStar.Heap.Equals>
;;;;;;;;;;;;;;;;Assumption: Equals
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
FStar.Heap.heap)
(HasType @x1
FStar.Heap.heap))
(iff (BoxBool_proj_0 (FStar.Heap.equal @x0
@x1))
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(FStar.Heap.ref @a2)))
(= (FStar.Heap.sel @a2
@x0
@x3)
(FStar.Heap.sel @a2
@x1
@x3)))
  
:pattern ((FStar.Heap.sel @a2
@x0
@x3) (FStar.Heap.sel @a2
@x1
@x3))))))
  
:pattern ((FStar.Heap.equal @x0
@x1)))))

; </end encoding FStar.Heap.Equals>

; <Start encoding FStar.Heap.RestrictSel>
;;;;;;;;;;;;;;;;Assumption: RestrictSel
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Set.set FStar.Heap.aref))
(HasType @x3
(FStar.Heap.ref @a0))
(BoxBool_proj_0 (FStar.Set.mem FStar.Heap.aref
(FStar.Heap.Ref @a0
@x3)
@x2)))
(= (FStar.Heap.sel @a0
(FStar.Heap.restrict @x1
@x2)
@x3)
(FStar.Heap.sel @a0
@x1
@x3)))
  
:pattern ((FStar.Heap.sel @a0
(FStar.Heap.restrict @x1
@x2)
@x3)))))

; </end encoding FStar.Heap.RestrictSel>

; <Start encoding FStar.Heap.RestrictIn>
;;;;;;;;;;;;;;;;Assumption: RestrictIn
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
(FStar.Set.set FStar.Heap.aref))
(HasType @x3
(FStar.Heap.ref @a0)))
(= (FStar.Heap.contains @a0
(FStar.Heap.restrict @x1
@x2)
@x3)
(Prims.op_AmpAmp (FStar.Set.mem FStar.Heap.aref
(FStar.Heap.Ref @a0
@x3)
@x2)
(FStar.Heap.contains @a0
@x1
@x3))))
  
:pattern ((FStar.Heap.contains @a0
(FStar.Heap.restrict @x1
@x2)
@x3)))))

; </end encoding FStar.Heap.RestrictIn>

; <Start encoding FStar.Heap.SelConcat>
;;;;;;;;;;;;;;;;Assumption: SelConcat
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a0)))
(ite (BoxBool_proj_0 (FStar.Heap.contains @a0
@x2
@x3))
(= (FStar.Heap.sel @a0
(FStar.Heap.concat @x1
@x2)
@x3)
(FStar.Heap.sel @a0
@x2
@x3))
(= (FStar.Heap.sel @a0
(FStar.Heap.concat @x1
@x2)
@x3)
(FStar.Heap.sel @a0
@x1
@x3))))
  
:pattern ((FStar.Heap.sel @a0
(FStar.Heap.concat @x1
@x2)
@x3)))))

; </end encoding FStar.Heap.SelConcat>

; <Start encoding FStar.Heap.ContainsConcat>
;;;;;;;;;;;;;;;;Assumption: ContainsConcat
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap)
(HasType @x3
(FStar.Heap.ref @a0)))
(= (FStar.Heap.contains @a0
(FStar.Heap.concat @x1
@x2)
@x3)
(Prims.op_BarBar (FStar.Heap.contains @a0
@x1
@x3)
(FStar.Heap.contains @a0
@x2
@x3))))
  
:pattern ((FStar.Heap.contains @a0
(FStar.Heap.concat @x1
@x2)
@x3)))))

; </end encoding FStar.Heap.ContainsConcat>

; <Start encoding FStar.Heap.On>
;;;;;;;;;;;;;;;;(heap -> Type)
(declare-fun Kind_arrow_2470 () Kind)
;;;;;;;;;;;;;;;;Kind_arrow_2470 interpretation
(assert (forall ((@a0 Type))
 (! (iff (HasKind @a0
Kind_arrow_2470)
(and (is-Kind_arrow (PreKind @a0))
(forall ((@x1 Term))
 (! (implies (HasType @x1
FStar.Heap.heap)
(HasKind (ApplyTE @a0
@x1)
Kind_type))
  
:pattern ((ApplyTE @a0
@x1))))))
  
:pattern ((HasKind @a0
Kind_arrow_2470)))))
(declare-fun FStar.Heap.On (Term Type Term) Type)
(declare-fun FStar.Heap.On@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2471
(Type_constr_id FStar.Heap.On@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTE FStar.Heap.On@tok
@x0)
@a1)
@x2)
(FStar.Heap.On @x0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTE FStar.Heap.On@tok
@x0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@x0 Term) (@a1 Type) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasKind @a1
Kind_arrow_2470)
(HasType @x2
FStar.Heap.heap))
(= (FStar.Heap.On @x0
@a1
@x2)
(ApplyTE @a1
(FStar.Heap.restrict @x2
@x0))))
  
:pattern ((FStar.Heap.On @x0
@a1
@x2)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@x0 Term) (@a1 Type) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasKind @a1
Kind_arrow_2470)
(HasType @x2
FStar.Heap.heap))
(HasKind (FStar.Heap.On @x0
@a1
@x2)
Kind_type))
  
:pattern ((FStar.Heap.On @x0
@a1
@x2)))))

; </end encoding FStar.Heap.On>

; <Start encoding FStar.Heap.fresh>
(declare-fun FStar.Heap.fresh (Term Term Term) Type)
(declare-fun FStar.Heap.fresh@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2472
(Type_constr_id FStar.Heap.fresh@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTE FStar.Heap.fresh@tok
@x0)
@x1)
@x2)
(FStar.Heap.fresh @x0
@x1
@x2))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE FStar.Heap.fresh@tok
@x0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(= (Valid (FStar.Heap.fresh @x0
@x1
@x2))
(forall ((@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a3
Kind_type)
(HasType @x4
(FStar.Heap.ref @a3))
(BoxBool_proj_0 (FStar.Set.mem FStar.Heap.aref
(FStar.Heap.Ref @a3
@x4)
@x0)))
(and (not (BoxBool_proj_0 (FStar.Heap.contains @a3
@x1
@x4)))
(BoxBool_proj_0 (FStar.Heap.contains @a3
@x2
@x4))))
  
:pattern ((FStar.Heap.contains @a3
@x1
@x4))))))
  
:pattern ((Valid (FStar.Heap.fresh @x0
@x1
@x2))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(HasKind (FStar.Heap.fresh @x0
@x1
@x2)
Kind_type))
  
:pattern ((FStar.Heap.fresh @x0
@x1
@x2)))))

; </end encoding FStar.Heap.fresh>

; <Start encoding FStar.Heap.modifies>
(declare-fun FStar.Heap.modifies (Term Term Term) Type)
(declare-fun FStar.Heap.modifies@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2473
(Type_constr_id FStar.Heap.modifies@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTE FStar.Heap.modifies@tok
@x0)
@x1)
@x2)
(FStar.Heap.modifies @x0
@x1
@x2))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE FStar.Heap.modifies@tok
@x0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(= (Valid (FStar.Heap.modifies @x0
@x1
@x2))
(BoxBool_proj_0 (FStar.Heap.equal @x2
(FStar.Heap.concat @x2
(FStar.Heap.restrict @x1
(FStar.Set.complement FStar.Heap.aref
@x0)))))))
  
:pattern ((Valid (FStar.Heap.modifies @x0
@x1
@x2))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(HasKind (FStar.Heap.modifies @x0
@x1
@x2)
Kind_type))
  
:pattern ((FStar.Heap.modifies @x0
@x1
@x2)))))

; </end encoding FStar.Heap.modifies>

; <Start encoding FStar.Heap.only>
(declare-fun FStar.Heap.only (Type Term) Term)
;;;;;;;;;;;;;;;;(x:(ref _2_2079) -> Tot (set aref))
(declare-fun Typ_fun_2475 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2475 kinding
(assert (HasKind Typ_fun_2475
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2475)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2475)))))
;;;;;;;;;;;;;;;;Typ_fun_2475 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2475)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Heap.ref @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2475)))))
(declare-fun FStar.Heap.only@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2477
(Term_constr_id FStar.Heap.only@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET FStar.Heap.only@tok
@a0)
@x1)
(FStar.Heap.only @a0
@x1))
  
:pattern ((ApplyEE (ApplyET FStar.Heap.only@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.only@tok
Typ_fun_2475))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Heap.ref @a0)))
(HasType (FStar.Heap.only @a0
@x1)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((FStar.Heap.only @a0
@x1)))))
(declare-fun Exp_abs_2478 (Type) Term)
;;;;;;;;;;;;;;;;(x:(ref _2_2079) -> Tot (set aref))
(declare-fun Typ_fun_2480 (Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_2480 kinding
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_fun_2480 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_fun_2480 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasTypeFuel @u0
@x1
(Typ_fun_2480 @a2))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_2480 @a2))))))
;;;;;;;;;;;;;;;;Typ_fun_2480 interpretation
(assert (forall ((@x0 Term) (@a1 Type))
 (! (iff (HasTypeZ @x0
(Typ_fun_2480 @a1))
(forall ((@x2 Term))
 (! (implies (HasType @x2
(FStar.Heap.ref @a1))
(HasType (ApplyEE @x0
@x2)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((ApplyEE @x0
@x2)))))
  
:pattern ((HasTypeZ @x0
(Typ_fun_2480 @a1))))))
;;;;;;;;;;;;;;;;Exp_abs_2478 typing
(assert (forall ((@a0 Type))
 (! (HasType (Exp_abs_2478 @a0)
(Typ_fun_2480 @a0))
  
:pattern ((Exp_abs_2478 @a0)))))
;;;;;;;;;;;;;;;;Exp_abs_2478 interpretation
(assert (forall ((@x0 Term) (@a1 Type))
 (! (implies (IsTyped (ApplyEE (Exp_abs_2478 @a1)
@x0))
(= (ApplyEE (Exp_abs_2478 @a1)
@x0)
(FStar.Set.singleton FStar.Heap.aref
(FStar.Heap.Ref @a1
@x0))))
  
:pattern ((ApplyEE (Exp_abs_2478 @a1)
@x0)))))
;;;;;;;;;;;;;;;;Equation for FStar.Heap.only
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Heap.ref @a0)))
(= (FStar.Heap.only @a0
@x1)
(ApplyEE (Exp_abs_2478 @a0)
@x1)))
  
:pattern ((FStar.Heap.only @a0
@x1)))))

; </end encoding FStar.Heap.only>

; <Skipped FStar.Heap.op_Hat_Plus_Plus/>

; <Start encoding FStar.Heap.op_Hat_Plus_Plus>
(declare-fun FStar.Heap.op_Hat_Plus_Plus (Type Term Term) Term)
;;;;;;;;;;;;;;;;(r:(ref a) -> (set aref) -> Tot (set aref))
(declare-fun Typ_fun_2483 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2483 kinding
(assert (HasKind Typ_fun_2483
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2483)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2483)))))
;;;;;;;;;;;;;;;;Typ_fun_2483 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2483)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Heap.ref @a1))
(HasType @x3
(FStar.Set.set FStar.Heap.aref)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2483)))))
(declare-fun FStar.Heap.op_Hat_Plus_Plus@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2485
(Term_constr_id FStar.Heap.op_Hat_Plus_Plus@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Heap.op_Hat_Plus_Plus@tok
@a0)
@x1)
@x2)
(FStar.Heap.op_Hat_Plus_Plus @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Heap.op_Hat_Plus_Plus@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.op_Hat_Plus_Plus@tok
Typ_fun_2483))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Heap.ref @a0))
(HasType @x2
(FStar.Set.set FStar.Heap.aref)))
(HasType (FStar.Heap.op_Hat_Plus_Plus @a0
@x1
@x2)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((FStar.Heap.op_Hat_Plus_Plus @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Equation for FStar.Heap.op_Hat_Plus_Plus
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Heap.ref @a0))
(HasType @x2
(FStar.Set.set FStar.Heap.aref)))
(= (FStar.Heap.op_Hat_Plus_Plus @a0
@x1
@x2)
(FStar.Set.union FStar.Heap.aref
(FStar.Set.singleton FStar.Heap.aref
(FStar.Heap.Ref @a0
@x1))
@x2)))
  
:pattern ((FStar.Heap.op_Hat_Plus_Plus @a0
@x1
@x2)))))

; </end encoding FStar.Heap.op_Hat_Plus_Plus>

; <Skipped FStar.Heap.op_Plus_Plus_Hat/>

; <Start encoding FStar.Heap.op_Plus_Plus_Hat>
(declare-fun FStar.Heap.op_Plus_Plus_Hat (Type Term Term) Term)
;;;;;;;;;;;;;;;;((set aref) -> r:(ref a) -> Tot (set aref))
(declare-fun Typ_fun_2487 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2487 kinding
(assert (HasKind Typ_fun_2487
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2487)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2487)))))
;;;;;;;;;;;;;;;;Typ_fun_2487 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2487)
(forall ((@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(FStar.Set.set FStar.Heap.aref))
(HasType @x3
(FStar.Heap.ref @a1)))
(HasType (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2487)))))
(declare-fun FStar.Heap.op_Plus_Plus_Hat@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2489
(Term_constr_id FStar.Heap.op_Plus_Plus_Hat@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET FStar.Heap.op_Plus_Plus_Hat@tok
@a0)
@x1)
@x2)
(FStar.Heap.op_Plus_Plus_Hat @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET FStar.Heap.op_Plus_Plus_Hat@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.op_Plus_Plus_Hat@tok
Typ_fun_2487))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set FStar.Heap.aref))
(HasType @x2
(FStar.Heap.ref @a0)))
(HasType (FStar.Heap.op_Plus_Plus_Hat @a0
@x1
@x2)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((FStar.Heap.op_Plus_Plus_Hat @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Equation for FStar.Heap.op_Plus_Plus_Hat
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(FStar.Set.set FStar.Heap.aref))
(HasType @x2
(FStar.Heap.ref @a0)))
(= (FStar.Heap.op_Plus_Plus_Hat @a0
@x1
@x2)
(FStar.Set.union FStar.Heap.aref
@x1
(FStar.Set.singleton FStar.Heap.aref
(FStar.Heap.Ref @a0
@x2)))))
  
:pattern ((FStar.Heap.op_Plus_Plus_Hat @a0
@x1
@x2)))))

; </end encoding FStar.Heap.op_Plus_Plus_Hat>

; <Skipped FStar.Heap.op_Hat_Plus_Hat/>

; <Start encoding FStar.Heap.op_Hat_Plus_Hat>
(declare-fun FStar.Heap.op_Hat_Plus_Hat (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;((ref a) -> (ref b) -> Tot (set aref))
(declare-fun Typ_fun_2491 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2491 kinding
(assert (HasKind Typ_fun_2491
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2491)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2491)))))
;;;;;;;;;;;;;;;;Typ_fun_2491 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2491)
(forall ((@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(FStar.Heap.ref @a1))
(HasType @x4
(FStar.Heap.ref @a2)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2491)))))
(declare-fun FStar.Heap.op_Hat_Plus_Hat@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2493
(Term_constr_id FStar.Heap.op_Hat_Plus_Hat@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET FStar.Heap.op_Hat_Plus_Hat@tok
@a0)
@a1)
@x2)
@x3)
(FStar.Heap.op_Hat_Plus_Hat @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET FStar.Heap.op_Hat_Plus_Hat@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType FStar.Heap.op_Hat_Plus_Hat@tok
Typ_fun_2491))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(FStar.Heap.ref @a0))
(HasType @x3
(FStar.Heap.ref @a1)))
(HasType (FStar.Heap.op_Hat_Plus_Hat @a0
@a1
@x2
@x3)
(FStar.Set.set FStar.Heap.aref)))
  
:pattern ((FStar.Heap.op_Hat_Plus_Hat @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Equation for FStar.Heap.op_Hat_Plus_Hat
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(FStar.Heap.ref @a0))
(HasType @x3
(FStar.Heap.ref @a1)))
(= (FStar.Heap.op_Hat_Plus_Hat @a0
@a1
@x2
@x3)
(FStar.Set.union FStar.Heap.aref
(FStar.Set.singleton FStar.Heap.aref
(FStar.Heap.Ref @a0
@x2))
(FStar.Set.singleton FStar.Heap.aref
(FStar.Heap.Ref @a1
@x3)))))
  
:pattern ((FStar.Heap.op_Hat_Plus_Hat @a0
@a1
@x2
@x3)))))

; </end encoding FStar.Heap.op_Hat_Plus_Hat>

; End Externals for module FStar.Heap

; Externals for module FStar.ST

; <Start encoding FStar.ST.ref>
(declare-fun FStar.ST.ref (Type) Type)
(declare-fun FStar.ST.ref@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2613
(Type_constr_id FStar.ST.ref@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT FStar.ST.ref@tok
@a0)
(FStar.ST.ref @a0))
  
:pattern ((ApplyTT FStar.ST.ref@tok
@a0)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(= (FStar.ST.ref @a0)
(FStar.Heap.ref @a0)))
  
:pattern ((FStar.ST.ref @a0)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (FStar.ST.ref @a0)
Kind_type))
  
:pattern ((FStar.ST.ref @a0)))))

; </end encoding FStar.ST.ref>

; <Start encoding FStar.ST.modifies>
(declare-fun FStar.ST.modifies (Term Term Term) Type)
(declare-fun FStar.ST.modifies@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2614
(Type_constr_id FStar.ST.modifies@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTE FStar.ST.modifies@tok
@x0)
@x1)
@x2)
(FStar.ST.modifies @x0
@x1
@x2))
  
:pattern ((ApplyTE (ApplyTE (ApplyTE FStar.ST.modifies@tok
@x0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(= (Valid (FStar.ST.modifies @x0
@x1
@x2))
(BoxBool_proj_0 (FStar.Heap.equal @x2
(FStar.Heap.concat @x2
(FStar.Heap.restrict @x1
(FStar.Set.complement FStar.Heap.aref
@x0)))))))
  
:pattern ((Valid (FStar.ST.modifies @x0
@x1
@x2))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@x0 Term) (@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x0
(FStar.Set.set FStar.Heap.aref))
(HasType @x1
FStar.Heap.heap)
(HasType @x2
FStar.Heap.heap))
(HasKind (FStar.ST.modifies @x0
@x1
@x2)
Kind_type))
  
:pattern ((FStar.ST.modifies @x0
@x1
@x2)))))

; </end encoding FStar.ST.modifies>

; <Skipped FStar.ST.STPre/>

; <Skipped FStar.ST.STPost/>

; <Skipped FStar.ST.STWP/>

; <Skipped FStar.ST.STATE/>

; <Skipped FStar.ST.State/>

; <Skipped FStar.ST.ST/>

; <Skipped FStar.ST.St/>

; <Skipped />

; <Start encoding FStar.ST.recall>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.ST.recall (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.ST.recall@tok () Term)

; </end encoding FStar.ST.recall>

; <Start encoding FStar.ST.alloc>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.ST.alloc (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.ST.alloc@tok () Term)

; </end encoding FStar.ST.alloc>

; <Start encoding FStar.ST.read>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.ST.read (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.ST.read@tok () Term)

; </end encoding FStar.ST.read>

; <Start encoding FStar.ST.write>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.ST.write (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.ST.write@tok () Term)

; </end encoding FStar.ST.write>

; <Start encoding FStar.ST.op_Colon_Equals>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.ST.op_Colon_Equals (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.ST.op_Colon_Equals@tok () Term)

; </end encoding FStar.ST.op_Colon_Equals>

; <Start encoding FStar.ST.get>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.ST.get (Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.ST.get@tok () Term)

; </end encoding FStar.ST.get>

; End Externals for module FStar.ST

; Externals for module FStar.All

; <Skipped FStar.All.AllPre/>

; <Skipped FStar.All.AllPost/>

; <Skipped FStar.All.AllWP/>

; <Skipped FStar.All.ALL/>

; <Skipped FStar.All.All/>

; <Skipped FStar.All.ML/>

; <Skipped />

; <Skipped />

; <Start encoding FStar.All.pipe_right>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.All.pipe_right (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.All.pipe_right@tok () Term)

; </end encoding FStar.All.pipe_right>

; <Start encoding FStar.All.pipe_left>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.All.pipe_left (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.All.pipe_left@tok () Term)

; </end encoding FStar.All.pipe_left>

; <Start encoding FStar.All.failwith>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.All.failwith (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.All.failwith@tok () Term)

; </end encoding FStar.All.failwith>

; <Start encoding FStar.All.exit>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.All.exit (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.All.exit@tok () Term)

; </end encoding FStar.All.exit>

; <Start encoding FStar.All.try_with>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun FStar.All.try_with (Type Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun FStar.All.try_with@tok () Term)

; </end encoding FStar.All.try_with>

; End Externals for module FStar.All

; Internals for module DList

; encoding sigelt DList.dList1, DList.Nil, DList.Unit, DList.Join

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun DList.dList1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.dList1@a0 (Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun DList.dList1@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun DList.Nil (Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Nil__t (Term) Type)
;;;;;;;;;;;;;;;;( -> Tot (dList1 't))
(declare-fun Typ_fun_2765 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Nil
(declare-fun DList.Nil@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun DList.Unit (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Unit__t (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Unit__0 (Term) Term)
;;;;;;;;;;;;;;;;(_0:'t -> Tot (dList1 't))
(declare-fun Typ_fun_2771 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Unit
(declare-fun DList.Unit@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun DList.Join (Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Join__t (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Join__0 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Join__1 (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun DList.Join__2 (Term) Term)
;;;;;;;;;;;;;;;;(_0:(dList1 't) -> _1:(dList1 't) -> _2:nat -> Tot (dList1 't))
(declare-fun Typ_fun_2777 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Join
(declare-fun DList.Join@tok () Term)

; <Start encoding DList.dList1>

; <start constructor DList.dList1>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 2756
(Type_constr_id (DList.dList1 @a0)))
  
:pattern ((DList.dList1 @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (DList.dList1@a0 (DList.dList1 @a0))
@a0)
  
:pattern ((DList.dList1 @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-DList.dList1 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2756)
(= @a0
(DList.dList1 (DList.dList1@a0 @a0)))))

; </end constructor DList.dList1>
;;;;;;;;;;;;;;;;fresh token
(assert (= 2757
(Type_constr_id DList.dList1@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT DList.dList1@tok
@a0)
(DList.dList1 @a0))
  
:pattern ((ApplyTT DList.dList1@tok
@a0))

:pattern ((DList.dList1 @a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind DList.dList1@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (DList.dList1 @a0)
Kind_type))
  
:pattern ((DList.dList1 @a0)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type))
 (! (implies (HasTypeFuel @u1
@x0
(DList.dList1 @a2))
(= (DList.dList1 @a2)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(DList.dList1 @a2))))))

; </end encoding DList.dList1>

; <Start encoding DList.Nil>

; <start constructor DList.Nil>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (! (= 2763
(Term_constr_id (DList.Nil @a0)))
  
:pattern ((DList.Nil @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (DList.Nil__t (DList.Nil @a0))
@a0)
  
:pattern ((DList.Nil @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-DList.Nil ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
2763)
(= @x0
(DList.Nil (DList.Nil__t @x0)))))

; </end constructor DList.Nil>
;;;;;;;;;;;;;;;;Typ_fun_2765 kinding
(assert (HasKind Typ_fun_2765
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2765)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2765)))))
;;;;;;;;;;;;;;;;Typ_fun_2765 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2765)
(forall ((@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasType (ApplyET @x0
@a1)
(DList.dList1 @a1)))
  
:pattern ((ApplyET @x0
@a1)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2765)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2767
(Term_constr_id DList.Nil@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType DList.Nil@tok
Typ_fun_2765))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type))
 (! (= (ApplyET DList.Nil@tok
@a0)
(DList.Nil @a0))
  
:pattern ((ApplyET DList.Nil@tok
@a0)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type))
 (! (implies (HasKind @a1
Kind_type)
(HasTypeFuel @u0
(DList.Nil @a1)
(DList.dList1 @a1)))
  
:pattern ((HasTypeFuel @u0
(DList.Nil @a1)
(DList.dList1 @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(DList.Nil @a1)
(DList.dList1 @a2))
(and (= @a1
@a2)
(HasKind @a1
Kind_type)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(DList.Nil @a1)
(DList.dList1 @a2))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding DList.Nil>

; <Start encoding DList.Unit>

; <start constructor DList.Unit>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= 2769
(Term_constr_id (DList.Unit @a0
@x1)))
  
:pattern ((DList.Unit @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.Unit__t (DList.Unit @a0
@x1))
@a0)
  
:pattern ((DList.Unit @a0
@x1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.Unit__0 (DList.Unit @a0
@x1))
@x1)
  
:pattern ((DList.Unit @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-DList.Unit ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
2769)
(= @x0
(DList.Unit (DList.Unit__t @x0)
(DList.Unit__0 @x0)))))

; </end constructor DList.Unit>
;;;;;;;;;;;;;;;;Typ_fun_2771 kinding
(assert (HasKind Typ_fun_2771
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2771)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2771)))))
;;;;;;;;;;;;;;;;Typ_fun_2771 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2771)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(DList.dList1 @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2771)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2773
(Term_constr_id DList.Unit@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType DList.Unit@tok
Typ_fun_2771))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.Unit@tok
@a0)
@x1)
(DList.Unit @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.Unit@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1))
(HasTypeFuel @u0
(DList.Unit @a1
@x2)
(DList.dList1 @a1)))
  
:pattern ((HasTypeFuel @u0
(DList.Unit @a1
@x2)
(DList.dList1 @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(DList.Unit @a1
@x2)
(DList.dList1 @a3))
(and (= @a1
@a3)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
@a1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(DList.Unit @a1
@x2)
(DList.dList1 @a3))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(DList.Unit @a1
@x2)
(DList.dList1 @a3))
(Valid (Precedes @x2
(DList.Unit @a1
@x2))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(DList.Unit @a1
@x2)
(DList.dList1 @a3))))))

; </end encoding DList.Unit>

; <Start encoding DList.Join>

; <start constructor DList.Join>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= 2775
(Term_constr_id (DList.Join @a0
@x1
@x2
@x3)))
  
:pattern ((DList.Join @a0
@x1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (DList.Join__t (DList.Join @a0
@x1
@x2
@x3))
@a0)
  
:pattern ((DList.Join @a0
@x1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (DList.Join__0 (DList.Join @a0
@x1
@x2
@x3))
@x1)
  
:pattern ((DList.Join @a0
@x1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (DList.Join__1 (DList.Join @a0
@x1
@x2
@x3))
@x2)
  
:pattern ((DList.Join @a0
@x1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (DList.Join__2 (DList.Join @a0
@x1
@x2
@x3))
@x3)
  
:pattern ((DList.Join @a0
@x1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-DList.Join ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
2775)
(= @x0
(DList.Join (DList.Join__t @x0)
(DList.Join__0 @x0)
(DList.Join__1 @x0)
(DList.Join__2 @x0)))))

; </end constructor DList.Join>
;;;;;;;;;;;;;;;;Typ_fun_2777 kinding
(assert (HasKind Typ_fun_2777
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2777)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2777)))))
;;;;;;;;;;;;;;;;Typ_fun_2777 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2777)
(forall ((@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList1 @a1))
(HasType @x3
(DList.dList1 @a1))
(HasType @x4
Prims.nat@tok))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
@x4)
(DList.dList1 @a1)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET @x0
@a1)
@x2)
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2777)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2779
(Term_constr_id DList.Join@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType DList.Join@tok
Typ_fun_2777))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET DList.Join@tok
@a0)
@x1)
@x2)
@x3)
(DList.Join @a0
@x1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET DList.Join@tok
@a0)
@x1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
(DList.dList1 @a1))
(HasTypeFuel @u0
@x3
(DList.dList1 @a1))
(HasTypeFuel @u0
@x4
Prims.nat@tok))
(HasTypeFuel @u0
(DList.Join @a1
@x2
@x3
@x4)
(DList.dList1 @a1)))
  
:pattern ((HasTypeFuel @u0
(DList.Join @a1
@x2
@x3
@x4)
(DList.dList1 @a1))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(DList.Join @a1
@x2
@x3
@x4)
(DList.dList1 @a5))
(and (= @a1
@a5)
(HasKind @a1
Kind_type)
(HasTypeFuel @u0
@x2
(DList.dList1 @a1))
(HasTypeFuel @u0
@x3
(DList.dList1 @a1))
(HasTypeFuel @u0
@x4
Prims.nat@tok)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(DList.Join @a1
@x2
@x3
@x4)
(DList.dList1 @a5))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term) (@a5 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(DList.Join @a1
@x2
@x3
@x4)
(DList.dList1 @a5))
(and (Valid (Precedes @x2
(DList.Join @a1
@x2
@x3
@x4)))
(Valid (Precedes @x3
(DList.Join @a1
@x2
@x3
@x4)))
(Valid (Precedes @x4
(DList.Join @a1
@x2
@x3
@x4)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(DList.Join @a1
@x2
@x3
@x4)
(DList.dList1 @a5))))))

; </end encoding DList.Join>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(DList.dList1 @a2))
(or (and (is-DList.Nil @x1)
(= @a2
(DList.Nil__t @x1)))
(and (is-DList.Unit @x1)
(= @a2
(DList.Unit__t @x1)))
(and (is-DList.Join @x1)
(= @a2
(DList.Join__t @x1)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(DList.dList1 @a2))))))

; </end encoding >

; encoding sigelt DList.is_Nil

; <Start encoding DList.is_Nil>
(declare-fun DList.is_Nil (Type Term) Term)
;;;;;;;;;;;;;;;;((dList1 't) -> Tot bool)
(declare-fun Typ_fun_2781 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2781 kinding
(assert (HasKind Typ_fun_2781
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2781)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2781)))))
;;;;;;;;;;;;;;;;Typ_fun_2781 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2781)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList1 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2781)))))
(declare-fun DList.is_Nil@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2783
(Term_constr_id DList.is_Nil@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.is_Nil@tok
@a0)
@x1)
(DList.is_Nil @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.is_Nil@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.is_Nil@tok
Typ_fun_2781))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(DList.dList1 @a0)))
(HasType (DList.is_Nil @a0
@x1)
Prims.bool))
  
:pattern ((DList.is_Nil @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.is_Nil @a0
@x1)
(BoxBool (is-DList.Nil @x1)))
  
:pattern ((DList.is_Nil @a0
@x1)))))

; </end encoding DList.is_Nil>

; encoding sigelt DList.is_Unit

; <Start encoding DList.is_Unit>
(declare-fun DList.is_Unit (Type Term) Term)
(declare-fun DList.is_Unit@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2785
(Term_constr_id DList.is_Unit@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.is_Unit@tok
@a0)
@x1)
(DList.is_Unit @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.is_Unit@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.is_Unit@tok
Typ_fun_2781))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(DList.dList1 @a0)))
(HasType (DList.is_Unit @a0
@x1)
Prims.bool))
  
:pattern ((DList.is_Unit @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.is_Unit @a0
@x1)
(BoxBool (is-DList.Unit @x1)))
  
:pattern ((DList.is_Unit @a0
@x1)))))

; </end encoding DList.is_Unit>

; encoding sigelt DList.is_Join

; <Start encoding DList.is_Join>
(declare-fun DList.is_Join (Type Term) Term)
(declare-fun DList.is_Join@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2787
(Term_constr_id DList.is_Join@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.is_Join@tok
@a0)
@x1)
(DList.is_Join @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.is_Join@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.is_Join@tok
Typ_fun_2781))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(DList.dList1 @a0)))
(HasType (DList.is_Join @a0
@x1)
Prims.bool))
  
:pattern ((DList.is_Join @a0
@x1)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.is_Join @a0
@x1)
(BoxBool (is-DList.Join @x1)))
  
:pattern ((DList.is_Join @a0
@x1)))))

; </end encoding DList.is_Join>

; encoding sigelt DList.Unit._0

; <Start encoding DList.Unit._0>
(declare-fun Typ_refine_2789 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_2789 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2789 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_5_3:(dList1 't){(is_Unit _5_3)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_2789 @a2))
(and (HasTypeFuel @u0
@x1
(DList.dList1 @a2))
(BoxBool_proj_0 (DList.is_Unit @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2789 @a2))))))
(declare-fun DList.Unit._0 (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_5_3:(dList1 't){(is_Unit _5_3)} -> Tot 't)
(declare-fun Typ_fun_2792 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2792 kinding
(assert (HasKind Typ_fun_2792
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2792)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2792)))))
;;;;;;;;;;;;;;;;Typ_fun_2792 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2792)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_2789 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
@a1))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2792)))))
(declare-fun DList.Unit._0@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2794
(Term_constr_id DList.Unit._0@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.Unit._0@tok
@a0)
@x1)
(DList.Unit._0 @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.Unit._0@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.Unit._0@tok
Typ_fun_2792))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_2789 @a0)))
(HasType (DList.Unit._0 @a0
@x1)
@a0))
  
:pattern ((DList.Unit._0 @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.Unit._0 @a0
@x1)
(DList.Unit__0 @x1))
  
:pattern ((DList.Unit._0 @a0
@x1)))))

; </end encoding DList.Unit._0>

; encoding sigelt let DList.Unit._0 : (projectee:_5_3:(dList1 't){(is_Unit _5_3)} -> Tot 't)

; <Skipped />

; encoding sigelt DList.Join._0

; <Start encoding DList.Join._0>
(declare-fun Typ_refine_2798 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_2798 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2798 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_5_6:(dList1 't){(is_Join _5_6)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_2798 @a2))
(and (HasTypeFuel @u0
@x1
(DList.dList1 @a2))
(BoxBool_proj_0 (DList.is_Join @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2798 @a2))))))
(declare-fun DList.Join._0 (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_5_6:(dList1 't){(is_Join _5_6)} -> Tot (dList1 't))
(declare-fun Typ_fun_2801 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2801 kinding
(assert (HasKind Typ_fun_2801
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2801)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2801)))))
;;;;;;;;;;;;;;;;Typ_fun_2801 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2801)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_2798 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
(DList.dList1 @a1)))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2801)))))
(declare-fun DList.Join._0@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2803
(Term_constr_id DList.Join._0@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.Join._0@tok
@a0)
@x1)
(DList.Join._0 @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.Join._0@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.Join._0@tok
Typ_fun_2801))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_2798 @a0)))
(HasType (DList.Join._0 @a0
@x1)
(DList.dList1 @a0)))
  
:pattern ((DList.Join._0 @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.Join._0 @a0
@x1)
(DList.Join__0 @x1))
  
:pattern ((DList.Join._0 @a0
@x1)))))

; </end encoding DList.Join._0>

; encoding sigelt let DList.Join._0 : (projectee:_5_6:(dList1 't){(is_Join _5_6)} -> Tot (dList1 't))

; <Skipped />

; encoding sigelt DList.Join._1

; <Start encoding DList.Join._1>
(declare-fun DList.Join._1 (Type Term) Term)
(declare-fun DList.Join._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2810
(Term_constr_id DList.Join._1@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.Join._1@tok
@a0)
@x1)
(DList.Join._1 @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.Join._1@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.Join._1@tok
Typ_fun_2801))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_2798 @a0)))
(HasType (DList.Join._1 @a0
@x1)
(DList.dList1 @a0)))
  
:pattern ((DList.Join._1 @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.Join._1 @a0
@x1)
(DList.Join__1 @x1))
  
:pattern ((DList.Join._1 @a0
@x1)))))

; </end encoding DList.Join._1>

; encoding sigelt let DList.Join._1 : (projectee:_5_6:(dList1 't){(is_Join _5_6)} -> Tot (dList1 't))

; <Skipped />

; encoding sigelt DList.Join._2

; <Start encoding DList.Join._2>
(declare-fun DList.Join._2 (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_5_6:(dList1 't){(is_Join _5_6)} -> Tot nat)
(declare-fun Typ_fun_2817 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2817 kinding
(assert (HasKind Typ_fun_2817
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2817)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2817)))))
;;;;;;;;;;;;;;;;Typ_fun_2817 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2817)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_2798 @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.nat@tok))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2817)))))
(declare-fun DList.Join._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2819
(Term_constr_id DList.Join._2@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.Join._2@tok
@a0)
@x1)
(DList.Join._2 @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.Join._2@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.Join._2@tok
Typ_fun_2817))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_2798 @a0)))
(HasType (DList.Join._2 @a0
@x1)
Prims.nat@tok))
  
:pattern ((DList.Join._2 @a0
@x1)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.Join._2 @a0
@x1)
(DList.Join__2 @x1))
  
:pattern ((DList.Join._2 @a0
@x1)))))

; </end encoding DList.Join._2>

; encoding sigelt let DList.Join._2 : (projectee:_5_6:(dList1 't){(is_Join _5_6)} -> Tot nat)

; <Skipped />

; encoding sigelt DList.isCorrectJoined

; <Skipped DList.isCorrectJoined/>

; encoding sigelt let DList.isCorrectJoined : (l:(dList1 't) -> Tot bool)

; <Start encoding DList.isCorrectJoined>
;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun DList.isCorrectJoined__2840 (Fuel Type Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun DList.isCorrectJoined__2841 () Term)
(declare-fun DList.isCorrectJoined (Type Term) Term)
(declare-fun DList.isCorrectJoined@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2838
(Term_constr_id DList.isCorrectJoined@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.isCorrectJoined@tok
@a0)
@x1)
(DList.isCorrectJoined @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.isCorrectJoined@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.isCorrectJoined@tok
Typ_fun_2781))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(DList.dList1 @a0)))
(HasType (DList.isCorrectJoined @a0
@x1)
Prims.bool))
  
:pattern ((DList.isCorrectJoined @a0
@x1)))))
;;;;;;;;;;;;;;;;Fuel token correspondence
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyEF DList.isCorrectJoined__2841
@u0)
@a1)
@x2)
(DList.isCorrectJoined__2840 @u0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyEF DList.isCorrectJoined__2841
@u0)
@a1)
@x2)))))
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList1 @a1)))
(HasType (DList.isCorrectJoined__2840 @u0
@a1
@x2)
Prims.bool))
  
:pattern ((DList.isCorrectJoined__2840 @u0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.isCorrectJoined @a0
@x1)
(DList.isCorrectJoined__2840 MaxFuel
@a0
@x1))
  
:pattern ((DList.isCorrectJoined @a0
@x1)))))
;;;;;;;;;;;;;;;;Fuel irrelevance
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (= (DList.isCorrectJoined__2840 (SFuel @u0)
@a1
@x2)
(DList.isCorrectJoined__2840 ZFuel
@a1
@x2))
  
:pattern ((DList.isCorrectJoined__2840 (SFuel @u0)
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for fuel-instrumented recursive function: DList.isCorrectJoined
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList1 @a1)))
(= (DList.isCorrectJoined__2840 (SFuel @u0)
@a1
@x2)
(ite (is-DList.Nil @x2)
(BoxBool true)
(ite (is-DList.Unit @x2)
(BoxBool true)
(ite (and (is-DList.Join @x2)
(is-DList.Nil (DList.Join__0 @x2)))
(BoxBool false)
(ite (is-DList.Join @x2)
(Prims.op_AmpAmp (DList.isCorrectJoined__2840 @u0
@a1
(DList.Join__0 @x2))
(DList.isCorrectJoined__2840 @u0
@a1
(DList.Join__1 @x2)))
Term_unit))))))
  
:pattern ((DList.isCorrectJoined__2840 (SFuel @u0)
@a1
@x2)))))

; </end encoding DList.isCorrectJoined>

; encoding sigelt DList.dList

; <Start encoding DList.dList>
(declare-fun DList.dList (Type) Type)
(declare-fun DList.dList@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2842
(Type_constr_id DList.dList@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT DList.dList@tok
@a0)
(DList.dList @a0))
  
:pattern ((ApplyTT DList.dList@tok
@a0)))))
(declare-fun Typ_refine_2844 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_2844 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2844 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;l:(dList1 't){(isCorrectJoined l)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_2844 @a2))
(and (HasTypeFuel @u0
@x1
(DList.dList1 @a2))
(BoxBool_proj_0 (DList.isCorrectJoined @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2844 @a2))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(= (DList.dList @a0)
(Typ_refine_2844 @a0)))
  
:pattern ((DList.dList @a0)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (DList.dList @a0)
Kind_type))
  
:pattern ((DList.dList @a0)))))

; </end encoding DList.dList>

; encoding sigelt DList.ld

; <Skipped DList.ld/>

; encoding sigelt let DList.ld : (l:(dList 't) -> Tot pos)

; <Start encoding DList.ld>
;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun DList.ld__2869 (Fuel Type Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun DList.ld__2870 () Term)
(declare-fun DList.ld (Type Term) Term)
;;;;;;;;;;;;;;;;(l:(dList 't) -> Tot pos)
(declare-fun Typ_fun_2865 () Type)
(declare-fun DList.ld@tok () Term)
;;;;;;;;;;;;;;;;Typ_fun_2865 kinding
(assert (HasKind Typ_fun_2865
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2865)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2865)))))
;;;;;;;;;;;;;;;;Typ_fun_2865 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2865)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList @a1)))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.pos@tok))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2865)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2867
(Term_constr_id DList.ld@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.ld@tok
@a0)
@x1)
(DList.ld @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.ld@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.ld@tok
Typ_fun_2865))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(DList.dList @a0)))
(HasType (DList.ld @a0
@x1)
Prims.pos@tok))
  
:pattern ((DList.ld @a0
@x1)))))
;;;;;;;;;;;;;;;;Fuel token correspondence
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyEF DList.ld__2870
@u0)
@a1)
@x2)
(DList.ld__2869 @u0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyEF DList.ld__2870
@u0)
@a1)
@x2)))))
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList @a1)))
(HasType (DList.ld__2869 @u0
@a1
@x2)
Prims.pos@tok))
  
:pattern ((DList.ld__2869 @u0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.ld @a0
@x1)
(DList.ld__2869 MaxFuel
@a0
@x1))
  
:pattern ((DList.ld @a0
@x1)))))
;;;;;;;;;;;;;;;;Fuel irrelevance
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (= (DList.ld__2869 (SFuel @u0)
@a1
@x2)
(DList.ld__2869 ZFuel
@a1
@x2))
  
:pattern ((DList.ld__2869 (SFuel @u0)
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for fuel-instrumented recursive function: DList.ld
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(DList.dList @a1)))
(= (DList.ld__2869 (SFuel @u0)
@a1
@x2)
(ite (is-DList.Nil @x2)
(BoxInt 1)
(ite (is-DList.Unit @x2)
(BoxInt 1)
(ite (is-DList.Join @x2)
(Prims.op_Addition (BoxInt 1)
(Prims.op_Addition (DList.ld__2869 @u0
@a1
(DList.Join__0 @x2))
(DList.ld__2869 @u0
@a1
(DList.Join__1 @x2))))
Term_unit)))))
  
:pattern ((DList.ld__2869 (SFuel @u0)
@a1
@x2)))))

; </end encoding DList.ld>

; encoding sigelt DList.lt

; <Skipped DList.lt/>

; encoding sigelt let DList.lt : (l:(list (dList 't)) -> Tot pos)

; <Start encoding DList.lt>
;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun DList.lt__2907 (Fuel Type Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun DList.lt__2908 () Term)
(declare-fun DList.lt (Type Term) Term)
;;;;;;;;;;;;;;;;(l:(list (dList 't)) -> Tot pos)
(declare-fun Typ_fun_2903 () Type)
(declare-fun DList.lt@tok () Term)
;;;;;;;;;;;;;;;;Typ_fun_2903 kinding
(assert (HasKind Typ_fun_2903
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2903)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2903)))))
;;;;;;;;;;;;;;;;Typ_fun_2903 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2903)
(forall ((@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Prims.list (DList.dList @a1))))
(HasType (ApplyEE (ApplyET @x0
@a1)
@x2)
Prims.pos@tok))
  
:pattern ((ApplyEE (ApplyET @x0
@a1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2903)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2905
(Term_constr_id DList.lt@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET DList.lt@tok
@a0)
@x1)
(DList.lt @a0
@x1))
  
:pattern ((ApplyEE (ApplyET DList.lt@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.lt@tok
Typ_fun_2903))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Prims.list (DList.dList @a0))))
(HasType (DList.lt @a0
@x1)
Prims.pos@tok))
  
:pattern ((DList.lt @a0
@x1)))))
;;;;;;;;;;;;;;;;Fuel token correspondence
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (= (ApplyEE (ApplyET (ApplyEF DList.lt__2908
@u0)
@a1)
@x2)
(DList.lt__2907 @u0
@a1
@x2))
  
:pattern ((ApplyEE (ApplyET (ApplyEF DList.lt__2908
@u0)
@a1)
@x2)))))
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Prims.list (DList.dList @a1))))
(HasType (DList.lt__2907 @u0
@a1
@x2)
Prims.pos@tok))
  
:pattern ((DList.lt__2907 @u0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (DList.lt @a0
@x1)
(DList.lt__2907 MaxFuel
@a0
@x1))
  
:pattern ((DList.lt @a0
@x1)))))
;;;;;;;;;;;;;;;;Fuel irrelevance
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (= (DList.lt__2907 (SFuel @u0)
@a1
@x2)
(DList.lt__2907 ZFuel
@a1
@x2))
  
:pattern ((DList.lt__2907 (SFuel @u0)
@a1
@x2)))))
;;;;;;;;;;;;;;;;Equation for fuel-instrumented recursive function: DList.lt
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(Prims.list (DList.dList @a1))))
(= (DList.lt__2907 (SFuel @u0)
@a1
@x2)
(ite (is-Prims.Nil @x2)
(BoxInt 1)
(ite (is-Prims.Cons @x2)
(Prims.op_Addition (BoxInt 1)
(Prims.op_Addition (DList.ld @a1
(Prims.Cons_hd @x2))
(DList.lt__2907 @u0
@a1
(Prims.Cons_tl @x2))))
Term_unit))))
  
:pattern ((DList.lt__2907 (SFuel @u0)
@a1
@x2)))))

; </end encoding DList.lt>

; encoding sigelt 

; <Skipped />
(push)

; Starting query at /home/hritcu/Projects/fstar/pub/examples/bug-reports/bug442.fst(38,0-40,3)
(pop)

; Ending query at /home/hritcu/Projects/fstar/pub/examples/bug-reports/bug442.fst(38,0-40,3)

; encoding sigelt DList.finish

; <Skipped DList.finish/>
(push)

; encoding sigelt DList.walk

; <Skipped DList.walk/>
(push)

; Starting query at /home/hritcu/Projects/fstar/pub/examples/bug-reports/bug442.fst(42,0-54,0)
;;;;;;;;;;;;;;;;'a
(declare-fun _a___5_3146 () Type)
(assert (HasKind _a___5_3146
Kind_type))
;;;;;;;;;;;;;;;;'t
(declare-fun _t___5_3147 () Type)
(assert (HasKind _t___5_3147
Kind_type))
;;;;;;;;;;;;;;;;rights : (list (dList 't)) ((list l:(dList1 't){(isCorrectJoined l)}))
(declare-fun rights___5_63 () Term)
(declare-fun Typ_refine_2925 () Type)
(assert (HasKind Typ_refine_2925
Kind_type))
;;;;;;;;;;;;;;;;l:(dList1 't){(isCorrectJoined l)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasTypeFuel @u0
@x1
Typ_refine_2925)
(and (HasTypeFuel @u0
@x1
(DList.dList1 _t___5_3147))
(BoxBool_proj_0 (DList.isCorrectJoined _t___5_3147
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2925)))))
(assert (HasType rights___5_63
(Prims.list Typ_refine_2925)))
;;;;;;;;;;;;;;;;l : (dList 't) (l:(dList1 't){(isCorrectJoined l)})
(declare-fun l___5_64 () Term)
(assert (HasType l___5_64
Typ_refine_2925))
;;;;;;;;;;;;;;;;xs : 'a ('a)
(declare-fun xs___5_65 () Term)
(assert (HasType xs___5_65
_a___5_3146))
;;;;;;;;;;;;;;;;f : ('a -> 't -> Tot 'a) (('a -> 't -> Tot 'a))
(declare-fun f___5_66 () Term)
;;;;;;;;;;;;;;;;('a -> 't -> Tot 'a)
(declare-fun Typ_fun_2928 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2928 kinding
(assert (HasKind Typ_fun_2928
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2928)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2928)))))
;;;;;;;;;;;;;;;;Typ_fun_2928 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2928)
(forall ((@x1 Term) (@x2 Term))
 (! (implies (and (HasType @x1
_a___5_3146)
(HasType @x2
_t___5_3147))
(HasType (ApplyEE (ApplyEE @x0
@x1)
@x2)
_a___5_3146))
  
:pattern ((ApplyEE (ApplyEE @x0
@x1)
@x2)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2928)))))
(assert (HasType f___5_66
Typ_fun_2928))
;;;;;;;;;;;;;;;;('a -> 't -> Tot 'a)
(declare-fun Typ_fun_2931 (Type Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_2931 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_2931 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_2931 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel @u0
@x1
(Typ_fun_2931 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_2931 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_2931 interpretation
(assert (forall ((@x0 Term) (@a1 Type) (@a2 Type))
 (! (iff (HasTypeZ @x0
(Typ_fun_2931 @a1
@a2))
(forall ((@x3 Term) (@x4 Term))
 (! (implies (and (HasType @x3
@a2)
(HasType @x4
@a1))
(HasType (ApplyEE (ApplyEE @x0
@x3)
@x4)
@a2))
  
:pattern ((ApplyEE (ApplyEE @x0
@x3)
@x4)))))
  
:pattern ((HasTypeZ @x0
(Typ_fun_2931 @a1
@a2))))))
(declare-fun Typ_refine_2934 (Term Type Type) Type)
(assert (forall ((@x0 Term) (@a1 Type) (@a2 Type))
 (! (HasKind (Typ_refine_2934 @x0
@a1
@a2)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2934 @x0
@a1
@a2)
Kind_type)))))
;;;;;;;;;;;;;;;;_5_3159:('a -> 't -> Tot 'a){(%[(lt rights); 1] << %[((ld l) + (lt rights)); 0])}
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@a3 Type) (@a4 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_2934 @x2
@a3
@a4))
(and (HasTypeFuel @u0
@x1
(Typ_fun_2931 @a4
@a3))
(Valid (Prims.Precedes Prims.lex_t
Prims.lex_t
(LexCons (DList.lt @a4
@x2)
(LexCons (BoxInt 1)
Prims.LexTop@tok))
(LexCons (Prims.op_Addition (DList.ld _t___5_3147
l___5_64)
(DList.lt _t___5_3147
rights___5_63))
(LexCons (BoxInt 0)
Prims.LexTop@tok))))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2934 @x2
@a3
@a4))))))
(declare-fun DList.finish (Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;(rights:(list (dList 't)) -> xs:'a -> f:_5_3159:('a -> 't -> Tot 'a){(%[(lt rights); 1] << %[((ld l) + (lt rights)); 0])} -> Tot 'a (decreases %[(lt rights); 1]))
(declare-fun Typ_fun_2938 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2938 kinding
(assert (HasKind Typ_fun_2938
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2938)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2938)))))
;;;;;;;;;;;;;;;;Typ_fun_2938 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2938)
(forall ((@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.list (DList.dList @a2)))
(HasType @x4
@a1)
(HasType @x5
(Typ_refine_2934 @x3
@a1
@a2)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
@x5)
@a1))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
@x5)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2938)))))
(declare-fun DList.finish@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2940
(Term_constr_id DList.finish@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET DList.finish@tok
@a0)
@a1)
@x2)
@x3)
@x4)
(DList.finish @a0
@a1
@x2
@x3
@x4))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET DList.finish@tok
@a0)
@a1)
@x2)
@x3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.finish@tok
Typ_fun_2938))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.list (DList.dList @a1)))
(HasType @x3
@a0)
(HasType @x4
(Typ_refine_2934 @x2
@a0
@a1)))
(HasType (DList.finish @a0
@a1
@x2
@x3
@x4)
@a0))
  
:pattern ((DList.finish @a0
@a1
@x2
@x3
@x4)))))
(declare-fun Typ_refine_2943 (Term Term Type Type) Type)
(assert (forall ((@x0 Term) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (HasKind (Typ_refine_2943 @x0
@x1
@a2
@a3)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2943 @x0
@x1
@a2
@a3)
Kind_type)))))
;;;;;;;;;;;;;;;;_5_3569:('a -> 't -> Tot 'a){(%[((ld l) + (lt rights)); 0] << %[((ld l) + (lt rights)); 0])}
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@x3 Term) (@a4 Type) (@a5 Type))
 (! (iff (HasTypeFuel @u0
@x1
(Typ_refine_2943 @x2
@x3
@a4
@a5))
(and (HasTypeFuel @u0
@x1
(Typ_fun_2931 @a5
@a4))
(Valid (Prims.Precedes Prims.lex_t
Prims.lex_t
(LexCons (Prims.op_Addition (DList.ld @a5
@x3)
(DList.lt @a5
@x2))
(LexCons (BoxInt 0)
Prims.LexTop@tok))
(LexCons (Prims.op_Addition (DList.ld _t___5_3147
l___5_64)
(DList.lt _t___5_3147
rights___5_63))
(LexCons (BoxInt 0)
Prims.LexTop@tok))))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2943 @x2
@x3
@a4
@a5))))))
(declare-fun DList.walk (Type Type Term Term Term Term) Term)
;;;;;;;;;;;;;;;;(rights:(list (dList 't)) -> l:(dList 't) -> xs:'a -> f:_5_3569:('a -> 't -> Tot 'a){(%[((ld l) + (lt rights)); 0] << %[((ld l) + (lt rights)); 0])} -> Tot 'a (decreases %[((ld l) + (lt rights)); 0]))
(declare-fun Typ_fun_2947 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2947 kinding
(assert (HasKind Typ_fun_2947
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel @u0
@x1
Typ_fun_2947)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2947)))))
;;;;;;;;;;;;;;;;Typ_fun_2947 interpretation
(assert (forall ((@x0 Term))
 (! (iff (HasTypeZ @x0
Typ_fun_2947)
(forall ((@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.list (DList.dList @a2)))
(HasType @x4
(DList.dList @a2))
(HasType @x5
@a1)
(HasType @x6
(Typ_refine_2943 @x3
@x4
@a1
@a2)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
@x5)
@x6)
@a1))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x0
@a1)
@a2)
@x3)
@x4)
@x5)
@x6)))))
  
:pattern ((HasTypeZ @x0
Typ_fun_2947)))))
(declare-fun DList.walk@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2949
(Term_constr_id DList.walk@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET DList.walk@tok
@a0)
@a1)
@x2)
@x3)
@x4)
@x5)
(DList.walk @a0
@a1
@x2
@x3
@x4
@x5))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET DList.walk@tok
@a0)
@a1)
@x2)
@x3)
@x4)
@x5)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType DList.walk@tok
Typ_fun_2947))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.list (DList.dList @a1)))
(HasType @x3
(DList.dList @a1))
(HasType @x4
@a0)
(HasType @x5
(Typ_refine_2943 @x2
@x3
@a0
@a1)))
(HasType (DList.walk @a0
@a1
@x2
@x3
@x4
@x5)
@a0))
  
:pattern ((DList.walk @a0
@a1
@x2
@x3
@x4
@x5)))))
(declare-fun label_2951 () Bool)
(declare-fun label_2950 () Bool)
(declare-fun label_2953 () Bool)
(declare-fun label_2952 () Bool)
(declare-fun label_2961 () Bool)
(declare-fun label_2959 () Bool)
(declare-fun label_2958 () Bool)
(declare-fun label_2957 () Bool)
(declare-fun label_2962 () Bool)
(push)

; <fuel='2' ifuel='1'>
(assert (= MaxFuel
(SFuel (SFuel ZFuel))))
(assert (= MaxIFuel
(SFuel ZFuel)))
;;;;;;;;;;;;;;;;query
(assert (not (ite (= (DList.is_Nil _t___5_3147
                                   l___5_64)
                     (BoxBool true))
                  (implies (= l___5_64
                              (DList.Nil _t___5_3147))
                           (or label_2950
                               true))
                  (ite (= (DList.is_Unit _t___5_3147
                                         l___5_64)
                          (BoxBool true))
                       (forall ((@x0 Term))
                               (implies (and (HasType @x0
                                                      _t___5_3147)
                                             (= l___5_64
                                                (DList.Unit _t___5_3147
                                                            @x0)))
                                        (or label_2952
                                            true)));;no pats

                       (ite (= (DList.is_Join _t___5_3147
                                              l___5_64)
                               (BoxBool true))
                            (forall ((@x0 Term) (@x1 Term) (@x2 Term))
                                    (implies (and (HasType @x0
                                                           (DList.dList1 _t___5_3147))
                                                  (HasType @x1
                                                           (DList.dList1 _t___5_3147))
                                                  (HasType @x2
                                                           Typ_refine_2242)
                                                  (= l___5_64
                                                     (DList.Join _t___5_3147
                                                                 @x0
                                                                 @x1
                                                                 @x2)))
                                             (and (or label_2961
                                                      (BoxBool_proj_0 (DList.isCorrectJoined _t___5_3147
                                                                                             @x1)))
                                                  (forall ((@x3 Term))
                                                          (implies (and (HasType @x3
                                                                                 (Prims.list Typ_refine_2925))
                                                                        (= @x3
                                                                           (Prims.Cons Typ_refine_2925
                                                                                       @x1
                                                                                       rights___5_63)))
                                                                   (and (or label_2958
                                                                            (BoxBool_proj_0 (DList.isCorrectJoined _t___5_3147
                                                                                                                   @x0)))
                                                                        (or label_2957
                                                                            true))));;no pats
                                                  )));;no pats

label_2962)))))
(check-sat)
(echo "label_2951")
(eval label_2951)
(echo "label_2950")
(eval label_2950)
(echo "label_2953")
(eval label_2953)
(echo "label_2952")
(eval label_2952)
(echo "label_2961")
(eval label_2961)
(echo "label_2959")
(eval label_2959)
(echo "label_2958")
(eval label_2958)
(echo "label_2957")
(eval label_2957)
(echo "label_2962")
(eval label_2962)
(echo "Done!")
(pop)
(push)
