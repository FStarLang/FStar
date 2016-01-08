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
(define-fun HasType ((x Term) (t Type)) Bool
(HasTypeFuel MaxIFuel x t))

                (define-fun  IsTyped ((x Term)) Bool
(exists ((t Type)) (HasType x t)))
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
 (= 0
(String_constr_id (String_const @u0)))))
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
 (= 1
(Kind_constr_id (Kind_arrow @u0)))))
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
 (= 2
(Kind_constr_id (Kind_uvar @u0)))))
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
 (= 1
(Type_constr_id (Typ_fun @u0)))))
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
 (= 2
(Type_constr_id (Typ_app @a0
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
 (= 3
(Type_constr_id (Typ_dep @a0
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
 (= 4
(Type_constr_id (Typ_uvar @u0)))))
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
 (= 1
(Term_constr_id (BoxInt @u0)))))
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
 (= 2
(Term_constr_id (BoxBool @u0)))))
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
 (= 3
(Term_constr_id (BoxString @u0)))))
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
 (= 4
(Term_constr_id (BoxRef @u0)))))
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
 (= 5
(Term_constr_id (Exp_uvar @u0)))))
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
 (= 6
(Term_constr_id (LexCons @x0
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
 (! (implies (HasType @x1
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
 (= 20
(Type_constr_id (Prims.Eq2 @a0
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
 (! (implies (HasType @x1
Typ_fun_37)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_37)))))
;;;;;;;;;;;;;;;;Typ_fun_37 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_37)
(forall ((@x2 Term))
 (! (implies (HasType @x2
Prims.True)
(HasType (ApplyEE @x1
@x2)
Prims.bool))
  
:pattern ((ApplyEE @x1
@x2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_37)))))
(declare-fun Prims.is_T@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 40
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
(assert (= 42
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
(declare-fun Typ_fun_44 (Type Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_44 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_44 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_44 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasType @x1
(Typ_fun_44 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_44 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_44 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_fun_44 @a2
@a3))
(forall ((@x4 Term))
 (! (implies (HasType @x4
@a3)
(HasType (ApplyEE @x1
@x4)
@a2))
  
:pattern ((ApplyEE @x1
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_44 @a2
@a3))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type))
(= (Prims.l_imp @a0
@a1)
(Typ_fun_44 @a1
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
;;;;;;;;;;;;;;;;(p -> q -> Tot p)
(declare-fun Typ_fun_68 (Term) Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.And (Type Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And_p (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.And_q (Term) Type)
;;;;;;;;;;;;;;;;(p -> q -> Tot p)
(declare-fun Typ_fun_78 (Type Type) Type)
;;;;;;;;;;;;;;;;( -> Tot ((p -> q -> Tot p) /\ q))
(declare-fun Typ_fun_81 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: And
(declare-fun Prims.And@tok () Term)

; <Start encoding Prims.l_and>

; <start constructor Prims.l_and>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (= 64
(Type_constr_id (Prims.l_and @a0
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
64)
(= @a0
(Prims.l_and (Prims.l_and@a0 @a0)
(Prims.l_and@a1 @a0)))))

; </end constructor Prims.l_and>
;;;;;;;;;;;;;;;;fresh token
(assert (= 65
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
;;;;;;;;;;;;;;;;Typ_fun_68 kinding
(assert (forall ((@x0 Term))
 (! (HasKind (Typ_fun_68 @x0)
Kind_type)
  
:pattern ((HasKind (Typ_fun_68 @x0)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (implies (HasType @x1
(Typ_fun_68 @x2))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_68 @x2))))))
;;;;;;;;;;;;;;;;Typ_fun_68 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (iff (HasType @x1
(Typ_fun_68 @x2))
(forall ((@x3 Term) (@x4 Term))
 (! (implies (and (HasType @x3
(Prims.And_p @x2))
(HasType @x4
(Prims.And_q @x2)))
(HasType (ApplyEE (ApplyEE @x1
@x3)
@x4)
(Prims.And_p @x2)))
  
:pattern ((ApplyEE (ApplyEE @x1
@x3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_68 @x2))))))
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
(assert (forall ((@a0 Type) (@a1 Type))
 (= 75
(Term_constr_id (Prims.And @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.And_p (Prims.And @a0
@a1))
@a0)
  
:pattern ((Prims.And @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.And_q (Prims.And @a0
@a1))
@a1)
  
:pattern ((Prims.And @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.And ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
75)
(= @x0
(Prims.And (Prims.And_p @x0)
(Prims.And_q @x0)))))

; </end constructor Prims.And>
;;;;;;;;;;;;;;;;Typ_fun_78 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_78 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_78 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasType @x1
(Typ_fun_78 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_78 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_78 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_fun_78 @a2
@a3))
(forall ((@x4 Term) (@x5 Term))
 (! (implies (and (HasType @x4
@a3)
(HasType @x5
@a2))
(HasType (ApplyEE (ApplyEE @x1
@x4)
@x5)
@a3))
  
:pattern ((ApplyEE (ApplyEE @x1
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_78 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_81 kinding
(assert (HasKind Typ_fun_81
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_81)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_81)))))
;;;;;;;;;;;;;;;;Typ_fun_81 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_81)
(forall ((@a2 Type) (@a3 Type))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type))
(HasType (ApplyET (ApplyET @x1
@a2)
@a3)
(Prims.l_and (Typ_fun_78 @a3
@a2)
@a3)))
  
:pattern ((ApplyET (ApplyET @x1
@a2)
@a3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_81)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 85
(Term_constr_id Prims.And@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.And@tok
Typ_fun_81))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyET (ApplyET Prims.And@tok
@a0)
@a1)
(Prims.And @a0
@a1))
  
:pattern ((ApplyET (ApplyET Prims.And@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type))
(HasTypeFuel @u0
(Prims.And @a1
@a2)
(Prims.l_and (Typ_fun_78 @a2
@a1)
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.And @a1
@a2)
(Prims.l_and (Typ_fun_78 @a2
@a1)
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.And @a1
@a2)
(Prims.l_and @a3
@a4))
(and (= @a2
@a4)
(= (Typ_fun_78 @a2
@a1)
@a3)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.And @a1
@a2)
(Prims.l_and @a3
@a4))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.And>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.l_and @a2
@a3))
(and (is-Prims.And @x1)
(= @a2
(Typ_fun_68 @x1))
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
(declare-fun Typ_fun_88 () Type)
;;;;;;;;;;;;;;;;Typ_fun_88 kinding
(assert (HasKind Typ_fun_88
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_88)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_88)))))
;;;;;;;;;;;;;;;;Typ_fun_88 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_88)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.l_and @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_88)))))
(declare-fun Prims.is_And@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 91
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
Typ_fun_88))
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

; encoding sigelt Prims.And.p

; <Start encoding Prims.And.p>
(declare-fun Prims.And.p (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.And.p@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 93
(Type_constr_id Prims.And.p@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.And.p@tok
@a0)
@a1)
@x2)
(Prims.And.p @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.And.p@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.And.p@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_and @a0
@a1)))
(HasKind (Prims.And.p @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.And.p @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.And.p @a0
@a1
@x2)
(Prims.And_p @x2))
  
:pattern ((Prims.And.p @a0
@a1
@x2)))))

; </end encoding Prims.And.p>

; encoding sigelt Prims.And.q

; <Start encoding Prims.And.q>
(declare-fun Prims.And.q (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.And.q@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 95
(Type_constr_id Prims.And.q@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.And.q@tok
@a0)
@a1)
@x2)
(Prims.And.q @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.And.q@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.And.q@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.l_and @a0
@a1)))
(HasKind (Prims.And.q @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.And.q @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.And.q @a0
@a1
@x2)
(Prims.And_q @x2))
  
:pattern ((Prims.And.q @a0
@a1
@x2)))))

; </end encoding Prims.And.q>

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
;;;;;;;;;;;;;;;;(p -> Tot p)
(declare-fun Typ_fun_127 (Term) Type)
;;;;;;;;;;;;;;;;(q -> Tot p)
(declare-fun Typ_fun_131 (Term) Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Left (Type Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left_p (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Left_q (Term) Type)
;;;;;;;;;;;;;;;;(p -> Tot p)
(declare-fun Typ_fun_141 (Type) Type)
;;;;;;;;;;;;;;;;( -> Tot ((p -> Tot p) \/ q))
(declare-fun Typ_fun_144 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Left
(declare-fun Prims.Left@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Right (Type Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right_p (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Right_q (Term) Type)
;;;;;;;;;;;;;;;;( -> Tot ((q -> Tot p) \/ q))
(declare-fun Typ_fun_154 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Right
(declare-fun Prims.Right@tok () Term)

; <Start encoding Prims.l_or>

; <start constructor Prims.l_or>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (= 123
(Type_constr_id (Prims.l_or @a0
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
123)
(= @a0
(Prims.l_or (Prims.l_or@a0 @a0)
(Prims.l_or@a1 @a0)))))

; </end constructor Prims.l_or>
;;;;;;;;;;;;;;;;fresh token
(assert (= 124
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
;;;;;;;;;;;;;;;;Typ_fun_127 kinding
(assert (forall ((@x0 Term))
 (! (HasKind (Typ_fun_127 @x0)
Kind_type)
  
:pattern ((HasKind (Typ_fun_127 @x0)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (implies (HasType @x1
(Typ_fun_127 @x2))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_127 @x2))))))
;;;;;;;;;;;;;;;;Typ_fun_127 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (iff (HasType @x1
(Typ_fun_127 @x2))
(forall ((@x3 Term))
 (! (implies (HasType @x3
(Prims.Left_p @x2))
(HasType (ApplyEE @x1
@x3)
(Prims.Left_p @x2)))
  
:pattern ((ApplyEE @x1
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_127 @x2))))))
;;;;;;;;;;;;;;;;Typ_fun_131 kinding
(assert (forall ((@x0 Term))
 (! (HasKind (Typ_fun_131 @x0)
Kind_type)
  
:pattern ((HasKind (Typ_fun_131 @x0)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (implies (HasType @x1
(Typ_fun_131 @x2))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_131 @x2))))))
;;;;;;;;;;;;;;;;Typ_fun_131 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term))
 (! (iff (HasType @x1
(Typ_fun_131 @x2))
(forall ((@x3 Term))
 (! (implies (HasType @x3
(Prims.Right_q @x2))
(HasType (ApplyEE @x1
@x3)
(Prims.Right_p @x2)))
  
:pattern ((ApplyEE @x1
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_131 @x2))))))
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
(assert (forall ((@a0 Type) (@a1 Type))
 (= 138
(Term_constr_id (Prims.Left @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.Left_p (Prims.Left @a0
@a1))
@a0)
  
:pattern ((Prims.Left @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.Left_q (Prims.Left @a0
@a1))
@a1)
  
:pattern ((Prims.Left @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Left ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
138)
(= @x0
(Prims.Left (Prims.Left_p @x0)
(Prims.Left_q @x0)))))

; </end constructor Prims.Left>
;;;;;;;;;;;;;;;;Typ_fun_141 kinding
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_fun_141 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_fun_141 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasType @x1
(Typ_fun_141 @a2))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_141 @a2))))))
;;;;;;;;;;;;;;;;Typ_fun_141 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_fun_141 @a2))
(forall ((@x3 Term))
 (! (implies (HasType @x3
@a2)
(HasType (ApplyEE @x1
@x3)
@a2))
  
:pattern ((ApplyEE @x1
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_141 @a2))))))
;;;;;;;;;;;;;;;;Typ_fun_144 kinding
(assert (HasKind Typ_fun_144
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_144)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_144)))))
;;;;;;;;;;;;;;;;Typ_fun_144 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_144)
(forall ((@a2 Type) (@a3 Type))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type))
(HasType (ApplyET (ApplyET @x1
@a2)
@a3)
(Prims.l_or (Typ_fun_141 @a2)
@a3)))
  
:pattern ((ApplyET (ApplyET @x1
@a2)
@a3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_144)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 148
(Term_constr_id Prims.Left@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Left@tok
Typ_fun_144))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyET (ApplyET Prims.Left@tok
@a0)
@a1)
(Prims.Left @a0
@a1))
  
:pattern ((ApplyET (ApplyET Prims.Left@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type))
(HasTypeFuel @u0
(Prims.Left @a1
@a2)
(Prims.l_or (Typ_fun_141 @a1)
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.Left @a1
@a2)
(Prims.l_or (Typ_fun_141 @a1)
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Left @a1
@a2)
(Prims.l_or @a3
@a4))
(and (= @a2
@a4)
(= (Typ_fun_141 @a1)
@a3)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Left @a1
@a2)
(Prims.l_or @a3
@a4))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.Left>

; <Start encoding Prims.Right>

; <start constructor Prims.Right>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (= 151
(Term_constr_id (Prims.Right @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.Right_p (Prims.Right @a0
@a1))
@a0)
  
:pattern ((Prims.Right @a0
@a1)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (Prims.Right_q (Prims.Right @a0
@a1))
@a1)
  
:pattern ((Prims.Right @a0
@a1)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Right ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
151)
(= @x0
(Prims.Right (Prims.Right_p @x0)
(Prims.Right_q @x0)))))

; </end constructor Prims.Right>
;;;;;;;;;;;;;;;;Typ_fun_154 kinding
(assert (HasKind Typ_fun_154
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_154)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_154)))))
;;;;;;;;;;;;;;;;Typ_fun_154 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_154)
(forall ((@a2 Type) (@a3 Type))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type))
(HasType (ApplyET (ApplyET @x1
@a2)
@a3)
(Prims.l_or (Typ_fun_44 @a2
@a3)
@a3)))
  
:pattern ((ApplyET (ApplyET @x1
@a2)
@a3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_154)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 158
(Term_constr_id Prims.Right@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Right@tok
Typ_fun_154))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type))
 (! (= (ApplyET (ApplyET Prims.Right@tok
@a0)
@a1)
(Prims.Right @a0
@a1))
  
:pattern ((ApplyET (ApplyET Prims.Right@tok
@a0)
@a1)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type))
(HasTypeFuel @u0
(Prims.Right @a1
@a2)
(Prims.l_or (Typ_fun_44 @a1
@a2)
@a2)))
  
:pattern ((HasTypeFuel @u0
(Prims.Right @a1
@a2)
(Prims.l_or (Typ_fun_44 @a1
@a2)
@a2))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
(Prims.Right @a1
@a2)
(Prims.l_or @a3
@a4))
(and (= @a2
@a4)
(= (Typ_fun_44 @a1
@a2)
@a3)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)))
  
:pattern ((HasTypeFuel (SFuel @u0)
(Prims.Right @a1
@a2)
(Prims.l_or @a3
@a4))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert true)

; </end encoding Prims.Right>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(Prims.l_or @a2
@a3))
(or (and (is-Prims.Left @x1)
(= @a2
(Typ_fun_127 @x1))
(= @a3
(Prims.Left_q @x1)))
(and (is-Prims.Right @x1)
(= @a2
(Typ_fun_131 @x1))
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
(declare-fun Typ_fun_161 () Type)
;;;;;;;;;;;;;;;;Typ_fun_161 kinding
(assert (HasKind Typ_fun_161
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_161)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_161)))))
;;;;;;;;;;;;;;;;Typ_fun_161 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_161)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.l_or @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_161)))))
(declare-fun Prims.is_Left@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 164
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
Typ_fun_161))
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
(assert (= 166
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
Typ_fun_161))
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

; encoding sigelt Prims.Left.p

; <Start encoding Prims.Left.p>
(declare-fun Prims.Left.p (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Left.p@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 170
(Type_constr_id Prims.Left.p@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Left.p@tok
@a0)
@a1)
@x2)
(Prims.Left.p @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Left.p@tok
@a0)
@a1)
@x2)))))
(declare-fun Typ_refine_167 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_167 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_167 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_16:(p \/ q){(is_Left _0_16)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_refine_167 @a2
@a3))
(and (HasType @x1
(Prims.l_or @a3
@a2))
(Valid (Prims.b2t (Prims.is_Left @a3
@a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_167 @a2
@a3))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Left.p@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_167 @a1
@a0)))
(HasKind (Prims.Left.p @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Left.p @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Left.p @a0
@a1
@x2)
(Prims.Left_p @x2))
  
:pattern ((Prims.Left.p @a0
@a1
@x2)))))

; </end encoding Prims.Left.p>

; encoding sigelt Prims.Left.q

; <Start encoding Prims.Left.q>
(declare-fun Prims.Left.q (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Left.q@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 172
(Type_constr_id Prims.Left.q@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Left.q@tok
@a0)
@a1)
@x2)
(Prims.Left.q @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Left.q@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Left.q@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_167 @a1
@a0)))
(HasKind (Prims.Left.q @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Left.q @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Left.q @a0
@a1
@x2)
(Prims.Left_q @x2))
  
:pattern ((Prims.Left.q @a0
@a1
@x2)))))

; </end encoding Prims.Left.q>

; encoding sigelt Prims.Right.p

; <Start encoding Prims.Right.p>
(declare-fun Prims.Right.p (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Right.p@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 176
(Type_constr_id Prims.Right.p@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Right.p@tok
@a0)
@a1)
@x2)
(Prims.Right.p @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Right.p@tok
@a0)
@a1)
@x2)))))
(declare-fun Typ_refine_173 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_173 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_173 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_18:(p \/ q){(is_Right _0_18)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_refine_173 @a2
@a3))
(and (HasType @x1
(Prims.l_or @a3
@a2))
(Valid (Prims.b2t (Prims.is_Right @a3
@a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_173 @a2
@a3))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Right.p@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_173 @a1
@a0)))
(HasKind (Prims.Right.p @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Right.p @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Right.p @a0
@a1
@x2)
(Prims.Right_p @x2))
  
:pattern ((Prims.Right.p @a0
@a1
@x2)))))

; </end encoding Prims.Right.p>

; encoding sigelt Prims.Right.q

; <Start encoding Prims.Right.q>
(declare-fun Prims.Right.q (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Right.q@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 178
(Type_constr_id Prims.Right.q@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Right.q@tok
@a0)
@a1)
@x2)
(Prims.Right.q @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Right.q@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Right.q@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_173 @a1
@a0)))
(HasKind (Prims.Right.q @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Right.q @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Right.q @a0
@a1
@x2)
(Prims.Right_q @x2))
  
:pattern ((Prims.Right.q @a0
@a1
@x2)))))

; </end encoding Prims.Right.q>

; encoding sigelt Prims.l_iff

; <Start encoding Prims.l_iff>
(declare-fun Prims.l_iff (Type Type) Type)
(declare-fun Prims.l_iff@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 179
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
(implies (and (Valid @a0)
(Valid @a1)
(Valid @a1))
(Valid @a0))))
  
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
(assert (= 180
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
(declare-fun Kind_arrow_182 (Type) Kind)
;;;;;;;;;;;;;;;;Kind_arrow_182 interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (HasKind @a0
(Kind_arrow_182 @a1))
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
(Kind_arrow_182 @a1))))))
(declare-fun Prims.Forall (Type Type) Type)
(declare-fun Prims.Forall@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 183
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
(declare-fun Typ_fun_185 (Type Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_185 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_185 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_185 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasType @x1
(Typ_fun_185 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_185 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_185 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_fun_185 @a2
@a3))
(forall ((@x4 Term))
 (! (implies (HasType @x4
@a3)
(HasType (ApplyEE @x1
@x4)
(ApplyTE @a2
@x4)))
  
:pattern ((ApplyEE @x1
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_185 @a2
@a3))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0)))
(= (Prims.Forall @a0
@a1)
(Typ_fun_185 @a1
@a0)))
  
:pattern ((Prims.Forall @a0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0)))
(HasKind (Prims.Forall @a0
@a1)
Kind_type))
  
:pattern ((Prims.Forall @a0
@a1)))))
;;;;;;;;;;;;;;;;forall interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (forall ((@x2 Term))
 (! (implies (HasType @x2
@a0)
(Valid (ApplyTE @a1
@x2)))
  
:pattern ((HasType @x2
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
(declare-fun Typ_fun_216 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkDTuple2
(declare-fun Prims.MkDTuple2@tok () Term)

; <Start encoding Prims.DTuple2>

; <start constructor Prims.DTuple2>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (= 205
(Type_constr_id (Prims.DTuple2 @a0
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
205)
(= @a0
(Prims.DTuple2 (Prims.DTuple2@a0 @a0)
(Prims.DTuple2@a1 @a0)))))

; </end constructor Prims.DTuple2>
;;;;;;;;;;;;;;;;fresh token
(assert (= 206
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
@a1)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.DTuple2@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0)))
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
 (= 213
(Term_constr_id (Prims.MkDTuple2 @a0
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
213)
(= @x0
(Prims.MkDTuple2 (Prims.MkDTuple2_a @x0)
(Prims.MkDTuple2_b @x0)
(Prims.MkDTuple2__1 @x0)
(Prims.MkDTuple2__2 @x0)))))

; </end constructor Prims.MkDTuple2>
;;;;;;;;;;;;;;;;Typ_fun_216 kinding
(assert (HasKind Typ_fun_216
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_216)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_216)))))
;;;;;;;;;;;;;;;;Typ_fun_216 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_216)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasType @x4
@a2)
(HasType @x5
(ApplyTE @a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
(Prims.DTuple2 @a2
@a3)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_216)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 220
(Term_constr_id Prims.MkDTuple2@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkDTuple2@tok
Typ_fun_216))
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
(Kind_arrow_182 @a1))
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
(Kind_arrow_182 @a1))
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
(declare-fun Typ_fun_225 () Type)
;;;;;;;;;;;;;;;;Typ_fun_225 kinding
(assert (HasKind Typ_fun_225
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_225)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_225)))))
;;;;;;;;;;;;;;;;Typ_fun_225 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_225)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasType @x4
(Prims.DTuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_225)))))
(declare-fun Prims.is_MkDTuple2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 228
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
Typ_fun_225))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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
(assert (= 232
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
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple2.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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
(assert (= 236
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
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple2.b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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
(declare-fun Typ_fun_241 () Type)
;;;;;;;;;;;;;;;;Typ_fun_241 kinding
(assert (HasKind Typ_fun_241
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_241)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_241)))))
;;;;;;;;;;;;;;;;Typ_fun_241 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_241)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasType @x4
(Prims.DTuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
(Prims.MkDTuple2.a @a2
@a3
@x4)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_241)))))
(declare-fun Prims.MkDTuple2._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 244
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
Typ_fun_241))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.MkDTuple2__1 @x2)
(Prims.MkDTuple2.a @a0
@a1
@x2)))
  
:pattern ((HasType (Prims.MkDTuple2__1 @x2)
(Prims.MkDTuple2.a @a0
@a1
@x2))))))

; </end encoding Prims.MkDTuple2._1>

; encoding sigelt Prims.MkDTuple2._2

; <Start encoding Prims.MkDTuple2._2>
(declare-fun Prims.MkDTuple2._2 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple2 a b) -> Tot (b projectee (_1 projectee)))
(declare-fun Typ_fun_249 () Type)
;;;;;;;;;;;;;;;;Typ_fun_249 kinding
(assert (HasKind Typ_fun_249
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_249)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_249)))))
;;;;;;;;;;;;;;;;Typ_fun_249 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_249)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasType @x4
(Prims.DTuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
(Prims.MkDTuple2.b @a2
@a3
@x4
(Prims.MkDTuple2._1 @a2
@a3
@x4))))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_249)))))
(declare-fun Prims.MkDTuple2._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 252
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
Typ_fun_249))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasType @x2
(Prims.DTuple2 @a0
@a1)))
(HasType (Prims.MkDTuple2__2 @x2)
(Prims.MkDTuple2.b @a0
@a1
@x2
(Prims.MkDTuple2._1 @a0
@a1
@x2))))
  
:pattern ((HasType (Prims.MkDTuple2__2 @x2)
(Prims.MkDTuple2.b @a0
@a1
@x2
(Prims.MkDTuple2._1 @a0
@a1
@x2)))))))

; </end encoding Prims.MkDTuple2._2>

; encoding sigelt Prims.Exists

; <Start encoding Prims.Exists>
(declare-fun Prims.Exists (Type Type) Type)
(declare-fun Prims.Exists@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 256
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
(Kind_arrow_182 @a0)))
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
(Kind_arrow_182 @a0)))
(HasKind (Prims.Exists @a0
@a1)
Kind_type))
  
:pattern ((Prims.Exists @a0
@a1)))))
;;;;;;;;;;;;;;;;exists interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (exists ((@x2 Term))
 (! (implies (HasType @x2
@a0)
(Valid (ApplyTE @a1
@x2)))
  
:pattern ((HasType @x2
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
(assert (= 257
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
(assert (= 258
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
(assert (= 262
(Type_constr_id Prims.ForallTyp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.ForallTyp@tok
@a0)
(Prims.ForallTyp @a0))
  
:pattern ((ApplyTT Prims.ForallTyp@tok
@a0)))))
;;;;;;;;;;;;;;;;(Type -> Type)
(declare-fun Kind_arrow_260 () Kind)
;;;;;;;;;;;;;;;;Kind_arrow_260 interpretation
(assert (forall ((@a0 Type))
 (! (iff (HasKind @a0
Kind_arrow_260)
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
Kind_arrow_260)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.ForallTyp@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_arrow_260)
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
(assert (= 265
(Type_constr_id Prims.ExistsTyp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.ExistsTyp@tok
@a0)
(Prims.ExistsTyp @a0))
  
:pattern ((ApplyTT Prims.ExistsTyp@tok
@a0)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.ExistsTyp@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_arrow_260)
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
(assert (= 534
(Type_constr_id Prims.unit)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.unit ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
534)
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
 (! (implies (HasType @x1
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
(assert (= 538
(Type_constr_id Prims.int)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.int ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
538)
(= @a0
Prims.int)))

; </end constructor Prims.int>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.int
Kind_type))
;;;;;;;;;;;;;;;;int inversion
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
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
 (! (implies (and (HasType @x1
Prims.int)
(HasType @x2
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
(declare-fun Typ_refine_543 () Type)
(assert (HasKind Typ_refine_543
Kind_type))
;;;;;;;;;;;;;;;;i:int{((i > (- 32769)) /\ (32768 > i))}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_543)
(and (HasType @x1
Prims.int)
(Valid (Prims.b2t (Prims.op_GreaterThan @x1
(Prims.op_Minus (BoxInt 32769)))))
(Valid (Prims.b2t (Prims.op_GreaterThan (BoxInt 32768)
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_543)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.int16
Typ_refine_543))
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
(assert (= 545
(Type_constr_id Prims.int64)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.int64 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
545)
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
(assert (= 548
(Type_constr_id Prims.uint16)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.uint16 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
548)
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
(assert (= 551
(Type_constr_id Prims.uint32)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.uint32 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
551)
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
(assert (= 554
(Type_constr_id Prims.uint64)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.uint64 ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
554)
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
(assert (= 557
(Type_constr_id Prims.float)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.float ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
557)
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
(assert (= 560
(Type_constr_id Prims.string)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.string ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
560)
(= @a0
Prims.string)))

; </end constructor Prims.string>
;;;;;;;;;;;;;;;;kinding
(assert (HasKind Prims.string
Kind_type))
;;;;;;;;;;;;;;;;string inversion
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
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
 (= 564
(Type_constr_id (Prims.array @a0)))))
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
564)
(= @a0
(Prims.array (Prims.array@a0 @a0)))))

; </end constructor Prims.array>
;;;;;;;;;;;;;;;;token
(declare-fun Prims.array@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 565
(Type_constr_id Prims.array@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.array@tok
@a0)
(Prims.array @a0))
  
:pattern ((ApplyTT Prims.array@tok
@a0)))))
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

; encoding sigelt Prims.LBL

; <Start encoding Prims.LBL>
(declare-fun Prims.LBL (Term Type) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.LBL@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 569
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
(assert (= 570
(Type_constr_id Prims.exn)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.exn ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
570)
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
 (= 573
(Type_constr_id (Prims.HashMultiMap @a0
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
573)
(= @a0
(Prims.HashMultiMap (Prims.HashMultiMap@a0 @a0)
(Prims.HashMultiMap@a1 @a0)))))

; </end constructor Prims.HashMultiMap>
;;;;;;;;;;;;;;;;token
(declare-fun Prims.HashMultiMap@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 574
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
(declare-fun Typ_fun_604 () Type)
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
(declare-fun Typ_fun_611 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Cons
(declare-fun Prims.Cons@tok () Term)

; <Start encoding Prims.list>

; <start constructor Prims.list>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (= 595
(Type_constr_id (Prims.list @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.list@a0 (Prims.list @a0))
@a0)
  
:pattern ((Prims.list @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.list ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
595)
(= @a0
(Prims.list (Prims.list@a0 @a0)))))

; </end constructor Prims.list>
;;;;;;;;;;;;;;;;fresh token
(assert (= 596
(Type_constr_id Prims.list@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.list@tok
@a0)
(Prims.list @a0))
  
:pattern ((ApplyTT Prims.list@tok
@a0)))))
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
 (= 602
(Term_constr_id (Prims.Nil @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.Nil_a (Prims.Nil @a0))
@a0)
  
:pattern ((Prims.Nil @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.Nil ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
602)
(= @x0
(Prims.Nil (Prims.Nil_a @x0)))))

; </end constructor Prims.Nil>
;;;;;;;;;;;;;;;;Typ_fun_604 kinding
(assert (HasKind Typ_fun_604
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_604)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_604)))))
;;;;;;;;;;;;;;;;Typ_fun_604 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_604)
(forall ((@a2 Type))
 (! (implies (HasKind @a2
Kind_type)
(HasType (ApplyET @x1
@a2)
(Prims.list @a2)))
  
:pattern ((ApplyET @x1
@a2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_604)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 607
(Term_constr_id Prims.Nil@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Nil@tok
Typ_fun_604))
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
 (= 609
(Term_constr_id (Prims.Cons @a0
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
609)
(= @x0
(Prims.Cons (Prims.Cons_a @x0)
(Prims.Cons_hd @x0)
(Prims.Cons_tl @x0)))))

; </end constructor Prims.Cons>
;;;;;;;;;;;;;;;;Typ_fun_611 kinding
(assert (HasKind Typ_fun_611
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_611)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_611)))))
;;;;;;;;;;;;;;;;Typ_fun_611 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_611)
(forall ((@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
@a2)
(HasType @x4
(Prims.list @a2)))
(HasType (ApplyEE (ApplyEE (ApplyET @x1
@a2)
@x3)
@x4)
(Prims.list @a2)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x1
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_611)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 614
(Term_constr_id Prims.Cons@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Cons@tok
Typ_fun_611))
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
(declare-fun Typ_fun_616 () Type)
;;;;;;;;;;;;;;;;Typ_fun_616 kinding
(assert (HasKind Typ_fun_616
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_616)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_616)))))
;;;;;;;;;;;;;;;;Typ_fun_616 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_616)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Prims.list @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_616)))))
(declare-fun Prims.is_Nil@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 619
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
Typ_fun_616))
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
(assert (= 621
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
Typ_fun_616))
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

; encoding sigelt Prims.Nil.a

; <Start encoding Prims.Nil.a>
(declare-fun Prims.Nil.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Nil.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 625
(Type_constr_id Prims.Nil.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.Nil.a@tok
@a0)
@x1)
(Prims.Nil.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.Nil.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_622 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_622 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_622 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_143:(list a){(is_Nil _0_143)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_622 @a2))
(and (HasType @x1
(Prims.list @a2))
(Valid (Prims.b2t (Prims.is_Nil @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_622 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Nil.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_622 @a0)))
(HasKind (Prims.Nil.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.Nil.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Nil.a @a0
@x1)
(Prims.Nil_a @x1))
  
:pattern ((Prims.Nil.a @a0
@x1)))))

; </end encoding Prims.Nil.a>

; encoding sigelt Prims.Cons.a

; <Start encoding Prims.Cons.a>
(declare-fun Prims.Cons.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Cons.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 629
(Type_constr_id Prims.Cons.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.Cons.a@tok
@a0)
@x1)
(Prims.Cons.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.Cons.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_626 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_626 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_626 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_145:(list a){(is_Cons _0_145)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_626 @a2))
(and (HasType @x1
(Prims.list @a2))
(Valid (Prims.b2t (Prims.is_Cons @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_626 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Cons.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_626 @a0)))
(HasKind (Prims.Cons.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.Cons.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Cons.a @a0
@x1)
(Prims.Cons_a @x1))
  
:pattern ((Prims.Cons.a @a0
@x1)))))

; </end encoding Prims.Cons.a>

; encoding sigelt Prims.Cons.hd

; <Start encoding Prims.Cons.hd>
(declare-fun Prims.Cons.hd (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_145:(list a){(is_Cons _0_145)} -> Tot a)
(declare-fun Typ_fun_631 () Type)
;;;;;;;;;;;;;;;;Typ_fun_631 kinding
(assert (HasKind Typ_fun_631
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_631)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_631)))))
;;;;;;;;;;;;;;;;Typ_fun_631 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_631)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_626 @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_631)))))
(declare-fun Prims.Cons.hd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 634
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
Typ_fun_631))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_626 @a0)))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_626 @a0)))
(HasType (Prims.Cons_hd @x1)
@a0))
  
:pattern ((HasType (Prims.Cons_hd @x1)
@a0)))))

; </end encoding Prims.Cons.hd>

; encoding sigelt Prims.Cons.tl

; <Start encoding Prims.Cons.tl>
(declare-fun Prims.Cons.tl (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_145:(list a){(is_Cons _0_145)} -> Tot (list a))
(declare-fun Typ_fun_636 () Type)
;;;;;;;;;;;;;;;;Typ_fun_636 kinding
(assert (HasKind Typ_fun_636
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_636)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_636)))))
;;;;;;;;;;;;;;;;Typ_fun_636 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_636)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_626 @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
(Prims.list @a2)))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_636)))))
(declare-fun Prims.Cons.tl@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 639
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
Typ_fun_636))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_626 @a0)))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_626 @a0)))
(HasType (Prims.Cons_tl @x1)
(Prims.list @a0)))
  
:pattern ((HasType (Prims.Cons_tl @x1)
(Prims.list @a0))))))

; </end encoding Prims.Cons.tl>

; encoding sigelt Prims.pattern, Prims.SMTPat, Prims.SMTPatT

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
(declare-fun Typ_fun_665 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: SMTPat
(declare-fun Prims.SMTPat@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.SMTPatT (Type) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.SMTPatT_a (Term) Type)
;;;;;;;;;;;;;;;;(a:Type -> Tot pattern)
(declare-fun Typ_fun_672 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: SMTPatT
(declare-fun Prims.SMTPatT@tok () Term)

; <Start encoding Prims.pattern>

; <start constructor Prims.pattern>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (= 657
(Type_constr_id Prims.pattern)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.pattern ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
657)
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
 (= 663
(Term_constr_id (Prims.SMTPat @a0
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
663)
(= @x0
(Prims.SMTPat (Prims.SMTPat_a @x0)
(Prims.SMTPat__1 @x0)))))

; </end constructor Prims.SMTPat>
;;;;;;;;;;;;;;;;Typ_fun_665 kinding
(assert (HasKind Typ_fun_665
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_665)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_665)))))
;;;;;;;;;;;;;;;;Typ_fun_665 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_665)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
@a2))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.pattern))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_665)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 668
(Term_constr_id Prims.SMTPat@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.SMTPat@tok
Typ_fun_665))
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
 (= 670
(Term_constr_id (Prims.SMTPatT @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.SMTPatT_a (Prims.SMTPatT @a0))
@a0)
  
:pattern ((Prims.SMTPatT @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.SMTPatT ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
670)
(= @x0
(Prims.SMTPatT (Prims.SMTPatT_a @x0)))))

; </end constructor Prims.SMTPatT>
;;;;;;;;;;;;;;;;Typ_fun_672 kinding
(assert (HasKind Typ_fun_672
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_672)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_672)))))
;;;;;;;;;;;;;;;;Typ_fun_672 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_672)
(forall ((@a2 Type))
 (! (implies (HasKind @a2
Kind_type)
(HasType (ApplyET @x1
@a2)
Prims.pattern))
  
:pattern ((ApplyET @x1
@a2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_672)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 675
(Term_constr_id Prims.SMTPatT@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.SMTPatT@tok
Typ_fun_672))
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
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
Prims.pattern)
(or (is-Prims.SMTPat @x1)
(is-Prims.SMTPatT @x1)))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
Prims.pattern)))))

; </end encoding >

; encoding sigelt Prims.is_SMTPat

; <Start encoding Prims.is_SMTPat>
(declare-fun Prims.is_SMTPat (Term) Term)
;;;;;;;;;;;;;;;;(pattern -> Tot bool)
(declare-fun Typ_fun_677 () Type)
;;;;;;;;;;;;;;;;Typ_fun_677 kinding
(assert (HasKind Typ_fun_677
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_677)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_677)))))
;;;;;;;;;;;;;;;;Typ_fun_677 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_677)
(forall ((@x2 Term))
 (! (implies (HasType @x2
Prims.pattern)
(HasType (ApplyEE @x1
@x2)
Prims.bool))
  
:pattern ((ApplyEE @x1
@x2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_677)))))
(declare-fun Prims.is_SMTPat@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 680
(Term_constr_id Prims.is_SMTPat@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_SMTPat@tok
@x0)
(Prims.is_SMTPat @x0))
  
:pattern ((ApplyEE Prims.is_SMTPat@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_SMTPat@tok
Typ_fun_677))
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
(assert (= 682
(Term_constr_id Prims.is_SMTPatT@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_SMTPatT@tok
@x0)
(Prims.is_SMTPatT @x0))
  
:pattern ((ApplyEE Prims.is_SMTPatT@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_SMTPatT@tok
Typ_fun_677))
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

; encoding sigelt Prims.SMTPat.a

; <Start encoding Prims.SMTPat.a>
(declare-fun Prims.SMTPat.a (Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.SMTPat.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 686
(Type_constr_id Prims.SMTPat.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term))
 (! (= (ApplyTE Prims.SMTPat.a@tok
@x0)
(Prims.SMTPat.a @x0))
  
:pattern ((ApplyTE Prims.SMTPat.a@tok
@x0)))))
(declare-fun Typ_refine_683 () Type)
(assert (HasKind Typ_refine_683
Kind_type))
;;;;;;;;;;;;;;;;_0_149:pattern{(is_SMTPat _0_149)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_683)
(and (HasType @x1
Prims.pattern)
(Valid (Prims.b2t (Prims.is_SMTPat @x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_683)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.SMTPat.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_683)
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
;;;;;;;;;;;;;;;;(projectee:_0_149:pattern{(is_SMTPat _0_149)} -> Tot (a projectee))
(declare-fun Typ_fun_689 () Type)
;;;;;;;;;;;;;;;;Typ_fun_689 kinding
(assert (HasKind Typ_fun_689
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_689)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_689)))))
;;;;;;;;;;;;;;;;Typ_fun_689 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_689)
(forall ((@x2 Term))
 (! (implies (HasType @x2
Typ_refine_683)
(HasType (ApplyEE @x1
@x2)
(Prims.SMTPat.a @x2)))
  
:pattern ((ApplyEE @x1
@x2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_689)))))
(declare-fun Prims.SMTPat._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 692
(Term_constr_id Prims.SMTPat._1@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.SMTPat._1@tok
@x0)
(Prims.SMTPat._1 @x0))
  
:pattern ((ApplyEE Prims.SMTPat._1@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.SMTPat._1@tok
Typ_fun_689))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_683)
(HasType (Prims.SMTPat._1 @x0)
(Prims.SMTPat.a @x0)))
  
:pattern ((Prims.SMTPat._1 @x0)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPat._1 @x0)
(Prims.SMTPat__1 @x0))
  
:pattern ((Prims.SMTPat._1 @x0)))))
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_683)
(HasType (Prims.SMTPat__1 @x0)
(Prims.SMTPat.a @x0)))
  
:pattern ((HasType (Prims.SMTPat__1 @x0)
(Prims.SMTPat.a @x0))))))

; </end encoding Prims.SMTPat._1>

; encoding sigelt Prims.SMTPatT.a

; <Start encoding Prims.SMTPatT.a>
(declare-fun Prims.SMTPatT.a (Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.SMTPatT.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 696
(Type_constr_id Prims.SMTPatT.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@x0 Term))
 (! (= (ApplyTE Prims.SMTPatT.a@tok
@x0)
(Prims.SMTPatT.a @x0))
  
:pattern ((ApplyTE Prims.SMTPatT.a@tok
@x0)))))
(declare-fun Typ_refine_693 () Type)
(assert (HasKind Typ_refine_693
Kind_type))
;;;;;;;;;;;;;;;;_0_151:pattern{(is_SMTPatT _0_151)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_693)
(and (HasType @x1
Prims.pattern)
(Valid (Prims.b2t (Prims.is_SMTPatT @x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_693)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.SMTPatT.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@x0 Term))
 (! (implies (HasType @x0
Typ_refine_693)
(HasKind (Prims.SMTPatT.a @x0)
Kind_type))
  
:pattern ((Prims.SMTPatT.a @x0)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@x0 Term))
 (! (= (Prims.SMTPatT.a @x0)
(Prims.SMTPatT_a @x0))
  
:pattern ((Prims.SMTPatT.a @x0)))))

; </end encoding Prims.SMTPatT.a>

; encoding sigelt Prims.decreases

; <Start encoding Prims.decreases>
(declare-fun Prims.decreases (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.decreases@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 698
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
(declare-fun Typ_fun_726 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: None
(declare-fun Prims.None@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Some (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Some_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Some_v (Term) Term)
;;;;;;;;;;;;;;;;(v:a -> Tot (option a))
(declare-fun Typ_fun_733 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Some
(declare-fun Prims.Some@tok () Term)

; <Start encoding Prims.option>

; <start constructor Prims.option>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (= 717
(Type_constr_id (Prims.option @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.option@a0 (Prims.option @a0))
@a0)
  
:pattern ((Prims.option @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.option ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
717)
(= @a0
(Prims.option (Prims.option@a0 @a0)))))

; </end constructor Prims.option>
;;;;;;;;;;;;;;;;fresh token
(assert (= 718
(Type_constr_id Prims.option@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.option@tok
@a0)
(Prims.option @a0))
  
:pattern ((ApplyTT Prims.option@tok
@a0)))))
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
 (= 724
(Term_constr_id (Prims.None @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.None_a (Prims.None @a0))
@a0)
  
:pattern ((Prims.None @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.None ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
724)
(= @x0
(Prims.None (Prims.None_a @x0)))))

; </end constructor Prims.None>
;;;;;;;;;;;;;;;;Typ_fun_726 kinding
(assert (HasKind Typ_fun_726
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_726)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_726)))))
;;;;;;;;;;;;;;;;Typ_fun_726 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_726)
(forall ((@a2 Type))
 (! (implies (HasKind @a2
Kind_type)
(HasType (ApplyET @x1
@a2)
(Prims.option @a2)))
  
:pattern ((ApplyET @x1
@a2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_726)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 729
(Term_constr_id Prims.None@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.None@tok
Typ_fun_726))
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
 (= 731
(Term_constr_id (Prims.Some @a0
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
731)
(= @x0
(Prims.Some (Prims.Some_a @x0)
(Prims.Some_v @x0)))))

; </end constructor Prims.Some>
;;;;;;;;;;;;;;;;Typ_fun_733 kinding
(assert (HasKind Typ_fun_733
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_733)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_733)))))
;;;;;;;;;;;;;;;;Typ_fun_733 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_733)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
@a2))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
(Prims.option @a2)))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_733)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 736
(Term_constr_id Prims.Some@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Some@tok
Typ_fun_733))
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
(declare-fun Typ_fun_738 () Type)
;;;;;;;;;;;;;;;;Typ_fun_738 kinding
(assert (HasKind Typ_fun_738
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_738)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_738)))))
;;;;;;;;;;;;;;;;Typ_fun_738 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_738)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Prims.option @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_738)))))
(declare-fun Prims.is_None@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 741
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
Typ_fun_738))
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
(assert (= 743
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
Typ_fun_738))
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

; encoding sigelt Prims.None.a

; <Start encoding Prims.None.a>
(declare-fun Prims.None.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.None.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 747
(Type_constr_id Prims.None.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.None.a@tok
@a0)
@x1)
(Prims.None.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.None.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_744 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_744 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_744 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_161:(option a){(is_None _0_161)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_744 @a2))
(and (HasType @x1
(Prims.option @a2))
(Valid (Prims.b2t (Prims.is_None @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_744 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.None.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_744 @a0)))
(HasKind (Prims.None.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.None.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.None.a @a0
@x1)
(Prims.None_a @x1))
  
:pattern ((Prims.None.a @a0
@x1)))))

; </end encoding Prims.None.a>

; encoding sigelt Prims.Some.a

; <Start encoding Prims.Some.a>
(declare-fun Prims.Some.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Some.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 751
(Type_constr_id Prims.Some.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.Some.a@tok
@a0)
@x1)
(Prims.Some.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.Some.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_748 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_748 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_748 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_163:(option a){(is_Some _0_163)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_748 @a2))
(and (HasType @x1
(Prims.option @a2))
(Valid (Prims.b2t (Prims.is_Some @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_748 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Some.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_748 @a0)))
(HasKind (Prims.Some.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.Some.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Some.a @a0
@x1)
(Prims.Some_a @x1))
  
:pattern ((Prims.Some.a @a0
@x1)))))

; </end encoding Prims.Some.a>

; encoding sigelt Prims.Some.v

; <Start encoding Prims.Some.v>
(declare-fun Prims.Some.v (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_163:(option a){(is_Some _0_163)} -> Tot a)
(declare-fun Typ_fun_753 () Type)
;;;;;;;;;;;;;;;;Typ_fun_753 kinding
(assert (HasKind Typ_fun_753
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_753)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_753)))))
;;;;;;;;;;;;;;;;Typ_fun_753 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_753)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_748 @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_753)))))
(declare-fun Prims.Some.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 756
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
Typ_fun_753))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_748 @a0)))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_748 @a0)))
(HasType (Prims.Some_v @x1)
@a0))
  
:pattern ((HasType (Prims.Some_v @x1)
@a0)))))

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
(declare-fun Typ_fun_784 () Type)
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
(declare-fun Typ_fun_791 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Inr
(declare-fun Prims.Inr@tok () Term)

; <Start encoding Prims.either>

; <start constructor Prims.either>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (= 775
(Type_constr_id (Prims.either @a0
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
775)
(= @a0
(Prims.either (Prims.either@a0 @a0)
(Prims.either@a1 @a0)))))

; </end constructor Prims.either>
;;;;;;;;;;;;;;;;fresh token
(assert (= 776
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
 (= 782
(Term_constr_id (Prims.Inl @a0
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
782)
(= @x0
(Prims.Inl (Prims.Inl__a @x0)
(Prims.Inl__b @x0)
(Prims.Inl_v @x0)))))

; </end constructor Prims.Inl>
;;;;;;;;;;;;;;;;Typ_fun_784 kinding
(assert (HasKind Typ_fun_784
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_784)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_784)))))
;;;;;;;;;;;;;;;;Typ_fun_784 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_784)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
@a2))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
(Prims.either @a2
@a3)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_784)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 787
(Term_constr_id Prims.Inl@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Inl@tok
Typ_fun_784))
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
 (= 789
(Term_constr_id (Prims.Inr @a0
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
789)
(= @x0
(Prims.Inr (Prims.Inr__a @x0)
(Prims.Inr__b @x0)
(Prims.Inr_v @x0)))))

; </end constructor Prims.Inr>
;;;;;;;;;;;;;;;;Typ_fun_791 kinding
(assert (HasKind Typ_fun_791
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_791)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_791)))))
;;;;;;;;;;;;;;;;Typ_fun_791 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_791)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
@a3))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
(Prims.either @a2
@a3)))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_791)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 794
(Term_constr_id Prims.Inr@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Inr@tok
Typ_fun_791))
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
(declare-fun Typ_fun_796 () Type)
;;;;;;;;;;;;;;;;Typ_fun_796 kinding
(assert (HasKind Typ_fun_796
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_796)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_796)))))
;;;;;;;;;;;;;;;;Typ_fun_796 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_796)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.either @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_796)))))
(declare-fun Prims.is_Inl@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 799
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
Typ_fun_796))
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
(assert (= 801
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
Typ_fun_796))
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

; encoding sigelt Prims.Inl.'a

; <Start encoding Prims.Inl.'a>
(declare-fun Prims.Inl._a (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Inl._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 805
(Type_constr_id Prims.Inl._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Inl._a@tok
@a0)
@a1)
@x2)
(Prims.Inl._a @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Inl._a@tok
@a0)
@a1)
@x2)))))
(declare-fun Typ_refine_802 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_802 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_802 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_169:(either 'a 'b){(is_Inl _0_169)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_refine_802 @a2
@a3))
(and (HasType @x1
(Prims.either @a3
@a2))
(Valid (Prims.b2t (Prims.is_Inl @a3
@a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_802 @a2
@a3))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Inl._a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_802 @a1
@a0)))
(HasKind (Prims.Inl._a @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Inl._a @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inl._a @a0
@a1
@x2)
(Prims.Inl__a @x2))
  
:pattern ((Prims.Inl._a @a0
@a1
@x2)))))

; </end encoding Prims.Inl.'a>

; encoding sigelt Prims.Inl.'b

; <Start encoding Prims.Inl.'b>
(declare-fun Prims.Inl._b (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Inl._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 807
(Type_constr_id Prims.Inl._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Inl._b@tok
@a0)
@a1)
@x2)
(Prims.Inl._b @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Inl._b@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Inl._b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_802 @a1
@a0)))
(HasKind (Prims.Inl._b @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Inl._b @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inl._b @a0
@a1
@x2)
(Prims.Inl__b @x2))
  
:pattern ((Prims.Inl._b @a0
@a1
@x2)))))

; </end encoding Prims.Inl.'b>

; encoding sigelt Prims.Inl.v

; <Start encoding Prims.Inl.v>
(declare-fun Prims.Inl.v (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_169:(either 'a 'b){(is_Inl _0_169)} -> Tot 'a)
(declare-fun Typ_fun_809 () Type)
;;;;;;;;;;;;;;;;Typ_fun_809 kinding
(assert (HasKind Typ_fun_809
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_809)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_809)))))
;;;;;;;;;;;;;;;;Typ_fun_809 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_809)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Typ_refine_802 @a3
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_809)))))
(declare-fun Prims.Inl.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 812
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
Typ_fun_809))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_802 @a1
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_802 @a1
@a0)))
(HasType (Prims.Inl_v @x2)
@a0))))

; </end encoding Prims.Inl.v>

; encoding sigelt Prims.Inr.'a

; <Start encoding Prims.Inr.'a>
(declare-fun Prims.Inr._a (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Inr._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 816
(Type_constr_id Prims.Inr._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Inr._a@tok
@a0)
@a1)
@x2)
(Prims.Inr._a @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Inr._a@tok
@a0)
@a1)
@x2)))))
(declare-fun Typ_refine_813 (Type Type) Type)
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_refine_813 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_813 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_171:(either 'a 'b){(is_Inr _0_171)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_refine_813 @a2
@a3))
(and (HasType @x1
(Prims.either @a3
@a2))
(Valid (Prims.b2t (Prims.is_Inr @a3
@a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_813 @a2
@a3))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Inr._a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_813 @a1
@a0)))
(HasKind (Prims.Inr._a @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Inr._a @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inr._a @a0
@a1
@x2)
(Prims.Inr__a @x2))
  
:pattern ((Prims.Inr._a @a0
@a1
@x2)))))

; </end encoding Prims.Inr.'a>

; encoding sigelt Prims.Inr.'b

; <Start encoding Prims.Inr.'b>
(declare-fun Prims.Inr._b (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Inr._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 818
(Type_constr_id Prims.Inr._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.Inr._b@tok
@a0)
@a1)
@x2)
(Prims.Inr._b @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.Inr._b@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Inr._b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_813 @a1
@a0)))
(HasKind (Prims.Inr._b @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.Inr._b @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.Inr._b @a0
@a1
@x2)
(Prims.Inr__b @x2))
  
:pattern ((Prims.Inr._b @a0
@a1
@x2)))))

; </end encoding Prims.Inr.'b>

; encoding sigelt Prims.Inr.v

; <Start encoding Prims.Inr.v>
(declare-fun Prims.Inr.v (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_171:(either 'a 'b){(is_Inr _0_171)} -> Tot 'b)
(declare-fun Typ_fun_820 () Type)
;;;;;;;;;;;;;;;;Typ_fun_820 kinding
(assert (HasKind Typ_fun_820
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_820)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_820)))))
;;;;;;;;;;;;;;;;Typ_fun_820 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_820)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Typ_refine_813 @a3
@a2)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_820)))))
(declare-fun Prims.Inr.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 823
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
Typ_fun_820))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_813 @a1
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Typ_refine_813 @a1
@a0)))
(HasType (Prims.Inr_v @x2)
@a1))))

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
(declare-fun Typ_fun_858 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: V
(declare-fun Prims.V@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.E (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.E_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.E_e (Term) Term)
;;;;;;;;;;;;;;;;(e:exn -> Tot (result a))
(declare-fun Typ_fun_865 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: E
(declare-fun Prims.E@tok () Term)
;;;;;;;;;;;;;;;;Constructor
(declare-fun Prims.Err (Type Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Err_a (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun Prims.Err_msg (Term) Term)
;;;;;;;;;;;;;;;;(msg:string -> Tot (result a))
(declare-fun Typ_fun_872 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Err
(declare-fun Prims.Err@tok () Term)

; <Start encoding Prims.result>

; <start constructor Prims.result>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type))
 (= 849
(Type_constr_id (Prims.result @a0)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type))
 (! (= (Prims.result@a0 (Prims.result @a0))
@a0)
  
:pattern ((Prims.result @a0)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.result ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
849)
(= @a0
(Prims.result (Prims.result@a0 @a0)))))

; </end constructor Prims.result>
;;;;;;;;;;;;;;;;fresh token
(assert (= 850
(Type_constr_id Prims.result@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT Prims.result@tok
@a0)
(Prims.result @a0))
  
:pattern ((ApplyTT Prims.result@tok
@a0)))))
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
 (= 856
(Term_constr_id (Prims.V @a0
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
856)
(= @x0
(Prims.V (Prims.V_a @x0)
(Prims.V_v @x0)))))

; </end constructor Prims.V>
;;;;;;;;;;;;;;;;Typ_fun_858 kinding
(assert (HasKind Typ_fun_858
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_858)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_858)))))
;;;;;;;;;;;;;;;;Typ_fun_858 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_858)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
@a2))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
(Prims.result @a2)))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_858)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 861
(Term_constr_id Prims.V@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.V@tok
Typ_fun_858))
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
 (= 863
(Term_constr_id (Prims.E @a0
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
863)
(= @x0
(Prims.E (Prims.E_a @x0)
(Prims.E_e @x0)))))

; </end constructor Prims.E>
;;;;;;;;;;;;;;;;Typ_fun_865 kinding
(assert (HasKind Typ_fun_865
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_865)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_865)))))
;;;;;;;;;;;;;;;;Typ_fun_865 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_865)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
Prims.exn))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
(Prims.result @a2)))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_865)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 868
(Term_constr_id Prims.E@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.E@tok
Typ_fun_865))
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
 (= 870
(Term_constr_id (Prims.Err @a0
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
870)
(= @x0
(Prims.Err (Prims.Err_a @x0)
(Prims.Err_msg @x0)))))

; </end constructor Prims.Err>
;;;;;;;;;;;;;;;;Typ_fun_872 kinding
(assert (HasKind Typ_fun_872
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_872)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_872)))))
;;;;;;;;;;;;;;;;Typ_fun_872 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_872)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
Prims.string))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
(Prims.result @a2)))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_872)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 875
(Term_constr_id Prims.Err@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.Err@tok
Typ_fun_872))
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
(declare-fun Typ_fun_877 () Type)
;;;;;;;;;;;;;;;;Typ_fun_877 kinding
(assert (HasKind Typ_fun_877
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_877)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_877)))))
;;;;;;;;;;;;;;;;Typ_fun_877 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_877)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Prims.result @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_877)))))
(declare-fun Prims.is_V@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 880
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
Typ_fun_877))
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
(assert (= 882
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
Typ_fun_877))
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
(assert (= 884
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
Typ_fun_877))
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

; encoding sigelt Prims.V.a

; <Start encoding Prims.V.a>
(declare-fun Prims.V.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.V.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 888
(Type_constr_id Prims.V.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.V.a@tok
@a0)
@x1)
(Prims.V.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.V.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_885 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_885 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_885 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_177:(result a){(is_V _0_177)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_885 @a2))
(and (HasType @x1
(Prims.result @a2))
(Valid (Prims.b2t (Prims.is_V @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_885 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.V.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_885 @a0)))
(HasKind (Prims.V.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.V.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.V.a @a0
@x1)
(Prims.V_a @x1))
  
:pattern ((Prims.V.a @a0
@x1)))))

; </end encoding Prims.V.a>

; encoding sigelt Prims.V.v

; <Start encoding Prims.V.v>
(declare-fun Prims.V.v (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_177:(result a){(is_V _0_177)} -> Tot a)
(declare-fun Typ_fun_890 () Type)
;;;;;;;;;;;;;;;;Typ_fun_890 kinding
(assert (HasKind Typ_fun_890
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_890)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_890)))))
;;;;;;;;;;;;;;;;Typ_fun_890 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_890)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_885 @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_890)))))
(declare-fun Prims.V.v@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 893
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
Typ_fun_890))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_885 @a0)))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_885 @a0)))
(HasType (Prims.V_v @x1)
@a0))
  
:pattern ((HasType (Prims.V_v @x1)
@a0)))))

; </end encoding Prims.V.v>

; encoding sigelt Prims.E.a

; <Start encoding Prims.E.a>
(declare-fun Prims.E.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.E.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 897
(Type_constr_id Prims.E.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.E.a@tok
@a0)
@x1)
(Prims.E.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.E.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_894 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_894 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_894 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_179:(result a){(is_E _0_179)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_894 @a2))
(and (HasType @x1
(Prims.result @a2))
(Valid (Prims.b2t (Prims.is_E @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_894 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.E.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_894 @a0)))
(HasKind (Prims.E.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.E.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.E.a @a0
@x1)
(Prims.E_a @x1))
  
:pattern ((Prims.E.a @a0
@x1)))))

; </end encoding Prims.E.a>

; encoding sigelt Prims.E.e

; <Start encoding Prims.E.e>
(declare-fun Prims.E.e (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_179:(result a){(is_E _0_179)} -> Tot exn)
(declare-fun Typ_fun_899 () Type)
;;;;;;;;;;;;;;;;Typ_fun_899 kinding
(assert (HasKind Typ_fun_899
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_899)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_899)))))
;;;;;;;;;;;;;;;;Typ_fun_899 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_899)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_894 @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.exn))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_899)))))
(declare-fun Prims.E.e@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 902
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
Typ_fun_899))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_894 @a0)))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@x1 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_894 @a0)))
(HasType (Prims.E_e @x1)
Prims.exn))))

; </end encoding Prims.E.e>

; encoding sigelt Prims.Err.a

; <Start encoding Prims.Err.a>
(declare-fun Prims.Err.a (Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.Err.a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 906
(Type_constr_id Prims.Err.a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT Prims.Err.a@tok
@a0)
@x1)
(Prims.Err.a @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT Prims.Err.a@tok
@a0)
@x1)))))
(declare-fun Typ_refine_903 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_903 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_903 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;_0_181:(result a){(is_Err _0_181)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_903 @a2))
(and (HasType @x1
(Prims.result @a2))
(Valid (Prims.b2t (Prims.is_Err @a2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_903 @a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.Err.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_903 @a0)))
(HasKind (Prims.Err.a @a0
@x1)
Kind_type))
  
:pattern ((Prims.Err.a @a0
@x1)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (Prims.Err.a @a0
@x1)
(Prims.Err_a @x1))
  
:pattern ((Prims.Err.a @a0
@x1)))))

; </end encoding Prims.Err.a>

; encoding sigelt Prims.Err.msg

; <Start encoding Prims.Err.msg>
(declare-fun Prims.Err.msg (Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:_0_181:(result a){(is_Err _0_181)} -> Tot string)
(declare-fun Typ_fun_908 () Type)
;;;;;;;;;;;;;;;;Typ_fun_908 kinding
(assert (HasKind Typ_fun_908
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_908)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_908)))))
;;;;;;;;;;;;;;;;Typ_fun_908 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_908)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(Typ_refine_903 @a2)))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.string))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_908)))))
(declare-fun Prims.Err.msg@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 911
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
Typ_fun_908))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_903 @a0)))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@x1 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_refine_903 @a0)))
(HasType (Prims.Err_msg @x1)
Prims.string))))

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
(assert (= 1606
(Type_constr_id Prims.lex_t)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.lex_t ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
1606)
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
(assert (= 1612
(Term_constr_id Prims.LexTop)))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-Prims.LexTop ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
1612)
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
(declare-fun Typ_fun_1615 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1615 kinding
(assert (HasKind Typ_fun_1615
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1615)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1615)))))
;;;;;;;;;;;;;;;;Typ_fun_1615 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1615)
(forall ((@x2 Term))
 (! (implies (HasType @x2
Prims.lex_t)
(HasType (ApplyEE @x1
@x2)
Prims.bool))
  
:pattern ((ApplyEE @x1
@x2)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1615)))))
(declare-fun Prims.is_LexTop@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1618
(Term_constr_id Prims.is_LexTop@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_LexTop@tok
@x0)
(Prims.is_LexTop @x0))
  
:pattern ((ApplyEE Prims.is_LexTop@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_LexTop@tok
Typ_fun_1615))
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
(assert (= 1620
(Term_constr_id Prims.is_LexCons@tok)))
(assert (forall ((@x0 Term))
 (! (= (ApplyEE Prims.is_LexCons@tok
@x0)
(Prims.is_LexCons @x0))
  
:pattern ((ApplyEE Prims.is_LexCons@tok
@x0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.is_LexCons@tok
Typ_fun_1615))
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
(declare-fun Typ_fun_1641 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple2
(declare-fun Prims.MkTuple2@tok () Term)

; <Start encoding Prims.Tuple2>

; <start constructor Prims.Tuple2>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type))
 (= 1632
(Type_constr_id (Prims.Tuple2 @a0
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
1632)
(= @a0
(Prims.Tuple2 (Prims.Tuple2@a0 @a0)
(Prims.Tuple2@a1 @a0)))))

; </end constructor Prims.Tuple2>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1633
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
 (= 1639
(Term_constr_id (Prims.MkTuple2 @a0
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
1639)
(= @x0
(Prims.MkTuple2 (Prims.MkTuple2__a @x0)
(Prims.MkTuple2__b @x0)
(Prims.MkTuple2__1 @x0)
(Prims.MkTuple2__2 @x0)))))

; </end constructor Prims.MkTuple2>
;;;;;;;;;;;;;;;;Typ_fun_1641 kinding
(assert (HasKind Typ_fun_1641
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1641)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1641)))))
;;;;;;;;;;;;;;;;Typ_fun_1641 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1641)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
@a2)
(HasType @x5
@a3))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
(Prims.Tuple2 @a2
@a3)))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1641)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1644
(Term_constr_id Prims.MkTuple2@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple2@tok
Typ_fun_1641))
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
(declare-fun Typ_fun_1646 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1646 kinding
(assert (HasKind Typ_fun_1646
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1646)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1646)))))
;;;;;;;;;;;;;;;;Typ_fun_1646 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1646)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1646)))))
(declare-fun Prims.is_MkTuple2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1649
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
Typ_fun_1646))
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

; encoding sigelt Prims.MkTuple2.'a

; <Start encoding Prims.MkTuple2.'a>
(declare-fun Prims.MkTuple2._a (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple2._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1651
(Type_constr_id Prims.MkTuple2._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.MkTuple2._a@tok
@a0)
@a1)
@x2)
(Prims.MkTuple2._a @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.MkTuple2._a@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple2._a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasKind (Prims.MkTuple2._a @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.MkTuple2._a @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkTuple2._a @a0
@a1
@x2)
(Prims.MkTuple2__a @x2))
  
:pattern ((Prims.MkTuple2._a @a0
@a1
@x2)))))

; </end encoding Prims.MkTuple2.'a>

; encoding sigelt Prims.MkTuple2.'b

; <Start encoding Prims.MkTuple2.'b>
(declare-fun Prims.MkTuple2._b (Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple2._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1653
(Type_constr_id Prims.MkTuple2._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT Prims.MkTuple2._b@tok
@a0)
@a1)
@x2)
(Prims.MkTuple2._b @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT Prims.MkTuple2._b@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple2._b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasKind (Prims.MkTuple2._b @a0
@a1
@x2)
Kind_type))
  
:pattern ((Prims.MkTuple2._b @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (Prims.MkTuple2._b @a0
@a1
@x2)
(Prims.MkTuple2__b @x2))
  
:pattern ((Prims.MkTuple2._b @a0
@a1
@x2)))))

; </end encoding Prims.MkTuple2.'b>

; encoding sigelt Prims.MkTuple2._1

; <Start encoding Prims.MkTuple2._1>
(declare-fun Prims.MkTuple2._1 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple2 'a 'b) -> Tot 'a)
(declare-fun Typ_fun_1655 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1655 kinding
(assert (HasKind Typ_fun_1655
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1655)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1655)))))
;;;;;;;;;;;;;;;;Typ_fun_1655 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1655)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1655)))))
(declare-fun Prims.MkTuple2._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1658
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
Typ_fun_1655))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.MkTuple2__1 @x2)
@a0))))

; </end encoding Prims.MkTuple2._1>

; encoding sigelt Prims.MkTuple2._2

; <Start encoding Prims.MkTuple2._2>
(declare-fun Prims.MkTuple2._2 (Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple2 'a 'b) -> Tot 'b)
(declare-fun Typ_fun_1660 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1660 kinding
(assert (HasKind Typ_fun_1660
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1660)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1660)))))
;;;;;;;;;;;;;;;;Typ_fun_1660 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1660)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(Prims.Tuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1660)))))
(declare-fun Prims.MkTuple2._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1663
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
Typ_fun_1660))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(Prims.Tuple2 @a0
@a1)))
(HasType (Prims.MkTuple2__2 @x2)
@a1))))

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
(declare-fun Typ_fun_1684 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple3
(declare-fun Prims.MkTuple3@tok () Term)

; <Start encoding Prims.Tuple3>

; <start constructor Prims.Tuple3>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (= 1675
(Type_constr_id (Prims.Tuple3 @a0
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
1675)
(= @a0
(Prims.Tuple3 (Prims.Tuple3@a0 @a0)
(Prims.Tuple3@a1 @a0)
(Prims.Tuple3@a2 @a0)))))

; </end constructor Prims.Tuple3>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1676
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
 (= 1682
(Term_constr_id (Prims.MkTuple3 @a0
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
1682)
(= @x0
(Prims.MkTuple3 (Prims.MkTuple3__a @x0)
(Prims.MkTuple3__b @x0)
(Prims.MkTuple3__c @x0)
(Prims.MkTuple3__1 @x0)
(Prims.MkTuple3__2 @x0)
(Prims.MkTuple3__3 @x0)))))

; </end constructor Prims.MkTuple3>
;;;;;;;;;;;;;;;;Typ_fun_1684 kinding
(assert (HasKind Typ_fun_1684
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1684)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1684)))))
;;;;;;;;;;;;;;;;Typ_fun_1684 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1684)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
@a2)
(HasType @x6
@a3)
(HasType @x7
@a4))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
(Prims.Tuple3 @a2
@a3
@a4)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1684)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1687
(Term_constr_id Prims.MkTuple3@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple3@tok
Typ_fun_1684))
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
(declare-fun Typ_fun_1689 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1689 kinding
(assert (HasKind Typ_fun_1689
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1689)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1689)))))
;;;;;;;;;;;;;;;;Typ_fun_1689 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1689)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1689)))))
(declare-fun Prims.is_MkTuple3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1692
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
Typ_fun_1689))
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

; encoding sigelt Prims.MkTuple3.'a

; <Start encoding Prims.MkTuple3.'a>
(declare-fun Prims.MkTuple3._a (Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple3._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1694
(Type_constr_id Prims.MkTuple3._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple3._a@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkTuple3._a @a0
@a1
@a2
@x3))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple3._a@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple3._a@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple3._a @a0
@a1
@a2
@x3)
Kind_type))
  
:pattern ((Prims.MkTuple3._a @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkTuple3._a @a0
@a1
@a2
@x3)
(Prims.MkTuple3__a @x3))
  
:pattern ((Prims.MkTuple3._a @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkTuple3.'a>

; encoding sigelt Prims.MkTuple3.'b

; <Start encoding Prims.MkTuple3.'b>
(declare-fun Prims.MkTuple3._b (Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple3._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1696
(Type_constr_id Prims.MkTuple3._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple3._b@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkTuple3._b @a0
@a1
@a2
@x3))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple3._b@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple3._b@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple3._b @a0
@a1
@a2
@x3)
Kind_type))
  
:pattern ((Prims.MkTuple3._b @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkTuple3._b @a0
@a1
@a2
@x3)
(Prims.MkTuple3__b @x3))
  
:pattern ((Prims.MkTuple3._b @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkTuple3.'b>

; encoding sigelt Prims.MkTuple3.'c

; <Start encoding Prims.MkTuple3.'c>
(declare-fun Prims.MkTuple3._c (Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple3._c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1698
(Type_constr_id Prims.MkTuple3._c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple3._c@tok
@a0)
@a1)
@a2)
@x3)
(Prims.MkTuple3._c @a0
@a1
@a2
@x3))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple3._c@tok
@a0)
@a1)
@a2)
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple3._c@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple3._c @a0
@a1
@a2
@x3)
Kind_type))
  
:pattern ((Prims.MkTuple3._c @a0
@a1
@a2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (= (Prims.MkTuple3._c @a0
@a1
@a2
@x3)
(Prims.MkTuple3__c @x3))
  
:pattern ((Prims.MkTuple3._c @a0
@a1
@a2
@x3)))))

; </end encoding Prims.MkTuple3.'c>

; encoding sigelt Prims.MkTuple3._1

; <Start encoding Prims.MkTuple3._1>
(declare-fun Prims.MkTuple3._1 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple3 'a 'b 'c) -> Tot 'a)
(declare-fun Typ_fun_1700 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1700 kinding
(assert (HasKind Typ_fun_1700
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1700)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1700)))))
;;;;;;;;;;;;;;;;Typ_fun_1700 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1700)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1700)))))
(declare-fun Prims.MkTuple3._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1703
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
Typ_fun_1700))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.MkTuple3__1 @x3)
@a0))))

; </end encoding Prims.MkTuple3._1>

; encoding sigelt Prims.MkTuple3._2

; <Start encoding Prims.MkTuple3._2>
(declare-fun Prims.MkTuple3._2 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple3 'a 'b 'c) -> Tot 'b)
(declare-fun Typ_fun_1705 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1705 kinding
(assert (HasKind Typ_fun_1705
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1705)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1705)))))
;;;;;;;;;;;;;;;;Typ_fun_1705 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1705)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1705)))))
(declare-fun Prims.MkTuple3._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1708
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
Typ_fun_1705))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.MkTuple3__2 @x3)
@a1))))

; </end encoding Prims.MkTuple3._2>

; encoding sigelt Prims.MkTuple3._3

; <Start encoding Prims.MkTuple3._3>
(declare-fun Prims.MkTuple3._3 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple3 'a 'b 'c) -> Tot 'c)
(declare-fun Typ_fun_1710 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1710 kinding
(assert (HasKind Typ_fun_1710
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1710)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1710)))))
;;;;;;;;;;;;;;;;Typ_fun_1710 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1710)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasType @x5
(Prims.Tuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1710)))))
(declare-fun Prims.MkTuple3._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1713
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
Typ_fun_1710))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasType @x3
(Prims.Tuple3 @a0
@a1
@a2)))
(HasType (Prims.MkTuple3__3 @x3)
@a2))))

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
(declare-fun Typ_fun_1734 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple4
(declare-fun Prims.MkTuple4@tok () Term)

; <Start encoding Prims.Tuple4>

; <start constructor Prims.Tuple4>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (= 1725
(Type_constr_id (Prims.Tuple4 @a0
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
1725)
(= @a0
(Prims.Tuple4 (Prims.Tuple4@a0 @a0)
(Prims.Tuple4@a1 @a0)
(Prims.Tuple4@a2 @a0)
(Prims.Tuple4@a3 @a0)))))

; </end constructor Prims.Tuple4>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1726
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
 (= 1732
(Term_constr_id (Prims.MkTuple4 @a0
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
1732)
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
;;;;;;;;;;;;;;;;Typ_fun_1734 kinding
(assert (HasKind Typ_fun_1734
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1734)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1734)))))
;;;;;;;;;;;;;;;;Typ_fun_1734 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1734)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
@a2)
(HasType @x7
@a3)
(HasType @x8
@a4)
(HasType @x9
@a5))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)
(Prims.Tuple4 @a2
@a3
@a4
@a5)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1734)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1737
(Term_constr_id Prims.MkTuple4@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple4@tok
Typ_fun_1734))
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
(declare-fun Typ_fun_1739 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1739 kinding
(assert (HasKind Typ_fun_1739
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1739)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1739)))))
;;;;;;;;;;;;;;;;Typ_fun_1739 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1739)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1739)))))
(declare-fun Prims.is_MkTuple4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1742
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
Typ_fun_1739))
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

; encoding sigelt Prims.MkTuple4.'a

; <Start encoding Prims.MkTuple4.'a>
(declare-fun Prims.MkTuple4._a (Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple4._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1744
(Type_constr_id Prims.MkTuple4._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._a@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._a @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._a@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple4._a@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple4._a @a0
@a1
@a2
@a3
@x4)
Kind_type))
  
:pattern ((Prims.MkTuple4._a @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._a @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__a @x4))
  
:pattern ((Prims.MkTuple4._a @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4.'a>

; encoding sigelt Prims.MkTuple4.'b

; <Start encoding Prims.MkTuple4.'b>
(declare-fun Prims.MkTuple4._b (Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple4._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1746
(Type_constr_id Prims.MkTuple4._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._b@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._b @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._b@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple4._b@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple4._b @a0
@a1
@a2
@a3
@x4)
Kind_type))
  
:pattern ((Prims.MkTuple4._b @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._b @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__b @x4))
  
:pattern ((Prims.MkTuple4._b @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4.'b>

; encoding sigelt Prims.MkTuple4.'c

; <Start encoding Prims.MkTuple4.'c>
(declare-fun Prims.MkTuple4._c (Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple4._c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1748
(Type_constr_id Prims.MkTuple4._c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._c@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._c @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._c@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple4._c@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple4._c @a0
@a1
@a2
@a3
@x4)
Kind_type))
  
:pattern ((Prims.MkTuple4._c @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._c @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__c @x4))
  
:pattern ((Prims.MkTuple4._c @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4.'c>

; encoding sigelt Prims.MkTuple4.'d

; <Start encoding Prims.MkTuple4.'d>
(declare-fun Prims.MkTuple4._d (Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple4._d@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1750
(Type_constr_id Prims.MkTuple4._d@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._d@tok
@a0)
@a1)
@a2)
@a3)
@x4)
(Prims.MkTuple4._d @a0
@a1
@a2
@a3
@x4))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple4._d@tok
@a0)
@a1)
@a2)
@a3)
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple4._d@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple4._d @a0
@a1
@a2
@a3
@x4)
Kind_type))
  
:pattern ((Prims.MkTuple4._d @a0
@a1
@a2
@a3
@x4)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (= (Prims.MkTuple4._d @a0
@a1
@a2
@a3
@x4)
(Prims.MkTuple4__d @x4))
  
:pattern ((Prims.MkTuple4._d @a0
@a1
@a2
@a3
@x4)))))

; </end encoding Prims.MkTuple4.'d>

; encoding sigelt Prims.MkTuple4._1

; <Start encoding Prims.MkTuple4._1>
(declare-fun Prims.MkTuple4._1 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'a)
(declare-fun Typ_fun_1752 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1752 kinding
(assert (HasKind Typ_fun_1752
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1752)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1752)))))
;;;;;;;;;;;;;;;;Typ_fun_1752 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1752)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1752)))))
(declare-fun Prims.MkTuple4._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1755
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
Typ_fun_1752))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple4__1 @x4)
@a0))))

; </end encoding Prims.MkTuple4._1>

; encoding sigelt Prims.MkTuple4._2

; <Start encoding Prims.MkTuple4._2>
(declare-fun Prims.MkTuple4._2 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'b)
(declare-fun Typ_fun_1757 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1757 kinding
(assert (HasKind Typ_fun_1757
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1757)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1757)))))
;;;;;;;;;;;;;;;;Typ_fun_1757 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1757)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1757)))))
(declare-fun Prims.MkTuple4._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1760
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
Typ_fun_1757))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple4__2 @x4)
@a1))))

; </end encoding Prims.MkTuple4._2>

; encoding sigelt Prims.MkTuple4._3

; <Start encoding Prims.MkTuple4._3>
(declare-fun Prims.MkTuple4._3 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'c)
(declare-fun Typ_fun_1762 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1762 kinding
(assert (HasKind Typ_fun_1762
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1762)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1762)))))
;;;;;;;;;;;;;;;;Typ_fun_1762 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1762)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1762)))))
(declare-fun Prims.MkTuple4._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1765
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
Typ_fun_1762))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple4__3 @x4)
@a2))))

; </end encoding Prims.MkTuple4._3>

; encoding sigelt Prims.MkTuple4._4

; <Start encoding Prims.MkTuple4._4>
(declare-fun Prims.MkTuple4._4 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple4 'a 'b 'c 'd) -> Tot 'd)
(declare-fun Typ_fun_1767 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1767 kinding
(assert (HasKind Typ_fun_1767
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1767)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1767)))))
;;;;;;;;;;;;;;;;Typ_fun_1767 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1767)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasKind @a4
Kind_type)
(HasKind @a5
Kind_type)
(HasType @x6
(Prims.Tuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1767)))))
(declare-fun Prims.MkTuple4._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1770
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
Typ_fun_1767))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple4__4 @x4)
@a3))))

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
(declare-fun Typ_fun_1791 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple5
(declare-fun Prims.MkTuple5@tok () Term)

; <Start encoding Prims.Tuple5>

; <start constructor Prims.Tuple5>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type))
 (= 1782
(Type_constr_id (Prims.Tuple5 @a0
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
1782)
(= @a0
(Prims.Tuple5 (Prims.Tuple5@a0 @a0)
(Prims.Tuple5@a1 @a0)
(Prims.Tuple5@a2 @a0)
(Prims.Tuple5@a3 @a0)
(Prims.Tuple5@a4 @a0)))))

; </end constructor Prims.Tuple5>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1783
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
 (= 1789
(Term_constr_id (Prims.MkTuple5 @a0
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
1789)
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
;;;;;;;;;;;;;;;;Typ_fun_1791 kinding
(assert (HasKind Typ_fun_1791
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1791)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1791)))))
;;;;;;;;;;;;;;;;Typ_fun_1791 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1791)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term))
 (! (implies (and (HasKind @a2
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
@a2)
(HasType @x8
@a3)
(HasType @x9
@a4)
(HasType @x10
@a5)
(HasType @x11
@a6))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@x8)
@x9)
@x10)
@x11)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1791)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1794
(Term_constr_id Prims.MkTuple5@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple5@tok
Typ_fun_1791))
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
(declare-fun Typ_fun_1796 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1796 kinding
(assert (HasKind Typ_fun_1796
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1796)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1796)))))
;;;;;;;;;;;;;;;;Typ_fun_1796 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1796)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1796)))))
(declare-fun Prims.is_MkTuple5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1799
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
Typ_fun_1796))
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

; encoding sigelt Prims.MkTuple5.'a

; <Start encoding Prims.MkTuple5.'a>
(declare-fun Prims.MkTuple5._a (Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple5._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1801
(Type_constr_id Prims.MkTuple5._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._a @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple5._a@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple5._a @a0
@a1
@a2
@a3
@a4
@x5)
Kind_type))
  
:pattern ((Prims.MkTuple5._a @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._a @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__a @x5))
  
:pattern ((Prims.MkTuple5._a @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5.'a>

; encoding sigelt Prims.MkTuple5.'b

; <Start encoding Prims.MkTuple5.'b>
(declare-fun Prims.MkTuple5._b (Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple5._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1803
(Type_constr_id Prims.MkTuple5._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._b @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple5._b@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple5._b @a0
@a1
@a2
@a3
@a4
@x5)
Kind_type))
  
:pattern ((Prims.MkTuple5._b @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._b @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__b @x5))
  
:pattern ((Prims.MkTuple5._b @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5.'b>

; encoding sigelt Prims.MkTuple5.'c

; <Start encoding Prims.MkTuple5.'c>
(declare-fun Prims.MkTuple5._c (Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple5._c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1805
(Type_constr_id Prims.MkTuple5._c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._c @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple5._c@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple5._c @a0
@a1
@a2
@a3
@a4
@x5)
Kind_type))
  
:pattern ((Prims.MkTuple5._c @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._c @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__c @x5))
  
:pattern ((Prims.MkTuple5._c @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5.'c>

; encoding sigelt Prims.MkTuple5.'d

; <Start encoding Prims.MkTuple5.'d>
(declare-fun Prims.MkTuple5._d (Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple5._d@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1807
(Type_constr_id Prims.MkTuple5._d@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._d @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple5._d@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple5._d @a0
@a1
@a2
@a3
@a4
@x5)
Kind_type))
  
:pattern ((Prims.MkTuple5._d @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._d @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__d @x5))
  
:pattern ((Prims.MkTuple5._d @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5.'d>

; encoding sigelt Prims.MkTuple5.'e

; <Start encoding Prims.MkTuple5.'e>
(declare-fun Prims.MkTuple5._e (Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple5._e@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1809
(Type_constr_id Prims.MkTuple5._e@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)
(Prims.MkTuple5._e @a0
@a1
@a2
@a3
@a4
@x5))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple5._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple5._e@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple5._e @a0
@a1
@a2
@a3
@a4
@x5)
Kind_type))
  
:pattern ((Prims.MkTuple5._e @a0
@a1
@a2
@a3
@a4
@x5)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (= (Prims.MkTuple5._e @a0
@a1
@a2
@a3
@a4
@x5)
(Prims.MkTuple5__e @x5))
  
:pattern ((Prims.MkTuple5._e @a0
@a1
@a2
@a3
@a4
@x5)))))

; </end encoding Prims.MkTuple5.'e>

; encoding sigelt Prims.MkTuple5._1

; <Start encoding Prims.MkTuple5._1>
(declare-fun Prims.MkTuple5._1 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'a)
(declare-fun Typ_fun_1811 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1811 kinding
(assert (HasKind Typ_fun_1811
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1811)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1811)))))
;;;;;;;;;;;;;;;;Typ_fun_1811 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1811)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1811)))))
(declare-fun Prims.MkTuple5._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1814
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
Typ_fun_1811))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple5__1 @x5)
@a0))))

; </end encoding Prims.MkTuple5._1>

; encoding sigelt Prims.MkTuple5._2

; <Start encoding Prims.MkTuple5._2>
(declare-fun Prims.MkTuple5._2 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'b)
(declare-fun Typ_fun_1816 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1816 kinding
(assert (HasKind Typ_fun_1816
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1816)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1816)))))
;;;;;;;;;;;;;;;;Typ_fun_1816 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1816)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1816)))))
(declare-fun Prims.MkTuple5._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1819
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
Typ_fun_1816))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple5__2 @x5)
@a1))))

; </end encoding Prims.MkTuple5._2>

; encoding sigelt Prims.MkTuple5._3

; <Start encoding Prims.MkTuple5._3>
(declare-fun Prims.MkTuple5._3 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'c)
(declare-fun Typ_fun_1821 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1821 kinding
(assert (HasKind Typ_fun_1821
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1821)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1821)))))
;;;;;;;;;;;;;;;;Typ_fun_1821 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1821)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1821)))))
(declare-fun Prims.MkTuple5._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1824
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
Typ_fun_1821))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple5__3 @x5)
@a2))))

; </end encoding Prims.MkTuple5._3>

; encoding sigelt Prims.MkTuple5._4

; <Start encoding Prims.MkTuple5._4>
(declare-fun Prims.MkTuple5._4 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'd)
(declare-fun Typ_fun_1826 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1826 kinding
(assert (HasKind Typ_fun_1826
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1826)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1826)))))
;;;;;;;;;;;;;;;;Typ_fun_1826 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1826)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1826)))))
(declare-fun Prims.MkTuple5._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1829
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
Typ_fun_1826))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple5__4 @x5)
@a3))))

; </end encoding Prims.MkTuple5._4>

; encoding sigelt Prims.MkTuple5._5

; <Start encoding Prims.MkTuple5._5>
(declare-fun Prims.MkTuple5._5 (Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple5 'a 'b 'c 'd 'e) -> Tot 'e)
(declare-fun Typ_fun_1831 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1831 kinding
(assert (HasKind Typ_fun_1831
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1831)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1831)))))
;;;;;;;;;;;;;;;;Typ_fun_1831 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1831)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple5 @a2
@a3
@a4
@a5
@a6)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1831)))))
(declare-fun Prims.MkTuple5._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1834
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
Typ_fun_1831))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple5__5 @x5)
@a4))))

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
(declare-fun Typ_fun_1855 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple6
(declare-fun Prims.MkTuple6@tok () Term)

; <Start encoding Prims.Tuple6>

; <start constructor Prims.Tuple6>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type))
 (= 1846
(Type_constr_id (Prims.Tuple6 @a0
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
1846)
(= @a0
(Prims.Tuple6 (Prims.Tuple6@a0 @a0)
(Prims.Tuple6@a1 @a0)
(Prims.Tuple6@a2 @a0)
(Prims.Tuple6@a3 @a0)
(Prims.Tuple6@a4 @a0)
(Prims.Tuple6@a5 @a0)))))

; </end constructor Prims.Tuple6>
;;;;;;;;;;;;;;;;fresh token
(assert (= 1847
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
 (= 1853
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
1853)
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
;;;;;;;;;;;;;;;;Typ_fun_1855 kinding
(assert (HasKind Typ_fun_1855
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1855)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1855)))))
;;;;;;;;;;;;;;;;Typ_fun_1855 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1855)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term))
 (! (implies (and (HasKind @a2
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
@a2)
(HasType @x9
@a3)
(HasType @x10
@a4)
(HasType @x11
@a5)
(HasType @x12
@a6)
(HasType @x13
@a7))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
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
@x13)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1855)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1858
(Term_constr_id Prims.MkTuple6@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple6@tok
Typ_fun_1855))
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
(declare-fun Typ_fun_1860 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1860 kinding
(assert (HasKind Typ_fun_1860
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1860)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1860)))))
;;;;;;;;;;;;;;;;Typ_fun_1860 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1860)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1860)))))
(declare-fun Prims.is_MkTuple6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1863
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
Typ_fun_1860))
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

; encoding sigelt Prims.MkTuple6.'a

; <Start encoding Prims.MkTuple6.'a>
(declare-fun Prims.MkTuple6._a (Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple6._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1865
(Type_constr_id Prims.MkTuple6._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._a @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple6._a@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple6._a @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Kind_type))
  
:pattern ((Prims.MkTuple6._a @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._a @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__a @x6))
  
:pattern ((Prims.MkTuple6._a @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6.'a>

; encoding sigelt Prims.MkTuple6.'b

; <Start encoding Prims.MkTuple6.'b>
(declare-fun Prims.MkTuple6._b (Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple6._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1867
(Type_constr_id Prims.MkTuple6._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._b @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple6._b@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple6._b @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Kind_type))
  
:pattern ((Prims.MkTuple6._b @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._b @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__b @x6))
  
:pattern ((Prims.MkTuple6._b @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6.'b>

; encoding sigelt Prims.MkTuple6.'c

; <Start encoding Prims.MkTuple6.'c>
(declare-fun Prims.MkTuple6._c (Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple6._c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1869
(Type_constr_id Prims.MkTuple6._c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._c @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple6._c@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple6._c @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Kind_type))
  
:pattern ((Prims.MkTuple6._c @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._c @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__c @x6))
  
:pattern ((Prims.MkTuple6._c @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6.'c>

; encoding sigelt Prims.MkTuple6.'d

; <Start encoding Prims.MkTuple6.'d>
(declare-fun Prims.MkTuple6._d (Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple6._d@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1871
(Type_constr_id Prims.MkTuple6._d@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._d @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple6._d@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple6._d @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Kind_type))
  
:pattern ((Prims.MkTuple6._d @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._d @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__d @x6))
  
:pattern ((Prims.MkTuple6._d @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6.'d>

; encoding sigelt Prims.MkTuple6.'e

; <Start encoding Prims.MkTuple6.'e>
(declare-fun Prims.MkTuple6._e (Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple6._e@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1873
(Type_constr_id Prims.MkTuple6._e@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._e @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple6._e@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple6._e @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Kind_type))
  
:pattern ((Prims.MkTuple6._e @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._e @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__e @x6))
  
:pattern ((Prims.MkTuple6._e @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6.'e>

; encoding sigelt Prims.MkTuple6.'f

; <Start encoding Prims.MkTuple6.'f>
(declare-fun Prims.MkTuple6._f (Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple6._f@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1875
(Type_constr_id Prims.MkTuple6._f@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._f@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkTuple6._f @a0
@a1
@a2
@a3
@a4
@a5
@x6))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple6._f@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple6._f@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple6._f @a0
@a1
@a2
@a3
@a4
@a5
@x6)
Kind_type))
  
:pattern ((Prims.MkTuple6._f @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (= (Prims.MkTuple6._f @a0
@a1
@a2
@a3
@a4
@a5
@x6)
(Prims.MkTuple6__f @x6))
  
:pattern ((Prims.MkTuple6._f @a0
@a1
@a2
@a3
@a4
@a5
@x6)))))

; </end encoding Prims.MkTuple6.'f>

; encoding sigelt Prims.MkTuple6._1

; <Start encoding Prims.MkTuple6._1>
(declare-fun Prims.MkTuple6._1 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'a)
(declare-fun Typ_fun_1877 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1877 kinding
(assert (HasKind Typ_fun_1877
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1877)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1877)))))
;;;;;;;;;;;;;;;;Typ_fun_1877 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1877)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1877)))))
(declare-fun Prims.MkTuple6._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1880
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
Typ_fun_1877))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple6__1 @x6)
@a0))))

; </end encoding Prims.MkTuple6._1>

; encoding sigelt Prims.MkTuple6._2

; <Start encoding Prims.MkTuple6._2>
(declare-fun Prims.MkTuple6._2 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'b)
(declare-fun Typ_fun_1882 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1882 kinding
(assert (HasKind Typ_fun_1882
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1882)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1882)))))
;;;;;;;;;;;;;;;;Typ_fun_1882 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1882)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1882)))))
(declare-fun Prims.MkTuple6._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1885
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
Typ_fun_1882))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple6__2 @x6)
@a1))))

; </end encoding Prims.MkTuple6._2>

; encoding sigelt Prims.MkTuple6._3

; <Start encoding Prims.MkTuple6._3>
(declare-fun Prims.MkTuple6._3 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'c)
(declare-fun Typ_fun_1887 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1887 kinding
(assert (HasKind Typ_fun_1887
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1887)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1887)))))
;;;;;;;;;;;;;;;;Typ_fun_1887 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1887)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1887)))))
(declare-fun Prims.MkTuple6._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1890
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
Typ_fun_1887))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple6__3 @x6)
@a2))))

; </end encoding Prims.MkTuple6._3>

; encoding sigelt Prims.MkTuple6._4

; <Start encoding Prims.MkTuple6._4>
(declare-fun Prims.MkTuple6._4 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'd)
(declare-fun Typ_fun_1892 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1892 kinding
(assert (HasKind Typ_fun_1892
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1892)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1892)))))
;;;;;;;;;;;;;;;;Typ_fun_1892 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1892)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1892)))))
(declare-fun Prims.MkTuple6._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1895
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
Typ_fun_1892))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple6__4 @x6)
@a3))))

; </end encoding Prims.MkTuple6._4>

; encoding sigelt Prims.MkTuple6._5

; <Start encoding Prims.MkTuple6._5>
(declare-fun Prims.MkTuple6._5 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'e)
(declare-fun Typ_fun_1897 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1897 kinding
(assert (HasKind Typ_fun_1897
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1897)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1897)))))
;;;;;;;;;;;;;;;;Typ_fun_1897 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1897)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1897)))))
(declare-fun Prims.MkTuple6._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1900
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
Typ_fun_1897))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple6__5 @x6)
@a4))))

; </end encoding Prims.MkTuple6._5>

; encoding sigelt Prims.MkTuple6._6

; <Start encoding Prims.MkTuple6._6>
(declare-fun Prims.MkTuple6._6 (Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple6 'a 'b 'c 'd 'e 'f) -> Tot 'f)
(declare-fun Typ_fun_1902 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1902 kinding
(assert (HasKind Typ_fun_1902
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1902)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1902)))))
;;;;;;;;;;;;;;;;Typ_fun_1902 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1902)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple6 @a2
@a3
@a4
@a5
@a6
@a7)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
@a7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1902)))))
(declare-fun Prims.MkTuple6._6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1905
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
Typ_fun_1902))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple6__6 @x6)
@a5))))

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
(declare-fun Typ_fun_1926 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple7
(declare-fun Prims.MkTuple7@tok () Term)

; <Start encoding Prims.Tuple7>

; <start constructor Prims.Tuple7>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type))
 (= 1917
(Type_constr_id (Prims.Tuple7 @a0
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
1917)
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
(assert (= 1918
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
 (= 1924
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
1924)
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
;;;;;;;;;;;;;;;;Typ_fun_1926 kinding
(assert (HasKind Typ_fun_1926
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1926)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1926)))))
;;;;;;;;;;;;;;;;Typ_fun_1926 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1926)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term))
 (! (implies (and (HasKind @a2
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
@a7)
(HasType @x15
@a8))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
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
@x15)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1926)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 1929
(Term_constr_id Prims.MkTuple7@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple7@tok
Typ_fun_1926))
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
(declare-fun Typ_fun_1931 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1931 kinding
(assert (HasKind Typ_fun_1931
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1931)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1931)))))
;;;;;;;;;;;;;;;;Typ_fun_1931 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1931)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1931)))))
(declare-fun Prims.is_MkTuple7@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1934
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
Typ_fun_1931))
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

; encoding sigelt Prims.MkTuple7.'a

; <Start encoding Prims.MkTuple7.'a>
(declare-fun Prims.MkTuple7._a (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1936
(Type_constr_id Prims.MkTuple7._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._a@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__a @x7))
  
:pattern ((Prims.MkTuple7._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'a>

; encoding sigelt Prims.MkTuple7.'b

; <Start encoding Prims.MkTuple7.'b>
(declare-fun Prims.MkTuple7._b (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1938
(Type_constr_id Prims.MkTuple7._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._b@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__b @x7))
  
:pattern ((Prims.MkTuple7._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'b>

; encoding sigelt Prims.MkTuple7.'c

; <Start encoding Prims.MkTuple7.'c>
(declare-fun Prims.MkTuple7._c (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1940
(Type_constr_id Prims.MkTuple7._c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._c@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__c @x7))
  
:pattern ((Prims.MkTuple7._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'c>

; encoding sigelt Prims.MkTuple7.'d

; <Start encoding Prims.MkTuple7.'d>
(declare-fun Prims.MkTuple7._d (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._d@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1942
(Type_constr_id Prims.MkTuple7._d@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._d@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__d @x7))
  
:pattern ((Prims.MkTuple7._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'d>

; encoding sigelt Prims.MkTuple7.'e

; <Start encoding Prims.MkTuple7.'e>
(declare-fun Prims.MkTuple7._e (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._e@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1944
(Type_constr_id Prims.MkTuple7._e@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._e@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__e @x7))
  
:pattern ((Prims.MkTuple7._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'e>

; encoding sigelt Prims.MkTuple7.'f

; <Start encoding Prims.MkTuple7.'f>
(declare-fun Prims.MkTuple7._f (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._f@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1946
(Type_constr_id Prims.MkTuple7._f@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._f@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._f@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._f@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__f @x7))
  
:pattern ((Prims.MkTuple7._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'f>

; encoding sigelt Prims.MkTuple7.'g

; <Start encoding Prims.MkTuple7.'g>
(declare-fun Prims.MkTuple7._g (Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple7._g@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1948
(Type_constr_id Prims.MkTuple7._g@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._g@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)
(Prims.MkTuple7._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple7._g@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple7._g@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple7._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
Kind_type))
  
:pattern ((Prims.MkTuple7._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (! (= (Prims.MkTuple7._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)
(Prims.MkTuple7__g @x7))
  
:pattern ((Prims.MkTuple7._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@x7)))))

; </end encoding Prims.MkTuple7.'g>

; encoding sigelt Prims.MkTuple7._1

; <Start encoding Prims.MkTuple7._1>
(declare-fun Prims.MkTuple7._1 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'a)
(declare-fun Typ_fun_1950 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1950 kinding
(assert (HasKind Typ_fun_1950
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1950)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1950)))))
;;;;;;;;;;;;;;;;Typ_fun_1950 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1950)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1950)))))
(declare-fun Prims.MkTuple7._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1953
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
Typ_fun_1950))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__1 @x7)
@a0))))

; </end encoding Prims.MkTuple7._1>

; encoding sigelt Prims.MkTuple7._2

; <Start encoding Prims.MkTuple7._2>
(declare-fun Prims.MkTuple7._2 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'b)
(declare-fun Typ_fun_1955 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1955 kinding
(assert (HasKind Typ_fun_1955
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1955)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1955)))))
;;;;;;;;;;;;;;;;Typ_fun_1955 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1955)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1955)))))
(declare-fun Prims.MkTuple7._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1958
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
Typ_fun_1955))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__2 @x7)
@a1))))

; </end encoding Prims.MkTuple7._2>

; encoding sigelt Prims.MkTuple7._3

; <Start encoding Prims.MkTuple7._3>
(declare-fun Prims.MkTuple7._3 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'c)
(declare-fun Typ_fun_1960 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1960 kinding
(assert (HasKind Typ_fun_1960
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1960)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1960)))))
;;;;;;;;;;;;;;;;Typ_fun_1960 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1960)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1960)))))
(declare-fun Prims.MkTuple7._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1963
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
Typ_fun_1960))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__3 @x7)
@a2))))

; </end encoding Prims.MkTuple7._3>

; encoding sigelt Prims.MkTuple7._4

; <Start encoding Prims.MkTuple7._4>
(declare-fun Prims.MkTuple7._4 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'd)
(declare-fun Typ_fun_1965 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1965 kinding
(assert (HasKind Typ_fun_1965
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1965)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1965)))))
;;;;;;;;;;;;;;;;Typ_fun_1965 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1965)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1965)))))
(declare-fun Prims.MkTuple7._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1968
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
Typ_fun_1965))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__4 @x7)
@a3))))

; </end encoding Prims.MkTuple7._4>

; encoding sigelt Prims.MkTuple7._5

; <Start encoding Prims.MkTuple7._5>
(declare-fun Prims.MkTuple7._5 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'e)
(declare-fun Typ_fun_1970 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1970 kinding
(assert (HasKind Typ_fun_1970
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1970)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1970)))))
;;;;;;;;;;;;;;;;Typ_fun_1970 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1970)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1970)))))
(declare-fun Prims.MkTuple7._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1973
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
Typ_fun_1970))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__5 @x7)
@a4))))

; </end encoding Prims.MkTuple7._5>

; encoding sigelt Prims.MkTuple7._6

; <Start encoding Prims.MkTuple7._6>
(declare-fun Prims.MkTuple7._6 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'f)
(declare-fun Typ_fun_1975 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1975 kinding
(assert (HasKind Typ_fun_1975
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1975)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1975)))))
;;;;;;;;;;;;;;;;Typ_fun_1975 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1975)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1975)))))
(declare-fun Prims.MkTuple7._6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1978
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
Typ_fun_1975))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__6 @x7)
@a5))))

; </end encoding Prims.MkTuple7._6>

; encoding sigelt Prims.MkTuple7._7

; <Start encoding Prims.MkTuple7._7>
(declare-fun Prims.MkTuple7._7 (Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple7 'a 'b 'c 'd 'e 'f 'g) -> Tot 'g)
(declare-fun Typ_fun_1980 () Type)
;;;;;;;;;;;;;;;;Typ_fun_1980 kinding
(assert (HasKind Typ_fun_1980
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_1980)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1980)))))
;;;;;;;;;;;;;;;;Typ_fun_1980 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_1980)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@x9 Term))
 (! (implies (and (HasKind @a2
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
(Prims.Tuple7 @a2
@a3
@a4
@a5
@a6
@a7
@a8)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)
@a8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_1980)))))
(declare-fun Prims.MkTuple7._7@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 1983
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
Typ_fun_1980))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@x7 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple7__7 @x7)
@a6))))

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
(declare-fun Typ_fun_2004 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkTuple8
(declare-fun Prims.MkTuple8@tok () Term)

; <Start encoding Prims.Tuple8>

; <start constructor Prims.Tuple8>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type))
 (= 1995
(Type_constr_id (Prims.Tuple8 @a0
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
1995)
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
(assert (= 1996
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
 (= 2002
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
2002)
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
;;;;;;;;;;;;;;;;Typ_fun_2004 kinding
(assert (HasKind Typ_fun_2004
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2004)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2004)))))
;;;;;;;;;;;;;;;;Typ_fun_2004 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2004)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term) (@x11 Term) (@x12 Term) (@x13 Term) (@x14 Term) (@x15 Term) (@x16 Term) (@x17 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
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
@a8)
(HasType @x17
@a9))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@x11)
@x12)
@x13)
@x14)
@x15)
@x16)
@x17)
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@x11)
@x12)
@x13)
@x14)
@x15)
@x16)
@x17)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2004)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2007
(Term_constr_id Prims.MkTuple8@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkTuple8@tok
Typ_fun_2004))
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
(declare-fun Typ_fun_2009 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2009 kinding
(assert (HasKind Typ_fun_2009
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2009)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2009)))))
;;;;;;;;;;;;;;;;Typ_fun_2009 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2009)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2009)))))
(declare-fun Prims.is_MkTuple8@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2012
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
Typ_fun_2009))
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

; encoding sigelt Prims.MkTuple8.'a

; <Start encoding Prims.MkTuple8.'a>
(declare-fun Prims.MkTuple8._a (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._a@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2014
(Type_constr_id Prims.MkTuple8._a@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._a@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._a@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__a @x8))
  
:pattern ((Prims.MkTuple8._a @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'a>

; encoding sigelt Prims.MkTuple8.'b

; <Start encoding Prims.MkTuple8.'b>
(declare-fun Prims.MkTuple8._b (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._b@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2016
(Type_constr_id Prims.MkTuple8._b@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._b@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._b@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__b @x8))
  
:pattern ((Prims.MkTuple8._b @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'b>

; encoding sigelt Prims.MkTuple8.'c

; <Start encoding Prims.MkTuple8.'c>
(declare-fun Prims.MkTuple8._c (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._c@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2018
(Type_constr_id Prims.MkTuple8._c@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._c@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._c@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__c @x8))
  
:pattern ((Prims.MkTuple8._c @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'c>

; encoding sigelt Prims.MkTuple8.'d

; <Start encoding Prims.MkTuple8.'d>
(declare-fun Prims.MkTuple8._d (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._d@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2020
(Type_constr_id Prims.MkTuple8._d@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._d@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._d@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__d @x8))
  
:pattern ((Prims.MkTuple8._d @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'d>

; encoding sigelt Prims.MkTuple8.'e

; <Start encoding Prims.MkTuple8.'e>
(declare-fun Prims.MkTuple8._e (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._e@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2022
(Type_constr_id Prims.MkTuple8._e@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._e@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._e@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__e @x8))
  
:pattern ((Prims.MkTuple8._e @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'e>

; encoding sigelt Prims.MkTuple8.'f

; <Start encoding Prims.MkTuple8.'f>
(declare-fun Prims.MkTuple8._f (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._f@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2024
(Type_constr_id Prims.MkTuple8._f@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._f@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._f@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._f@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__f @x8))
  
:pattern ((Prims.MkTuple8._f @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'f>

; encoding sigelt Prims.MkTuple8.'g

; <Start encoding Prims.MkTuple8.'g>
(declare-fun Prims.MkTuple8._g (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._g@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2026
(Type_constr_id Prims.MkTuple8._g@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._g@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._g@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._g@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__g @x8))
  
:pattern ((Prims.MkTuple8._g @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'g>

; encoding sigelt Prims.MkTuple8.'h

; <Start encoding Prims.MkTuple8.'h>
(declare-fun Prims.MkTuple8._h (Type Type Type Type Type Type Type Type Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun Prims.MkTuple8._h@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2028
(Type_constr_id Prims.MkTuple8._h@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._h@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)
(Prims.MkTuple8._h @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT (ApplyTT Prims.MkTuple8._h@tok
@a0)
@a1)
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@x8)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkTuple8._h@tok)))
;;;;;;;;;;;;;;;;kinding
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
(HasKind (Prims.MkTuple8._h @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
Kind_type))
  
:pattern ((Prims.MkTuple8._h @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (= (Prims.MkTuple8._h @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)
(Prims.MkTuple8__h @x8))
  
:pattern ((Prims.MkTuple8._h @a0
@a1
@a2
@a3
@a4
@a5
@a6
@a7
@x8)))))

; </end encoding Prims.MkTuple8.'h>

; encoding sigelt Prims.MkTuple8._1

; <Start encoding Prims.MkTuple8._1>
(declare-fun Prims.MkTuple8._1 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'a)
(declare-fun Typ_fun_2030 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2030 kinding
(assert (HasKind Typ_fun_2030
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2030)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2030)))))
;;;;;;;;;;;;;;;;Typ_fun_2030 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2030)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2030)))))
(declare-fun Prims.MkTuple8._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2033
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
Typ_fun_2030))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__1 @x8)
@a0))))

; </end encoding Prims.MkTuple8._1>

; encoding sigelt Prims.MkTuple8._2

; <Start encoding Prims.MkTuple8._2>
(declare-fun Prims.MkTuple8._2 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'b)
(declare-fun Typ_fun_2035 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2035 kinding
(assert (HasKind Typ_fun_2035
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2035)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2035)))))
;;;;;;;;;;;;;;;;Typ_fun_2035 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2035)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a3))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2035)))))
(declare-fun Prims.MkTuple8._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2038
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
Typ_fun_2035))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__2 @x8)
@a1))))

; </end encoding Prims.MkTuple8._2>

; encoding sigelt Prims.MkTuple8._3

; <Start encoding Prims.MkTuple8._3>
(declare-fun Prims.MkTuple8._3 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'c)
(declare-fun Typ_fun_2040 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2040 kinding
(assert (HasKind Typ_fun_2040
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2040)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2040)))))
;;;;;;;;;;;;;;;;Typ_fun_2040 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2040)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a4))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2040)))))
(declare-fun Prims.MkTuple8._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2043
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
Typ_fun_2040))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__3 @x8)
@a2))))

; </end encoding Prims.MkTuple8._3>

; encoding sigelt Prims.MkTuple8._4

; <Start encoding Prims.MkTuple8._4>
(declare-fun Prims.MkTuple8._4 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'd)
(declare-fun Typ_fun_2045 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2045 kinding
(assert (HasKind Typ_fun_2045
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2045)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2045)))))
;;;;;;;;;;;;;;;;Typ_fun_2045 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2045)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a5))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2045)))))
(declare-fun Prims.MkTuple8._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2048
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
Typ_fun_2045))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__4 @x8)
@a3))))

; </end encoding Prims.MkTuple8._4>

; encoding sigelt Prims.MkTuple8._5

; <Start encoding Prims.MkTuple8._5>
(declare-fun Prims.MkTuple8._5 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'e)
(declare-fun Typ_fun_2050 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2050 kinding
(assert (HasKind Typ_fun_2050
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2050)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2050)))))
;;;;;;;;;;;;;;;;Typ_fun_2050 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2050)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a6))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2050)))))
(declare-fun Prims.MkTuple8._5@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2053
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
Typ_fun_2050))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__5 @x8)
@a4))))

; </end encoding Prims.MkTuple8._5>

; encoding sigelt Prims.MkTuple8._6

; <Start encoding Prims.MkTuple8._6>
(declare-fun Prims.MkTuple8._6 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'f)
(declare-fun Typ_fun_2055 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2055 kinding
(assert (HasKind Typ_fun_2055
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2055)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2055)))))
;;;;;;;;;;;;;;;;Typ_fun_2055 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2055)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a7))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2055)))))
(declare-fun Prims.MkTuple8._6@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2058
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
Typ_fun_2055))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__6 @x8)
@a5))))

; </end encoding Prims.MkTuple8._6>

; encoding sigelt Prims.MkTuple8._7

; <Start encoding Prims.MkTuple8._7>
(declare-fun Prims.MkTuple8._7 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'g)
(declare-fun Typ_fun_2060 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2060 kinding
(assert (HasKind Typ_fun_2060
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2060)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2060)))))
;;;;;;;;;;;;;;;;Typ_fun_2060 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2060)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a8))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2060)))))
(declare-fun Prims.MkTuple8._7@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2063
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
Typ_fun_2060))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__7 @x8)
@a6))))

; </end encoding Prims.MkTuple8._7>

; encoding sigelt Prims.MkTuple8._8

; <Start encoding Prims.MkTuple8._8>
(declare-fun Prims.MkTuple8._8 (Type Type Type Type Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(Tuple8 'a 'b 'c 'd 'e 'f 'g 'h) -> Tot 'h)
(declare-fun Typ_fun_2065 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2065 kinding
(assert (HasKind Typ_fun_2065
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2065)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2065)))))
;;;;;;;;;;;;;;;;Typ_fun_2065 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2065)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@a8 Type) (@a9 Type) (@x10 Term))
 (! (implies (and (HasKind @a2
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
(HasKind @a9
Kind_type)
(HasType @x10
(Prims.Tuple8 @a2
@a3
@a4
@a5
@a6
@a7
@a8
@a9)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)
@a9))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@a6)
@a7)
@a8)
@a9)
@x10)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2065)))))
(declare-fun Prims.MkTuple8._8@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2068
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
Typ_fun_2065))
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@a6 Type) (@a7 Type) (@x8 Term))
 (implies (and (HasKind @a0
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
(HasType (Prims.MkTuple8__8 @x8)
@a7))))

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
(declare-fun Kind_arrow_2093 (Type Type) Kind)
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
(declare-fun Typ_fun_2107 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkDTuple3
(declare-fun Prims.MkDTuple3@tok () Term)

; <Start encoding Prims.DTuple3>

; <start constructor Prims.DTuple3>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (= 2094
(Type_constr_id (Prims.DTuple3 @a0
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
2094)
(= @a0
(Prims.DTuple3 (Prims.DTuple3@a0 @a0)
(Prims.DTuple3@a1 @a0)
(Prims.DTuple3@a2 @a0)))))

; </end constructor Prims.DTuple3>
;;;;;;;;;;;;;;;;fresh token
(assert (= 2095
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
@a2)))))
;;;;;;;;;;;;;;;;Kind_arrow_2093 interpretation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (iff (HasKind @a0
(Kind_arrow_2093 @a1
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
(Kind_arrow_2093 @a1
@a2))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.DTuple3@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
 (= 2103
(Term_constr_id (Prims.MkDTuple3 @a0
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
2103)
(= @x0
(Prims.MkDTuple3 (Prims.MkDTuple3_a @x0)
(Prims.MkDTuple3_b @x0)
(Prims.MkDTuple3_c @x0)
(Prims.MkDTuple3__1 @x0)
(Prims.MkDTuple3__2 @x0)
(Prims.MkDTuple3__3 @x0)))))

; </end constructor Prims.MkDTuple3>
;;;;;;;;;;;;;;;;Typ_fun_2107 kinding
(assert (HasKind Typ_fun_2107
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2107)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2107)))))
;;;;;;;;;;;;;;;;Typ_fun_2107 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2107)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasType @x5
@a2)
(HasType @x6
(ApplyTE @a3
@x5))
(HasType @x7
(ApplyTE (ApplyTE @a4
@x5)
@x6)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)
(Prims.DTuple3 @a2
@a3
@a4)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
@x6)
@x7)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2107)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2112
(Term_constr_id Prims.MkDTuple3@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkDTuple3@tok
Typ_fun_2107))
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
(Kind_arrow_182 @a1))
(HasKind @a3
(Kind_arrow_2093 @a2
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
(Kind_arrow_182 @a1))
(HasKind @a3
(Kind_arrow_2093 @a2
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
(declare-fun Typ_fun_2120 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2120 kinding
(assert (HasKind Typ_fun_2120
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2120)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2120)))))
;;;;;;;;;;;;;;;;Typ_fun_2120 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2120)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasType @x5
(Prims.DTuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2120)))))
(declare-fun Prims.is_MkDTuple3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2123
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
Typ_fun_2120))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
(assert (= 2129
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
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple3.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
(assert (= 2138
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
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple3.b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
(assert (= 2149
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
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple3.c@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
(declare-fun Typ_fun_2160 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2160 kinding
(assert (HasKind Typ_fun_2160
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2160)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2160)))))
;;;;;;;;;;;;;;;;Typ_fun_2160 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2160)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasType @x5
(Prims.DTuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple3.a @a2
@a3
@a4
@x5)))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2160)))))
(declare-fun Prims.MkDTuple3._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2163
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
Typ_fun_2160))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.MkDTuple3__1 @x3)
(Prims.MkDTuple3.a @a0
@a1
@a2
@x3)))
  
:pattern ((HasType (Prims.MkDTuple3__1 @x3)
(Prims.MkDTuple3.a @a0
@a1
@a2
@x3))))))

; </end encoding Prims.MkDTuple3._1>

; encoding sigelt Prims.MkDTuple3._2

; <Start encoding Prims.MkDTuple3._2>
(declare-fun Prims.MkDTuple3._2 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple3 a b c) -> Tot (b projectee (_1 projectee)))
(declare-fun Typ_fun_2176 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2176 kinding
(assert (HasKind Typ_fun_2176
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2176)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2176)))))
;;;;;;;;;;;;;;;;Typ_fun_2176 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2176)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasType @x5
(Prims.DTuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple3.b @a2
@a3
@a4
@x5
(Prims.MkDTuple3._1 @a2
@a3
@a4
@x5))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2176)))))
(declare-fun Prims.MkDTuple3._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2179
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
Typ_fun_2176))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.MkDTuple3__2 @x3)
(Prims.MkDTuple3.b @a0
@a1
@a2
@x3
(Prims.MkDTuple3._1 @a0
@a1
@a2
@x3))))
  
:pattern ((HasType (Prims.MkDTuple3__2 @x3)
(Prims.MkDTuple3.b @a0
@a1
@a2
@x3
(Prims.MkDTuple3._1 @a0
@a1
@a2
@x3)))))))

; </end encoding Prims.MkDTuple3._2>

; encoding sigelt Prims.MkDTuple3._3

; <Start encoding Prims.MkDTuple3._3>
(declare-fun Prims.MkDTuple3._3 (Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple3 a b c) -> Tot (c projectee (_1 projectee) (_2 projectee)))
(declare-fun Typ_fun_2194 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2194 kinding
(assert (HasKind Typ_fun_2194
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2194)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2194)))))
;;;;;;;;;;;;;;;;Typ_fun_2194 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2194)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasType @x5
(Prims.DTuple3 @a2
@a3
@a4)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)
(Prims.MkDTuple3.c @a2
@a3
@a4
@x5
(Prims.MkDTuple3._1 @a2
@a3
@a4
@x5)
(Prims.MkDTuple3._2 @a2
@a3
@a4
@x5))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2194)))))
(declare-fun Prims.MkDTuple3._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2197
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
Typ_fun_2194))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasType @x3
(Prims.DTuple3 @a0
@a1
@a2)))
(HasType (Prims.MkDTuple3__3 @x3)
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
  
:pattern ((HasType (Prims.MkDTuple3__3 @x3)
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
@x3)))))))

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
(declare-fun Kind_arrow_2228 (Type Type Type) Kind)
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
(declare-fun Typ_fun_2244 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: MkDTuple4
(declare-fun Prims.MkDTuple4@tok () Term)

; <Start encoding Prims.DTuple4>

; <start constructor Prims.DTuple4>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (= 2229
(Type_constr_id (Prims.DTuple4 @a0
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
2229)
(= @a0
(Prims.DTuple4 (Prims.DTuple4@a0 @a0)
(Prims.DTuple4@a1 @a0)
(Prims.DTuple4@a2 @a0)
(Prims.DTuple4@a3 @a0)))))

; </end constructor Prims.DTuple4>
;;;;;;;;;;;;;;;;fresh token
(assert (= 2230
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
@a3)))))
;;;;;;;;;;;;;;;;Kind_arrow_2228 interpretation
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (iff (HasKind @a0
(Kind_arrow_2228 @a1
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
(Kind_arrow_2228 @a1
@a2
@a3))))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.DTuple4@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
 (= 2239
(Term_constr_id (Prims.MkDTuple4 @a0
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
2239)
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
;;;;;;;;;;;;;;;;Typ_fun_2244 kinding
(assert (HasKind Typ_fun_2244
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2244)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2244)))))
;;;;;;;;;;;;;;;;Typ_fun_2244 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2244)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term) (@x7 Term) (@x8 Term) (@x9 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasKind @a5
(Kind_arrow_2228 @a4
@a3
@a2))
(HasType @x6
@a2)
(HasType @x7
(ApplyTE @a3
@x6))
(HasType @x8
(ApplyTE (ApplyTE @a4
@x6)
@x7))
(HasType @x9
(ApplyTE (ApplyTE (ApplyTE @a5
@x6)
@x7)
@x8)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)
(Prims.DTuple4 @a2
@a3
@a4
@a5)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
@x7)
@x8)
@x9)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2244)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2250
(Term_constr_id Prims.MkDTuple4@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType Prims.MkDTuple4@tok
Typ_fun_2244))
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
(Kind_arrow_182 @a1))
(HasKind @a3
(Kind_arrow_2093 @a2
@a1))
(HasKind @a4
(Kind_arrow_2228 @a3
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
(Kind_arrow_182 @a1))
(HasKind @a3
(Kind_arrow_2093 @a2
@a1))
(HasKind @a4
(Kind_arrow_2228 @a3
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
(declare-fun Typ_fun_2261 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2261 kinding
(assert (HasKind Typ_fun_2261
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2261)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2261)))))
;;;;;;;;;;;;;;;;Typ_fun_2261 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2261)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasKind @a5
(Kind_arrow_2228 @a4
@a3
@a2))
(HasType @x6
(Prims.DTuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
Prims.bool))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2261)))))
(declare-fun Prims.is_MkDTuple4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2264
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
Typ_fun_2261))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
(assert (= 2272
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
@x4)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.a@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
(assert (= 2284
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
@x5)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.b@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
(assert (= 2298
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
@x6)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.c@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
(assert (= 2315
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
@x7)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind Prims.MkDTuple4.d@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term) (@x7 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
(declare-fun Typ_fun_2330 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2330 kinding
(assert (HasKind Typ_fun_2330
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2330)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2330)))))
;;;;;;;;;;;;;;;;Typ_fun_2330 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2330)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasKind @a5
(Kind_arrow_2228 @a4
@a3
@a2))
(HasType @x6
(Prims.DTuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkDTuple4.a @a2
@a3
@a4
@a5
@x6)))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2330)))))
(declare-fun Prims.MkDTuple4._1@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2333
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
Typ_fun_2330))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4__1 @x4)
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4)))
  
:pattern ((HasType (Prims.MkDTuple4__1 @x4)
(Prims.MkDTuple4.a @a0
@a1
@a2
@a3
@x4))))))

; </end encoding Prims.MkDTuple4._1>

; encoding sigelt Prims.MkDTuple4._2

; <Start encoding Prims.MkDTuple4._2>
(declare-fun Prims.MkDTuple4._2 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (b projectee (_1 projectee)))
(declare-fun Typ_fun_2350 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2350 kinding
(assert (HasKind Typ_fun_2350
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2350)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2350)))))
;;;;;;;;;;;;;;;;Typ_fun_2350 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2350)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasKind @a5
(Kind_arrow_2228 @a4
@a3
@a2))
(HasType @x6
(Prims.DTuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkDTuple4.b @a2
@a3
@a4
@a5
@x6
(Prims.MkDTuple4._1 @a2
@a3
@a4
@a5
@x6))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2350)))))
(declare-fun Prims.MkDTuple4._2@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2353
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
Typ_fun_2350))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4__2 @x4)
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
  
:pattern ((HasType (Prims.MkDTuple4__2 @x4)
(Prims.MkDTuple4.b @a0
@a1
@a2
@a3
@x4
(Prims.MkDTuple4._1 @a0
@a1
@a2
@a3
@x4)))))))

; </end encoding Prims.MkDTuple4._2>

; encoding sigelt Prims.MkDTuple4._3

; <Start encoding Prims.MkDTuple4._3>
(declare-fun Prims.MkDTuple4._3 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (c projectee (_1 projectee) (_2 projectee)))
(declare-fun Typ_fun_2372 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2372 kinding
(assert (HasKind Typ_fun_2372
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2372)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2372)))))
;;;;;;;;;;;;;;;;Typ_fun_2372 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2372)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasKind @a5
(Kind_arrow_2228 @a4
@a3
@a2))
(HasType @x6
(Prims.DTuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkDTuple4.c @a2
@a3
@a4
@a5
@x6
(Prims.MkDTuple4._1 @a2
@a3
@a4
@a5
@x6)
(Prims.MkDTuple4._2 @a2
@a3
@a4
@a5
@x6))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2372)))))
(declare-fun Prims.MkDTuple4._3@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2375
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
Typ_fun_2372))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4__3 @x4)
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
  
:pattern ((HasType (Prims.MkDTuple4__3 @x4)
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
@x4)))))))

; </end encoding Prims.MkDTuple4._3>

; encoding sigelt Prims.MkDTuple4._4

; <Start encoding Prims.MkDTuple4._4>
(declare-fun Prims.MkDTuple4._4 (Type Type Type Type Term) Term)
;;;;;;;;;;;;;;;;(projectee:(DTuple4 a b c d) -> Tot (d projectee (_1 projectee) (_2 projectee) (_3 projectee)))
(declare-fun Typ_fun_2396 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2396 kinding
(assert (HasKind Typ_fun_2396
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2396)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2396)))))
;;;;;;;;;;;;;;;;Typ_fun_2396 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2396)
(forall ((@a2 Type) (@a3 Type) (@a4 Type) (@a5 Type) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasKind @a4
(Kind_arrow_2093 @a3
@a2))
(HasKind @a5
(Kind_arrow_2228 @a4
@a3
@a2))
(HasType @x6
(Prims.DTuple4 @a2
@a3
@a4
@a5)))
(HasType (ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)
(Prims.MkDTuple4.d @a2
@a3
@a4
@a5
@x6
(Prims.MkDTuple4._1 @a2
@a3
@a4
@a5
@x6)
(Prims.MkDTuple4._2 @a2
@a3
@a4
@a5
@x6)
(Prims.MkDTuple4._3 @a2
@a3
@a4
@a5
@x6))))
  
:pattern ((ApplyEE (ApplyET (ApplyET (ApplyET (ApplyET @x1
@a2)
@a3)
@a4)
@a5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2396)))))
(declare-fun Prims.MkDTuple4._4@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2399
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
Typ_fun_2396))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
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
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
(HasKind @a2
(Kind_arrow_2093 @a1
@a0))
(HasKind @a3
(Kind_arrow_2228 @a2
@a1
@a0))
(HasType @x4
(Prims.DTuple4 @a0
@a1
@a2
@a3)))
(HasType (Prims.MkDTuple4__4 @x4)
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
  
:pattern ((HasType (Prims.MkDTuple4__4 @x4)
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
@x4)))))))

; </end encoding Prims.MkDTuple4._4>

; encoding sigelt Prims.as_requires

; <Start encoding Prims.as_requires>
;;;;;;;;;;;;;;;;((a -> Type) -> Type)
(declare-fun Kind_arrow_2406 (Type) Kind)
;;;;;;;;;;;;;;;;Kind_arrow_2406 interpretation
(assert (forall ((@a0 Type) (@a1 Type))
 (! (iff (HasKind @a0
(Kind_arrow_2406 @a1))
(and (is-Kind_arrow (PreKind @a0))
(forall ((@a2 Type))
 (! (implies (HasKind @a2
(Kind_arrow_182 @a1))
(HasKind (ApplyTT @a0
@a2)
Kind_type))
  
:pattern ((ApplyTT @a0
@a2))))))
  
:pattern ((HasKind @a0
(Kind_arrow_2406 @a1))))))
(declare-fun Prims.as_requires (Type Type) Type)
(declare-fun Prims.as_requires@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2407
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
(declare-fun Typ_lam_2408 (Type) Type)
;;;;;;;;;;;;;;;;Typ_lam interpretation
(assert (forall ((@x0 Term) (@a1 Type))
 (! (implies (HasType @x0
@a1)
(= (ApplyTE (Typ_lam_2408 @a1)
@x0)
Prims.True))
  
:pattern ((ApplyTE (Typ_lam_2408 @a1)
@x0)))))
;;;;;;;;;;;;;;;;Typ_lam kinding
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_lam_2408 @a0)
(Kind_arrow_182 @a0))
  
:pattern ((Typ_lam_2408 @a0)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2406 @a0)))
(= (Prims.as_requires @a0
@a1)
(ApplyTT @a1
(Typ_lam_2408 @a0))))
  
:pattern ((Prims.as_requires @a0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2406 @a0)))
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
(assert (= 2416
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
(declare-fun Typ_lam_2417 (Term Type) Type)
;;;;;;;;;;;;;;;;Typ_lam interpretation
(assert (forall ((@x0 Term) (@x1 Term) (@a2 Type))
 (! (implies (HasType @x0
@a2)
(= (ApplyTE (Typ_lam_2417 @x1
@a2)
@x0)
(Prims.l_not (Prims.b2t (Prims.op_Equality @a2
@x0
@x1)))))
  
:pattern ((ApplyTE (Typ_lam_2417 @x1
@a2)
@x0)))))
;;;;;;;;;;;;;;;;Typ_lam kinding
(assert (forall ((@x0 Term) (@a1 Type))
 (! (HasKind (Typ_lam_2417 @x0
@a1)
(Kind_arrow_182 @a1))
  
:pattern ((Typ_lam_2417 @x0
@a1)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2406 @a0))
(HasType @x2
@a0))
(= (Valid (Prims.as_ensures @a0
@a1
@x2))
(not (Valid (ApplyTT @a1
(Typ_lam_2417 @x2
@a0))))))
  
:pattern ((Valid (Prims.as_ensures @a0
@a1
@x2))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_2406 @a0))
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

; <Start encoding Prims.fst>
(declare-fun Prims.fst (Type Type Term) Term)
(declare-fun Prims.fst@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2420
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
Typ_fun_1655))
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

; </end encoding Prims.fst>

; encoding sigelt let Prims.fst : ((Tuple2 'a 'b) -> Tot 'a)

; <Start encoding Prims.fst>
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

; <Start encoding Prims.snd>
(declare-fun Prims.snd (Type Type Term) Term)
(declare-fun Prims.snd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2422
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
Typ_fun_1660))
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

; </end encoding Prims.snd>

; encoding sigelt let Prims.snd : ((Tuple2 'a 'b) -> Tot 'b)

; <Start encoding Prims.snd>
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

; <Start encoding Prims.dfst>
(declare-fun Prims.dfst (Type Type Term) Term)
;;;;;;;;;;;;;;;;((DTuple2 a b) -> Tot a)
(declare-fun Typ_fun_2427 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2427 kinding
(assert (HasKind Typ_fun_2427
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2427)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2427)))))
;;;;;;;;;;;;;;;;Typ_fun_2427 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2427)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasType @x4
(Prims.DTuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@a2))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2427)))))
(declare-fun Prims.dfst@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2430
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
Typ_fun_2427))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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

; </end encoding Prims.dfst>

; encoding sigelt let Prims.dfst : ((DTuple2 a b) -> Tot a)

; <Start encoding Prims.dfst>
;;;;;;;;;;;;;;;;Equation for Prims.dfst
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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

; <Start encoding Prims.dsnd>
(declare-fun Prims.dsnd (Type Type Term) Term)
;;;;;;;;;;;;;;;;(t:(DTuple2 a b) -> Tot (b (_1 t)))
(declare-fun Typ_fun_2445 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2445 kinding
(assert (HasKind Typ_fun_2445
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2445)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2445)))))
;;;;;;;;;;;;;;;;Typ_fun_2445 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2445)
(forall ((@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
(Kind_arrow_182 @a2))
(HasType @x4
(Prims.DTuple2 @a2
@a3)))
(HasType (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
(ApplyTE @a3
(Prims.MkDTuple2._1 @a2
@a3
@x4))))
  
:pattern ((ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2445)))))
(declare-fun Prims.dsnd@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2448
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
Typ_fun_2445))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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

; </end encoding Prims.dsnd>

; encoding sigelt let Prims.dsnd : (t:(DTuple2 a b) -> Tot (b (_1 t)))

; <Start encoding Prims.dsnd>
;;;;;;;;;;;;;;;;Equation for Prims.dsnd
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
(Kind_arrow_182 @a0))
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
(assert (= 2457
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
(Kind_arrow_182 @a0)))
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
(Kind_arrow_182 @a0)))
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
(assert (= 2459
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

; encoding sigelt Prims._assume

; <Start encoding Prims._assume>
(declare-fun Prims._assume (Type Term) Term)
(declare-fun Non_total_Typ_fun_2460 () Type)
(assert (HasKind Non_total_Typ_fun_2460
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Non_total_Typ_fun_2460)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2460)))))
(declare-fun Prims._assume@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2462
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
Non_total_Typ_fun_2460))
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
(declare-fun Typ_fun_2464 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2464 kinding
(assert (HasKind Typ_fun_2464
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2464)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2464)))))
;;;;;;;;;;;;;;;;Typ_fun_2464 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2464)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
Prims.unit))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
@a2))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2464)))))
(declare-fun Prims.magic@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2467
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
Typ_fun_2464))
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
(declare-fun Non_total_Typ_fun_2468 () Type)
(assert (HasKind Non_total_Typ_fun_2468
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Non_total_Typ_fun_2468)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2468)))))
(declare-fun Prims.admitP@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2470
(Term_constr_id Prims.admitP@tok)))
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.admitP@tok
@a0)
(Prims.admitP @a0))
  
:pattern ((ApplyET Prims.admitP@tok
@a0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.admitP@tok
Non_total_Typ_fun_2468))
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
(declare-fun Non_total_Typ_fun_2471 () Type)
(assert (HasKind Non_total_Typ_fun_2471
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Non_total_Typ_fun_2471)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2471)))))
(declare-fun Prims._assert@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2473
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
Non_total_Typ_fun_2471))
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
(declare-fun Non_total_Typ_fun_2474 () Type)
(assert (HasKind Non_total_Typ_fun_2474
Kind_type))
;;;;;;;;;;;;;;;;pre-typing
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Non_total_Typ_fun_2474)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Non_total_Typ_fun_2474)))))
(declare-fun Prims.cut@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2476
(Term_constr_id Prims.cut@tok)))
(assert (forall ((@a0 Type))
 (! (= (ApplyET Prims.cut@tok
@a0)
(Prims.cut @a0))
  
:pattern ((ApplyET Prims.cut@tok
@a0)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.cut@tok
Non_total_Typ_fun_2474))
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

; encoding sigelt Prims.raise

; <Start encoding Prims.raise>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun Prims.raise (Type Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun Prims.raise@tok () Term)

; </end encoding Prims.raise>

; encoding sigelt Prims.ignore

; <Start encoding Prims.ignore>
(declare-fun Prims.ignore (Type Term) Term)
;;;;;;;;;;;;;;;;('a -> Tot unit)
(declare-fun Typ_fun_2485 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2485 kinding
(assert (HasKind Typ_fun_2485
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2485)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2485)))))
;;;;;;;;;;;;;;;;Typ_fun_2485 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2485)
(forall ((@a2 Type) (@x3 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
@a2))
(HasType (ApplyEE (ApplyET @x1
@a2)
@x3)
Prims.unit))
  
:pattern ((ApplyEE (ApplyET @x1
@a2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2485)))))
(declare-fun Prims.ignore@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2488
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
Typ_fun_2485))
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

; </end encoding Prims.ignore>

; encoding sigelt let Prims.ignore : ('a -> Tot unit)

; <Start encoding Prims.ignore>
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

; encoding sigelt Prims.erase

; <Start encoding Prims.erase>
(declare-fun Prims.erase (Type Term) Term)
(declare-fun Prims.erase@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2490
(Term_constr_id Prims.erase@tok)))
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyEE (ApplyET Prims.erase@tok
@a0)
@x1)
(Prims.erase @a0
@x1))
  
:pattern ((ApplyEE (ApplyET Prims.erase@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.erase@tok
Typ_fun_2485))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(HasType (Prims.erase @a0
@x1)
Prims.unit))
  
:pattern ((Prims.erase @a0
@x1)))))

; </end encoding Prims.erase>

; encoding sigelt let Prims.erase : ('a -> Tot unit)

; <Start encoding Prims.erase>
;;;;;;;;;;;;;;;;Equation for Prims.erase
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0))
(= (Prims.erase @a0
@x1)
Term_unit))
  
:pattern ((Prims.erase @a0
@x1)))))

; </end encoding Prims.erase>

; encoding sigelt Prims.min

; <Start encoding Prims.min>
(declare-fun Prims.min (Term Term) Term)
;;;;;;;;;;;;;;;;(int -> int -> Tot int)
(declare-fun Typ_fun_2492 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2492 kinding
(assert (HasKind Typ_fun_2492
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2492)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2492)))))
;;;;;;;;;;;;;;;;Typ_fun_2492 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2492)
(forall ((@x2 Term) (@x3 Term))
 (! (implies (and (HasType @x2
Prims.int)
(HasType @x3
Prims.int))
(HasType (ApplyEE (ApplyEE @x1
@x2)
@x3)
Prims.int))
  
:pattern ((ApplyEE (ApplyEE @x1
@x2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2492)))))
(declare-fun Prims.min@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2495
(Term_constr_id Prims.min@tok)))
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (ApplyEE (ApplyEE Prims.min@tok
@x0)
@x1)
(Prims.min @x0
@x1))
  
:pattern ((ApplyEE (ApplyEE Prims.min@tok
@x0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.min@tok
Typ_fun_2492))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
Prims.int)
(HasType @x1
Prims.int))
(HasType (Prims.min @x0
@x1)
Prims.int))
  
:pattern ((Prims.min @x0
@x1)))))

; </end encoding Prims.min>

; encoding sigelt Prims.max

; <Start encoding Prims.max>
(declare-fun Prims.max (Term Term) Term)
(declare-fun Prims.max@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2497
(Term_constr_id Prims.max@tok)))
(assert (forall ((@x0 Term) (@x1 Term))
 (! (= (ApplyEE (ApplyEE Prims.max@tok
@x0)
@x1)
(Prims.max @x0
@x1))
  
:pattern ((ApplyEE (ApplyEE Prims.max@tok
@x0)
@x1)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType Prims.max@tok
Typ_fun_2492))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@x0 Term) (@x1 Term))
 (! (implies (and (HasType @x0
Prims.int)
(HasType @x1
Prims.int))
(HasType (Prims.max @x0
@x1)
Prims.int))
  
:pattern ((Prims.max @x0
@x1)))))

; </end encoding Prims.max>

; encoding sigelt Prims.nat

; <Start encoding Prims.nat>
(declare-fun Prims.nat () Type)
(declare-fun Prims.nat@tok () Type)
;;;;;;;;;;;;;;;;name-token correspondence
(assert (= Prims.nat@tok
Prims.nat))
(declare-fun Typ_refine_2498 () Type)
(assert (HasKind Typ_refine_2498
Kind_type))
;;;;;;;;;;;;;;;;i:int{(i >= 0)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_2498)
(and (HasType @x1
Prims.int)
(Valid (Prims.b2t (Prims.op_GreaterThanOrEqual @x1
(BoxInt 0))))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2498)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.nat
Typ_refine_2498))
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
(declare-fun Typ_refine_2500 () Type)
(assert (HasKind Typ_refine_2500
Kind_type))
;;;;;;;;;;;;;;;;i:int{(i > 0)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_2500)
(and (HasType @x1
Prims.int)
(Valid (Prims.b2t (Prims.op_GreaterThan @x1
(BoxInt 0))))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2500)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.pos
Typ_refine_2500))
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
(declare-fun Typ_refine_2502 () Type)
(assert (HasKind Typ_refine_2502
Kind_type))
;;;;;;;;;;;;;;;;i:int{(i <> 0)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_2502)
(and (HasType @x1
Prims.int)
(Valid (Prims.b2t (Prims.op_disEquality Prims.int
@x1
(BoxInt 0))))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2502)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (= Prims.nonzero
Typ_refine_2502))
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

; Internals for module OrdMap

; encoding sigelt OrdMap.total_order

; <Start encoding OrdMap.total_order>
;;;;;;;;;;;;;;;;(a -> a -> Tot bool)
(declare-fun Typ_fun_2509 (Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_2509 kinding
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_fun_2509 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_fun_2509 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (implies (HasType @x1
(Typ_fun_2509 @a2))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_2509 @a2))))))
;;;;;;;;;;;;;;;;Typ_fun_2509 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_fun_2509 @a2))
(forall ((@x3 Term) (@x4 Term))
 (! (implies (and (HasType @x3
@a2)
(HasType @x4
@a2))
(HasType (ApplyEE (ApplyEE @x1
@x3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE @x1
@x3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_2509 @a2))))))
(declare-fun OrdMap.total_order (Type Term) Type)
(declare-fun OrdMap.total_order@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2512
(Type_constr_id OrdMap.total_order@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT OrdMap.total_order@tok
@a0)
@x1)
(OrdMap.total_order @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT OrdMap.total_order@tok
@a0)
@x1)))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_fun_2509 @a0)))
(= (Valid (OrdMap.total_order @a0
@x1))
(and (forall ((@x2 Term) (@x3 Term))
 (implies (and (HasType @x2
@a0)
(HasType @x3
@a0)
(Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x2)
@x3)))
(Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x3)
@x2))))
(Valid (Prims.b2t (Prims.op_Equality @a0
@x2
@x3)))))
(forall ((@x2 Term) (@x3 Term) (@x4 Term))
 (implies (and (HasType @x2
@a0)
(HasType @x3
@a0)
(HasType @x4
@a0)
(Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x2)
@x3)))
(Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x3)
@x4))))
(Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x2)
@x4)))))
(forall ((@x2 Term) (@x3 Term))
 (implies (and (HasType @x2
@a0)
(HasType @x3
@a0))
(or (Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x2)
@x3)))
(Valid (Prims.b2t (ApplyEE (ApplyEE @x1
@x3)
@x2)))))))))
  
:pattern ((Valid (OrdMap.total_order @a0
@x1))))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(Typ_fun_2509 @a0)))
(HasKind (OrdMap.total_order @a0
@x1)
Kind_type))
  
:pattern ((OrdMap.total_order @a0
@x1)))))

; </end encoding OrdMap.total_order>

; encoding sigelt OrdMap.cmp

; <Start encoding OrdMap.cmp>
(declare-fun OrdMap.cmp (Type) Type)
(declare-fun OrdMap.cmp@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2518
(Type_constr_id OrdMap.cmp@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type))
 (! (= (ApplyTT OrdMap.cmp@tok
@a0)
(OrdMap.cmp @a0))
  
:pattern ((ApplyTT OrdMap.cmp@tok
@a0)))))
(declare-fun Typ_refine_2520 (Type) Type)
(assert (forall ((@a0 Type))
 (! (HasKind (Typ_refine_2520 @a0)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2520 @a0)
Kind_type)))))
;;;;;;;;;;;;;;;;f:(a -> a -> Tot bool){(total_order a f)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type))
 (! (iff (HasType @x1
(Typ_refine_2520 @a2))
(and (HasType @x1
(Typ_fun_2509 @a2))
(Valid (OrdMap.total_order @a2
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2520 @a2))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(= (OrdMap.cmp @a0)
(Typ_refine_2520 @a0)))
  
:pattern ((OrdMap.cmp @a0)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type))
 (! (implies (HasKind @a0
Kind_type)
(HasKind (OrdMap.cmp @a0)
Kind_type))
  
:pattern ((OrdMap.cmp @a0)))))

; </end encoding OrdMap.cmp>

; encoding sigelt OrdMap.sorted

; <Start encoding OrdMap.sorted>
(declare-fun OrdMap.sorted (Type Term Term) Term)
;;;;;;;;;;;;;;;;(f:(cmp a) -> (list a) -> Tot bool)
(declare-fun Typ_fun_2523 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2523 kinding
(assert (HasKind Typ_fun_2523
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2523)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2523)))))
;;;;;;;;;;;;;;;;Typ_fun_2523 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2523)
(forall ((@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
(OrdMap.cmp @a2))
(HasType @x4
(Prims.list @a2)))
(HasType (ApplyEE (ApplyEE (ApplyET @x1
@a2)
@x3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x1
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2523)))))
(declare-fun OrdMap.sorted@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2526
(Term_constr_id OrdMap.sorted@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET OrdMap.sorted@tok
@a0)
@x1)
@x2)
(OrdMap.sorted @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET OrdMap.sorted@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.sorted@tok
Typ_fun_2523))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(OrdMap.cmp @a0))
(HasType @x2
(Prims.list @a0)))
(HasType (OrdMap.sorted @a0
@x1
@x2)
Prims.bool))
  
:pattern ((OrdMap.sorted @a0
@x1
@x2)))))

; </end encoding OrdMap.sorted>

; encoding sigelt let OrdMap.sorted : (f:(cmp a) -> (list a) -> Tot bool)

; <Start encoding OrdMap.sorted>
;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun OrdMap.sorted__2545 (Fuel Type Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun OrdMap.sorted__2546 () Term)
;;;;;;;;;;;;;;;;Fuel token correspondence
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyEF OrdMap.sorted__2546
@u0)
@a1)
@x2)
@x3)
(OrdMap.sorted__2545 @u0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyEF OrdMap.sorted__2546
@u0)
@a1)
@x2)
@x3)))))
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a1))
(HasType @x3
(Prims.list @a1)))
(HasType (OrdMap.sorted__2545 @u0
@a1
@x2
@x3)
Prims.bool))
  
:pattern ((OrdMap.sorted__2545 @u0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (OrdMap.sorted @a0
@x1
@x2)
(OrdMap.sorted__2545 MaxFuel
@a0
@x1
@x2))
  
:pattern ((OrdMap.sorted @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Fuel irrelevance
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.sorted__2545 (SFuel @u0)
@a1
@x2
@x3)
(OrdMap.sorted__2545 @u0
@a1
@x2
@x3))
  
:pattern ((OrdMap.sorted__2545 (SFuel @u0)
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Equation for fuel-instrumented recursive function: OrdMap.sorted
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a1))
(HasType @x3
(Prims.list @a1)))
(= (OrdMap.sorted__2545 (SFuel @u0)
@a1
@x2
@x3)
(ite (is-Prims.Nil @x3)
(BoxBool true)
(ite (and (is-Prims.Cons @x3)
(is-Prims.Nil (Prims.Cons_tl @x3)))
(BoxBool true)
(ite (and (is-Prims.Cons @x3)
(is-Prims.Cons (Prims.Cons_tl @x3)))
(Prims.op_AmpAmp (Prims.op_AmpAmp (ApplyEE (ApplyEE @x2
(Prims.Cons_hd @x3))
(Prims.Cons_hd (Prims.Cons_tl @x3)))
(Prims.op_disEquality @a1
(Prims.Cons_hd @x3)
(Prims.Cons_hd (Prims.Cons_tl @x3))))
(OrdMap.sorted__2545 @u0
@a1
@x2
(Prims.Cons @a1
(Prims.Cons_hd (Prims.Cons_tl @x3))
(Prims.Cons_tl (Prims.Cons_tl @x3)))))
Term_unit)))))
  
:pattern ((OrdMap.sorted__2545 (SFuel @u0)
@a1
@x2
@x3)))))

; </end encoding OrdMap.sorted>

; encoding sigelt OrdMap.ordset

; <Start encoding OrdMap.ordset>
(declare-fun OrdMap.ordset (Type Term) Type)
(declare-fun OrdMap.ordset@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2554
(Type_constr_id OrdMap.ordset@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@x1 Term))
 (! (= (ApplyTE (ApplyTT OrdMap.ordset@tok
@a0)
@x1)
(OrdMap.ordset @a0
@x1))
  
:pattern ((ApplyTE (ApplyTT OrdMap.ordset@tok
@a0)
@x1)))))
(declare-fun Typ_refine_2555 (Term Type) Type)
(assert (forall ((@x0 Term) (@a1 Type))
 (! (HasKind (Typ_refine_2555 @x0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2555 @x0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;l:(list a){(sorted f l)}
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@a3 Type))
 (! (iff (HasType @x1
(Typ_refine_2555 @x2
@a3))
(and (HasType @x1
(Prims.list @a3))
(Valid (Prims.b2t (OrdMap.sorted @a3
@x2
@x1)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_refine_2555 @x2
@a3))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(OrdMap.cmp @a0)))
(= (OrdMap.ordset @a0
@x1)
(Typ_refine_2555 @x1
@a0)))
  
:pattern ((OrdMap.ordset @a0
@x1)))))
;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@x1 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
(OrdMap.cmp @a0)))
(HasKind (OrdMap.ordset @a0
@x1)
Kind_type))
  
:pattern ((OrdMap.ordset @a0
@x1)))))

; </end encoding OrdMap.ordset>

; encoding sigelt OrdMap.mem

; <Start encoding OrdMap.mem>
(declare-fun OrdMap.mem (Type Term Term) Term)
;;;;;;;;;;;;;;;;('a -> (list 'a) -> Tot bool)
(declare-fun Typ_fun_2558 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2558 kinding
(assert (HasKind Typ_fun_2558
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2558)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2558)))))
;;;;;;;;;;;;;;;;Typ_fun_2558 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2558)
(forall ((@a2 Type) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasType @x3
@a2)
(HasType @x4
(Prims.list @a2)))
(HasType (ApplyEE (ApplyEE (ApplyET @x1
@a2)
@x3)
@x4)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyET @x1
@a2)
@x3)
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2558)))))
(declare-fun OrdMap.mem@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2561
(Term_constr_id OrdMap.mem@tok)))
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET OrdMap.mem@tok
@a0)
@x1)
@x2)
(OrdMap.mem @a0
@x1
@x2))
  
:pattern ((ApplyEE (ApplyEE (ApplyET OrdMap.mem@tok
@a0)
@x1)
@x2)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.mem@tok
Typ_fun_2558))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasType @x1
@a0)
(HasType @x2
(Prims.list @a0)))
(HasType (OrdMap.mem @a0
@x1
@x2)
Prims.bool))
  
:pattern ((OrdMap.mem @a0
@x1
@x2)))))

; </end encoding OrdMap.mem>

; encoding sigelt let OrdMap.mem : ('a -> (list 'a) -> Tot bool)

; <Start encoding OrdMap.mem>
;;;;;;;;;;;;;;;;Fuel-instrumented function name
(declare-fun OrdMap.mem__2574 (Fuel Type Term Term) Term)
;;;;;;;;;;;;;;;;Token for fuel-instrumented partial applications
(declare-fun OrdMap.mem__2575 () Term)
;;;;;;;;;;;;;;;;Fuel token correspondence
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyEF OrdMap.mem__2575
@u0)
@a1)
@x2)
@x3)
(OrdMap.mem__2574 @u0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyEF OrdMap.mem__2575
@u0)
@a1)
@x2)
@x3)))))
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasType @x2
@a1)
(HasType @x3
(Prims.list @a1)))
(HasType (OrdMap.mem__2574 @u0
@a1
@x2
@x3)
Prims.bool))
  
:pattern ((OrdMap.mem__2574 @u0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Correspondence of recursive function to instrumented version
(assert (forall ((@a0 Type) (@x1 Term) (@x2 Term))
 (! (= (OrdMap.mem @a0
@x1
@x2)
(OrdMap.mem__2574 MaxFuel
@a0
@x1
@x2))
  
:pattern ((OrdMap.mem @a0
@x1
@x2)))))
;;;;;;;;;;;;;;;;Fuel irrelevance
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.mem__2574 (SFuel @u0)
@a1
@x2
@x3)
(OrdMap.mem__2574 @u0
@a1
@x2
@x3))
  
:pattern ((OrdMap.mem__2574 (SFuel @u0)
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Equation for fuel-instrumented recursive function: OrdMap.mem
(assert (forall ((@u0 Fuel) (@a1 Type) (@x2 Term) (@x3 Term))
                (! (implies (and (HasKind @a1
                                          Kind_type)
                                 (HasType @x2
                                          @a1)
                                 (HasType @x3
                                          (Prims.list @a1)))
                            (= (OrdMap.mem__2574 (SFuel @u0)
                                                 @a1
                                                 @x2
                                                 @x3)
                               (ite (is-Prims.Nil @x3)
                                    (BoxBool false)
                                    (ite (is-Prims.Cons @x3)
                                         (ite (= (Prims.op_Equality @a1
                                                                    (Prims.Cons_hd @x3)
                                                                    @x2)
                                                 (BoxBool true))
                                              (BoxBool true)
                                              (ite (= (Prims.op_Equality @a1
                                                                         (Prims.Cons_hd @x3)
                                                                         @x2)
                                                      (BoxBool false))
                                                   (OrdMap.mem__2574 @u0
                                                                     @a1
                                                                     @x2
                                                                     (Prims.Cons_tl @x3))
                                                   Term_unit))
                                         Term_unit))))
                   
                   :pattern ((OrdMap.mem__2574 (SFuel @u0)
                                               @a1
                                               @x2
                                               @x3)))))

; </end encoding OrdMap.mem>

; encoding sigelt OrdMap.map_t

; <Start encoding OrdMap.map_t>
(declare-fun OrdMap.map_t (Type Type Term Term) Type)
(declare-fun OrdMap.map_t@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2588
(Type_constr_id OrdMap.map_t@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT OrdMap.map_t@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.map_t @a0
@a1
@x2
@x3))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT OrdMap.map_t@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;(k -> Tot (option v))
(declare-fun Typ_fun_2590 (Type Type) Type)
;;;;;;;;;;;;;;;;Typ_fun_2590 kinding
(assert (forall ((@a0 Type) (@a1 Type))
 (! (HasKind (Typ_fun_2590 @a0
@a1)
Kind_type)
  
:pattern ((HasKind (Typ_fun_2590 @a0
@a1)
Kind_type)))))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (implies (HasType @x1
(Typ_fun_2590 @a2
@a3))
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_2590 @a2
@a3))))))
;;;;;;;;;;;;;;;;Typ_fun_2590 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type))
 (! (iff (HasType @x1
(Typ_fun_2590 @a2
@a3))
(forall ((@x4 Term))
 (! (implies (HasType @x4
@a3)
(HasType (ApplyEE @x1
@x4)
(Prims.option @a2)))
  
:pattern ((ApplyEE @x1
@x4)))))
  
:pattern ((HasTypeFuel @u0
@x1
(Typ_fun_2590 @a2
@a3))))))
(declare-fun Typ_refine_2593 (Term Type Type) Type)
(assert (forall ((@x0 Term) (@a1 Type) (@a2 Type))
 (! (HasKind (Typ_refine_2593 @x0
@a1
@a2)
Kind_type)
  
:pattern ((HasKind (Typ_refine_2593 @x0
@a1
@a2)
Kind_type)))))
;;;;;;;;;;;;;;;;g:(k -> Tot (option v)){(forall (x). ((mem x d) = (is_Some (g x))))}
(assert (forall ((@u0 Fuel) (@x1 Term) (@x2 Term) (@a3 Type) (@a4 Type))
                (! (iff (HasType @x1
                                 (Typ_refine_2593 @x2
                                                  @a3
                                                  @a4))
                        (and (HasType @x1
                                      (Typ_fun_2590 @a4
                                                    @a3))
                             (forall ((@x5 Term))
                                     (implies (HasType @x5
                                                       @a3)
                                              (Valid (Prims.b2t (Prims.op_Equality Prims.bool
                                                                                   (OrdMap.mem @a3
                                                                                               @x5
                                                                                               @x2)
                                                                                   (Prims.is_Some @a4
                                                                                                  (ApplyEE @x1
                                                                                                           @x5)))))))))
                   
                   :pattern ((HasTypeFuel @u0
                                          @x1
                                          (Typ_refine_2593 @x2
                                                           @a3
                                                           @a4))))))
;;;;;;;;;;;;;;;;abbrev. elimination
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
                (! (implies (and (HasKind @a0
                                          Kind_type)
                                 (HasKind @a1
                                          Kind_type)
                                 (HasType @x2
                                          (OrdMap.cmp @a0))
                                 (HasType @x3
                                          (OrdMap.ordset @a0
                                                         @x2)))
                            (= (OrdMap.map_t @a0
                                             @a1
                                             @x2
                                             @x3)
                               (Typ_refine_2593 @x3
                                                @a0
                                                @a1)))
                   
                   :pattern ((OrdMap.map_t @a0
                                           @a1
                                           @x2
                                           @x3)))))

;;;;;;;;;;;;;;;;abbrev. kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordset @a0
@x2)))
(HasKind (OrdMap.map_t @a0
@a1
@x2
@x3)
Kind_type))
  
:pattern ((OrdMap.map_t @a0
@a1
@x2
@x3)))))

; </end encoding OrdMap.map_t>

; encoding sigelt OrdMap.ordmap, OrdMap.Mk_map

; <Start encoding >
;;;;;;;;;;;;;;;;Constructor
(declare-fun OrdMap.ordmap (Type Type Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.ordmap@a0 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.ordmap@a1 (Type) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.ordmap@x2 (Type) Term)
;;;;;;;;;;;;;;;;token
(declare-fun OrdMap.ordmap@tok () Type)
;;;;;;;;;;;;;;;;Constructor
(declare-fun OrdMap.Mk_map (Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.Mk_map_k (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.Mk_map_v (Term) Type)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.Mk_map_f (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.Mk_map_d (Term) Term)
;;;;;;;;;;;;;;;;Projector
(declare-fun OrdMap.Mk_map_m (Term) Term)
;;;;;;;;;;;;;;;;(d:(ordset k f) -> m:(map_t k v f d) -> Tot (ordmap k v f))
(declare-fun Typ_fun_2615 () Type)
;;;;;;;;;;;;;;;;data constructor proxy: Mk_map
(declare-fun OrdMap.Mk_map@tok () Term)

; <Start encoding OrdMap.ordmap>

; <start constructor OrdMap.ordmap>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (= 2606
(Type_constr_id (OrdMap.ordmap @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (OrdMap.ordmap@a0 (OrdMap.ordmap @a0
@a1
@x2))
@a0)
  
:pattern ((OrdMap.ordmap @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (OrdMap.ordmap@a1 (OrdMap.ordmap @a0
@a1
@x2))
@a1)
  
:pattern ((OrdMap.ordmap @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (OrdMap.ordmap@x2 (OrdMap.ordmap @a0
@a1
@x2))
@x2)
  
:pattern ((OrdMap.ordmap @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-OrdMap.ordmap ((@a0 Type)) Bool
 (and (= (Type_constr_id @a0)
2606)
(= @a0
(OrdMap.ordmap (OrdMap.ordmap@a0 @a0)
(OrdMap.ordmap@a1 @a0)
(OrdMap.ordmap@x2 @a0)))))

; </end constructor OrdMap.ordmap>
;;;;;;;;;;;;;;;;fresh token
(assert (= 2607
(Type_constr_id OrdMap.ordmap@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (= (ApplyTE (ApplyTT (ApplyTT OrdMap.ordmap@tok
@a0)
@a1)
@x2)
(OrdMap.ordmap @a0
@a1
@x2))
  
:pattern ((ApplyTE (ApplyTT (ApplyTT OrdMap.ordmap@tok
@a0)
@a1)
@x2)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind OrdMap.ordmap@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0)))
(HasKind (OrdMap.ordmap @a0
@a1
@x2)
Kind_type))
  
:pattern ((OrdMap.ordmap @a0
@a1
@x2)))))
;;;;;;;;;;;;;;;;pretyping
(assert (forall ((@x0 Term) (@u1 Fuel) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (HasTypeFuel @u1
@x0
(OrdMap.ordmap @a2
@a3
@x4))
(= (OrdMap.ordmap @a2
@a3
@x4)
(PreType @x0)))
  
:pattern ((HasTypeFuel @u1
@x0
(OrdMap.ordmap @a2
@a3
@x4))))))

; </end encoding OrdMap.ordmap>

; <Start encoding OrdMap.Mk_map>

; <start constructor OrdMap.Mk_map>
;;;;;;;;;;;;;;;;Constructor distinct
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (= 2613
(Term_constr_id (OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (OrdMap.Mk_map_k (OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4))
@a0)
  
:pattern ((OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (OrdMap.Mk_map_v (OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4))
@a1)
  
:pattern ((OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (OrdMap.Mk_map_f (OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4))
@x2)
  
:pattern ((OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (OrdMap.Mk_map_d (OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4))
@x3)
  
:pattern ((OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4)))))
;;;;;;;;;;;;;;;;Projection inverse
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (OrdMap.Mk_map_m (OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4))
@x4)
  
:pattern ((OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4)))))
;;;;;;;;;;;;;;;;Discriminator definition
(define-fun is-OrdMap.Mk_map ((@x0 Term)) Bool
 (and (= (Term_constr_id @x0)
2613)
(= @x0
(OrdMap.Mk_map (OrdMap.Mk_map_k @x0)
(OrdMap.Mk_map_v @x0)
(OrdMap.Mk_map_f @x0)
(OrdMap.Mk_map_d @x0)
(OrdMap.Mk_map_m @x0)))))

; </end constructor OrdMap.Mk_map>
;;;;;;;;;;;;;;;;Typ_fun_2615 kinding
(assert (HasKind Typ_fun_2615
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2615)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2615)))))
;;;;;;;;;;;;;;;;Typ_fun_2615 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2615)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
(OrdMap.ordset @a2
@x4))
(HasType @x6
(OrdMap.map_t @a2
@a3
@x4
@x5)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
@x6)
(OrdMap.ordmap @a2
@a3
@x4)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2615)))))
;;;;;;;;;;;;;;;;fresh token
(assert (= 2618
(Term_constr_id OrdMap.Mk_map@tok)))
;;;;;;;;;;;;;;;;typing for data constructor proxy
(assert (HasType OrdMap.Mk_map@tok
Typ_fun_2615))
;;;;;;;;;;;;;;;;equality for proxy
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map@tok
@a0)
@a1)
@x2)
@x3)
@x4)
(OrdMap.Mk_map @a0
@a1
@x2
@x3
@x4))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map@tok
@a0)
@a1)
@x2)
@x3)
@x4)))))
;;;;;;;;;;;;;;;;data constructor typing intro
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
(OrdMap.cmp @a1))
(HasTypeFuel @u0
@x4
(OrdMap.ordset @a1
@x3))
(HasTypeFuel @u0
@x5
(OrdMap.map_t @a1
@a2
@x3
@x4)))
(HasTypeFuel @u0
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)
(OrdMap.ordmap @a1
@a2
@x3)))
  
:pattern ((HasTypeFuel @u0
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)
(OrdMap.ordmap @a1
@a2
@x3))))))
;;;;;;;;;;;;;;;;data constructor typing elim
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)
(OrdMap.ordmap @a6
@a7
@x8))
(and (= @x3
@x8)
(= @a2
@a7)
(= @a1
@a6)
(HasKind @a1
Kind_type)
(HasKind @a2
Kind_type)
(HasTypeFuel @u0
@x3
(OrdMap.cmp @a1))
(HasTypeFuel @u0
@x4
(OrdMap.ordset @a1
@x3))
(HasTypeFuel @u0
@x5
(OrdMap.map_t @a1
@a2
@x3
@x4))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)
(OrdMap.ordmap @a6
@a7
@x8))))))
;;;;;;;;;;;;;;;;subterm ordering
(assert (forall ((@u0 Fuel) (@a1 Type) (@a2 Type) (@x3 Term) (@x4 Term) (@x5 Term) (@a6 Type) (@a7 Type) (@x8 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)
(OrdMap.ordmap @a6
@a7
@x8))
(and (Valid (Precedes @x3
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)))
(Valid (Precedes @x4
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)))
(Valid (Precedes @x5
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)))))
  
:pattern ((HasTypeFuel (SFuel @u0)
(OrdMap.Mk_map @a1
@a2
@x3
@x4
@x5)
(OrdMap.ordmap @a6
@a7
@x8))))))

; </end encoding OrdMap.Mk_map>
;;;;;;;;;;;;;;;;inversion axiom
(assert (forall ((@u0 Fuel) (@x1 Term) (@a2 Type) (@a3 Type) (@x4 Term))
 (! (implies (HasTypeFuel (SFuel @u0)
@x1
(OrdMap.ordmap @a2
@a3
@x4))
(and (is-OrdMap.Mk_map @x1)
(= @a2
(OrdMap.Mk_map_k @x1))
(= @a3
(OrdMap.Mk_map_v @x1))
(= @x4
(OrdMap.Mk_map_f @x1))))
  
:pattern ((HasTypeFuel (SFuel @u0)
@x1
(OrdMap.ordmap @a2
@a3
@x4))))))

; </end encoding >

; encoding sigelt OrdMap.is_Mk_map

; <Start encoding OrdMap.is_Mk_map>
(declare-fun OrdMap.is_Mk_map (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;((ordmap key value _2) -> Tot bool)
(declare-fun Typ_fun_2620 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2620 kinding
(assert (HasKind Typ_fun_2620
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2620)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2620)))))
;;;;;;;;;;;;;;;;Typ_fun_2620 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2620)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
(OrdMap.ordmap @a2
@a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2620)))))
(declare-fun OrdMap.is_Mk_map@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2623
(Term_constr_id OrdMap.is_Mk_map@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.is_Mk_map@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.is_Mk_map @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.is_Mk_map@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.is_Mk_map@tok
Typ_fun_2620))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.is_Mk_map @a0
@a1
@x2
@x3)
Prims.bool))
  
:pattern ((OrdMap.is_Mk_map @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Discriminator equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.is_Mk_map @a0
@a1
@x2
@x3)
(BoxBool (is-OrdMap.Mk_map @x3)))
  
:pattern ((OrdMap.is_Mk_map @a0
@a1
@x2
@x3)))))

; </end encoding OrdMap.is_Mk_map>

; encoding sigelt OrdMap.Mk_map.k

; <Start encoding OrdMap.Mk_map.k>
(declare-fun OrdMap.Mk_map.k (Type Type Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun OrdMap.Mk_map.k@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2625
(Type_constr_id OrdMap.Mk_map.k@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT OrdMap.Mk_map.k@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.Mk_map.k @a0
@a1
@x2
@x3))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT OrdMap.Mk_map.k@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind OrdMap.Mk_map.k@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasKind (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
Kind_type))
  
:pattern ((OrdMap.Mk_map.k @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map_k @x3))
  
:pattern ((OrdMap.Mk_map.k @a0
@a1
@x2
@x3)))))

; </end encoding OrdMap.Mk_map.k>

; encoding sigelt OrdMap.Mk_map.v

; <Start encoding OrdMap.Mk_map.v>
(declare-fun OrdMap.Mk_map.v (Type Type Term Term) Type)
;;;;;;;;;;;;;;;;token
(declare-fun OrdMap.Mk_map.v@tok () Type)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2627
(Type_constr_id OrdMap.Mk_map.v@tok)))
;;;;;;;;;;;;;;;;name-token correspondence
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyTE (ApplyTE (ApplyTT (ApplyTT OrdMap.Mk_map.v@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.Mk_map.v @a0
@a1
@x2
@x3))
  
:pattern ((ApplyTE (ApplyTE (ApplyTT (ApplyTT OrdMap.Mk_map.v@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;kinding
(assert (is-Kind_arrow (PreKind OrdMap.Mk_map.v@tok)))
;;;;;;;;;;;;;;;;kinding
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasKind (OrdMap.Mk_map.v @a0
@a1
@x2
@x3)
Kind_type))
  
:pattern ((OrdMap.Mk_map.v @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;projector axiom
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.Mk_map.v @a0
@a1
@x2
@x3)
(OrdMap.Mk_map_v @x3))
  
:pattern ((OrdMap.Mk_map.v @a0
@a1
@x2
@x3)))))

; </end encoding OrdMap.Mk_map.v>

; encoding sigelt OrdMap.Mk_map.f

; <Start encoding OrdMap.Mk_map.f>
(declare-fun OrdMap.Mk_map.f (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;(projectee:(ordmap key value _2) -> Tot (cmp (k projectee)))
(declare-fun Typ_fun_2629 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2629 kinding
(assert (HasKind Typ_fun_2629
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2629)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2629)))))
;;;;;;;;;;;;;;;;Typ_fun_2629 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2629)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
(OrdMap.ordmap @a2
@a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
(OrdMap.cmp (OrdMap.Mk_map.k @a2
@a3
@x4
@x5))))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2629)))))
(declare-fun OrdMap.Mk_map.f@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2632
(Term_constr_id OrdMap.Mk_map.f@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map.f@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map.f@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.Mk_map.f@tok
Typ_fun_2629))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.Mk_map.f @a0
@a1
@x2
@x3)
(OrdMap.cmp (OrdMap.Mk_map.k @a0
@a1
@x2
@x3))))
  
:pattern ((OrdMap.Mk_map.f @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.Mk_map.f @a0
@a1
@x2
@x3)
(OrdMap.Mk_map_f @x3))
  
:pattern ((OrdMap.Mk_map.f @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.Mk_map_f @x3)
(OrdMap.cmp (OrdMap.Mk_map.k @a0
@a1
@x2
@x3))))
  
:pattern ((HasType (OrdMap.Mk_map_f @x3)
(OrdMap.cmp (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)))))))

; </end encoding OrdMap.Mk_map.f>

; encoding sigelt let OrdMap.Mk_map.f : (projectee:(ordmap key value _2) -> Tot (cmp (k projectee)))

; <Skipped />

; encoding sigelt OrdMap.Mk_map.d

; <Start encoding OrdMap.Mk_map.d>
(declare-fun OrdMap.Mk_map.d (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;(projectee:(ordmap key value _2) -> Tot (ordset (k projectee) (f projectee)))
(declare-fun Typ_fun_2652 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2652 kinding
(assert (HasKind Typ_fun_2652
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2652)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2652)))))
;;;;;;;;;;;;;;;;Typ_fun_2652 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2652)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
(OrdMap.ordmap @a2
@a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
(OrdMap.ordset (OrdMap.Mk_map.k @a2
@a3
@x4
@x5)
(OrdMap.Mk_map.f @a2
@a3
@x4
@x5))))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2652)))))
(declare-fun OrdMap.Mk_map.d@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2655
(Term_constr_id OrdMap.Mk_map.d@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map.d@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.Mk_map.d @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map.d@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.Mk_map.d@tok
Typ_fun_2652))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.Mk_map.d @a0
@a1
@x2
@x3)
(OrdMap.ordset (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3))))
  
:pattern ((OrdMap.Mk_map.d @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.Mk_map.d @a0
@a1
@x2
@x3)
(OrdMap.Mk_map_d @x3))
  
:pattern ((OrdMap.Mk_map.d @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.Mk_map_d @x3)
(OrdMap.ordset (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3))))
  
:pattern ((HasType (OrdMap.Mk_map_d @x3)
(OrdMap.ordset (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3)))))))

; </end encoding OrdMap.Mk_map.d>

; encoding sigelt let OrdMap.Mk_map.d : (projectee:(ordmap key value _2) -> Tot (ordset (k projectee) (f projectee)))

; <Skipped />

; encoding sigelt OrdMap.Mk_map.m

; <Start encoding OrdMap.Mk_map.m>
(declare-fun OrdMap.Mk_map.m (Type Type Term Term) Term)
;;;;;;;;;;;;;;;;(projectee:(ordmap key value _2) -> Tot (map_t (k projectee) (v projectee) (f projectee) (d projectee)))
(declare-fun Typ_fun_2672 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2672 kinding
(assert (HasKind Typ_fun_2672
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2672)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2672)))))
;;;;;;;;;;;;;;;;Typ_fun_2672 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2672)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
(OrdMap.ordmap @a2
@a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
(OrdMap.map_t (OrdMap.Mk_map.k @a2
@a3
@x4
@x5)
(OrdMap.Mk_map.v @a2
@a3
@x4
@x5)
(OrdMap.Mk_map.f @a2
@a3
@x4
@x5)
(OrdMap.Mk_map.d @a2
@a3
@x4
@x5))))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2672)))))
(declare-fun OrdMap.Mk_map.m@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2675
(Term_constr_id OrdMap.Mk_map.m@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map.m@tok
@a0)
@a1)
@x2)
@x3)
(OrdMap.Mk_map.m @a0
@a1
@x2
@x3))
  
:pattern ((ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.Mk_map.m@tok
@a0)
@a1)
@x2)
@x3)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.Mk_map.m@tok
Typ_fun_2672))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.Mk_map.m @a0
@a1
@x2
@x3)
(OrdMap.map_t (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.v @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.d @a0
@a1
@x2
@x3))))
  
:pattern ((OrdMap.Mk_map.m @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Projector equation
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (= (OrdMap.Mk_map.m @a0
@a1
@x2
@x3)
(OrdMap.Mk_map_m @x3))
  
:pattern ((OrdMap.Mk_map.m @a0
@a1
@x2
@x3)))))
;;;;;;;;;;;;;;;;Primitive projector typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.Mk_map_m @x3)
(OrdMap.map_t (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.v @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.d @a0
@a1
@x2
@x3))))
  
:pattern ((HasType (OrdMap.Mk_map_m @x3)
(OrdMap.map_t (OrdMap.Mk_map.k @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.v @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.f @a0
@a1
@x2
@x3)
(OrdMap.Mk_map.d @a0
@a1
@x2
@x3)))))))

; </end encoding OrdMap.Mk_map.m>

; encoding sigelt let OrdMap.Mk_map.m : (projectee:(ordmap key value _2) -> Tot (map_t (k projectee) (v projectee) (f projectee) (d projectee)))

; <Skipped />

; encoding sigelt OrdMap.select

; <Start encoding OrdMap.select>
(declare-fun OrdMap.select (Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;(k:key -> m:(ordmap key value f) -> Tot (option value))
(declare-fun Typ_fun_2693 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2693 kinding
(assert (HasKind Typ_fun_2693
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2693)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2693)))))
;;;;;;;;;;;;;;;;Typ_fun_2693 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2693)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
@a2)
(HasType @x6
(OrdMap.ordmap @a2
@a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
@x6)
(Prims.option @a3)))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2693)))))
(declare-fun OrdMap.select@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2696
(Term_constr_id OrdMap.select@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.select@tok
@a0)
@a1)
@x2)
@x3)
@x4)
(OrdMap.select @a0
@a1
@x2
@x3
@x4))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.select@tok
@a0)
@a1)
@x2)
@x3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.select@tok
Typ_fun_2693))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
@a0)
(HasType @x4
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.select @a0
@a1
@x2
@x3
@x4)
(Prims.option @a1)))
  
:pattern ((OrdMap.select @a0
@a1
@x2
@x3
@x4)))))

; </end encoding OrdMap.select>

; encoding sigelt let OrdMap.select : (k:key -> m:(ordmap key value f) -> Tot (option value))

; <Start encoding OrdMap.select>
;;;;;;;;;;;;;;;;Equation for OrdMap.select
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
                (! (implies (and (HasKind @a0
                                          Kind_type)
                                 (HasKind @a1
                                          Kind_type)
                                 (HasType @x2
                                          (OrdMap.cmp @a0))
                                 (HasType @x3
                                          @a0)
                                 (HasType @x4
                                          (OrdMap.ordmap @a0
                                                         @a1
                                                         @x2)))
                            (= (OrdMap.select @a0
                                              @a1
                                              @x2
                                              @x3
                                              @x4)
                               (ite (is-OrdMap.Mk_map @x4)
                                    (ApplyEE (OrdMap.Mk_map_m @x4)
                                             @x3)
                                    Term_unit)))
                   
                   :pattern ((OrdMap.select @a0
                                            @a1
                                            @x2
                                            @x3
                                            @x4)))))

; </end encoding OrdMap.select>

; encoding sigelt OrdMap.contains

; <Start encoding OrdMap.contains>
(declare-fun OrdMap.contains (Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;(key -> (ordmap key value f) -> Tot bool)
(declare-fun Typ_fun_2714 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2714 kinding
(assert (HasKind Typ_fun_2714
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2714)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2714)))))
;;;;;;;;;;;;;;;;Typ_fun_2714 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2714)
(forall ((@a2 Type) (@a3 Type) (@x4 Term) (@x5 Term) (@x6 Term))
 (! (implies (and (HasKind @a2
Kind_type)
(HasKind @a3
Kind_type)
(HasType @x4
(OrdMap.cmp @a2))
(HasType @x5
@a2)
(HasType @x6
(OrdMap.ordmap @a2
@a3
@x4)))
(HasType (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
@x6)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET @x1
@a2)
@a3)
@x4)
@x5)
@x6)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2714)))))
(declare-fun OrdMap.contains@tok () Term)
;;;;;;;;;;;;;;;;fresh token
(assert (= 2717
(Term_constr_id OrdMap.contains@tok)))
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (= (ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.contains@tok
@a0)
@a1)
@x2)
@x3)
@x4)
(OrdMap.contains @a0
@a1
@x2
@x3
@x4))
  
:pattern ((ApplyEE (ApplyEE (ApplyEE (ApplyET (ApplyET OrdMap.contains@tok
@a0)
@a1)
@x2)
@x3)
@x4)))))
;;;;;;;;;;;;;;;;function token typing
(assert (HasType OrdMap.contains@tok
Typ_fun_2714))
;;;;;;;;;;;;;;;;free var typing
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
 (! (implies (and (HasKind @a0
Kind_type)
(HasKind @a1
Kind_type)
(HasType @x2
(OrdMap.cmp @a0))
(HasType @x3
@a0)
(HasType @x4
(OrdMap.ordmap @a0
@a1
@x2)))
(HasType (OrdMap.contains @a0
@a1
@x2
@x3
@x4)
Prims.bool))
  
:pattern ((OrdMap.contains @a0
@a1
@x2
@x3
@x4)))))

; </end encoding OrdMap.contains>

; encoding sigelt let OrdMap.contains : (key -> (ordmap key value f) -> Tot bool)

; <Start encoding OrdMap.contains>
;;;;;;;;;;;;;;;;Equation for OrdMap.contains
(assert (forall ((@a0 Type) (@a1 Type) (@x2 Term) (@x3 Term) (@x4 Term))
                (! (implies (and (HasKind @a0
                                          Kind_type)
                                 (HasKind @a1
                                          Kind_type)
                                 (HasType @x2
                                          (OrdMap.cmp @a0))
                                 (HasType @x3
                                          @a0)
                                 (HasType @x4
                                          (OrdMap.ordmap @a0
                                                         @a1
                                                         @x2)))
                            (= (OrdMap.contains @a0
                                                @a1
                                                @x2
                                                @x3
                                                @x4)
                               (ite (is-OrdMap.Mk_map @x4)
                                    (OrdMap.mem @a0
                                                @x3
                                                (OrdMap.Mk_map_d @x4))
                                    Term_unit)))
                   
                   :pattern ((OrdMap.contains @a0
                                              @a1
                                              @x2
                                              @x3
                                              @x4)))))

; </end encoding OrdMap.contains>

; encoding sigelt OrdMap.sel_contains

; <Start encoding OrdMap.sel_contains>
;;;;;;;;;;;;;;;;Uninterpreted function symbol for impure function
(declare-fun OrdMap.sel_contains (Type Type Term Term Term) Term)
;;;;;;;;;;;;;;;;Uninterpreted name for impure function
(declare-fun OrdMap.sel_contains@tok () Term)

; </end encoding OrdMap.sel_contains>

; encoding sigelt 

; <Skipped />
(push)

; Starting query at FStar.OrdMap.fst(43,0-44,0)
;;;;;;;;;;;;;;;;k
(declare-fun k___1_93 () Type)
(assert (HasKind k___1_93
Kind_type))
;;;;;;;;;;;;;;;;v
(declare-fun v___1_94 () Type)
(assert (HasKind v___1_94
Kind_type))
;;;;;;;;;;;;;;;;f : (cmp k) (f:(k -> k -> Tot bool){(total_order k f)})
(declare-fun f___1_95 () Term)
;;;;;;;;;;;;;;;;(k -> k -> Tot bool)
(declare-fun Typ_fun_2736 () Type)
;;;;;;;;;;;;;;;;Typ_fun_2736 kinding
(assert (HasKind Typ_fun_2736
Kind_type))
;;;;;;;;;;;;;;;;pre-typing for functions
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (implies (HasType @x1
Typ_fun_2736)
(is-Typ_fun (PreType @x1)))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2736)))))
;;;;;;;;;;;;;;;;Typ_fun_2736 interpretation
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_fun_2736)
(forall ((@x2 Term) (@x3 Term))
 (! (implies (and (HasType @x2
k___1_93)
(HasType @x3
k___1_93))
(HasType (ApplyEE (ApplyEE @x1
@x2)
@x3)
Prims.bool))
  
:pattern ((ApplyEE (ApplyEE @x1
@x2)
@x3)))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_fun_2736)))))
(declare-fun Typ_refine_2739 () Type)
(assert (HasKind Typ_refine_2739
Kind_type))
;;;;;;;;;;;;;;;;f:(k -> k -> Tot bool){(total_order k f)}
(assert (forall ((@u0 Fuel) (@x1 Term))
 (! (iff (HasType @x1
Typ_refine_2739)
(and (HasType @x1
Typ_fun_2736)
(Valid (OrdMap.total_order k___1_93
@x1))))
  
:pattern ((HasTypeFuel @u0
@x1
Typ_refine_2739)))))
(assert (HasType f___1_95
Typ_refine_2739))
;;;;;;;;;;;;;;;;x : k (k)
(declare-fun x___1_96 () Term)
(assert (HasType x___1_96
k___1_93))
;;;;;;;;;;;;;;;;m : (ordmap k v f) ((ordmap k v f))
(declare-fun m___1_97 () Term)
(assert (HasType m___1_97
(OrdMap.ordmap k___1_93
v___1_94
f___1_95)))
(declare-fun label_2743 () Bool)
;;;;;;;;;;;;;;;;(unit -> Type)
(declare-fun Kind_arrow_2742 () Kind)
;;;;;;;;;;;;;;;;Kind_arrow_2742 interpretation
(assert (forall ((@a0 Type))
 (! (iff (HasKind @a0
Kind_arrow_2742)
(and (is-Kind_arrow (PreKind @a0))
(forall ((@x1 Term))
 (! (implies (HasType @x1
Prims.unit)
(HasKind (ApplyTE @a0
@x1)
Kind_type))
  
:pattern ((ApplyTE @a0
@x1))))))
  
:pattern ((HasKind @a0
Kind_arrow_2742)))))
(push)

; <fuel='2'>
(assert (= MaxFuel
(SFuel (SFuel ZFuel))))
(assert (= MaxIFuel
(SFuel ZFuel)))


; No Fuel irrelevance
;; (assert (forall ((f Fuel) (e Term) (t Type))
;;                 (! (= (HasTypeFuel (SFuel f) e t)
;;                       (HasTypeFuel f e t))
;;                       :pattern ((HasTypeFuel (SFuel f) e t)))))

;;;;;;;;;;;;;;;; original query after simplification and unfolding -- does not work
;; (assert (not (=
;;               ;; (OrdMap.contains k___1_93
;;               ;;                  v___1_94
;;               ;;                  f___1_95
;;               ;;                  x___1_96
;;               ;;                  m___1_97)
;;               (OrdMap.mem__2574 MaxFuel k___1_93
;;                           x___1_96
;;                           (OrdMap.Mk_map_d m___1_97))
;;               (Prims.is_Some v___1_94
;;                              ;; (OrdMap.select k___1_93
;;                              ;;                v___1_94
;;                              ;;                f___1_95
;;                              ;;                x___1_96
;;                              ;;                m___1_97)
;;                              (ApplyEE (OrdMap.Mk_map_m m___1_97) x___1_96)
;;                              ))))

;; new query -- does not work, but surprisingly for -old either!
(assert (not (HasType (OrdMap.Mk_map_m m___1_97)
                 (Typ_refine_2593 (OrdMap.Mk_map_d m___1_97)
                                  v___1_94 k___1_93))))

(check-sat)
(echo "label_2743")
(eval label_2743)
(echo "Done!")
(pop)
(push)
