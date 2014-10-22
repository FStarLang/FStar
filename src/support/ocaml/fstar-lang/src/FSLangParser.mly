(* -------------------------------------------------------------------- *)
%{
  module Ast = FSLangAst

  let range = Ast.range
  let desc  = Ast.desc
  let mk_rg = Ast.mk_rg
%}

(* -------------------------------------------------------------------- *)
%token <Fstar.Types.bytes> BYTEARRAY
%token <Fstar.Types.bytes> STRING

%token <string> IDENT
%token <string> NAME
%token <string> TVAR
%token <string> DIV_MOD_OP
%token <string> PLUS_MINUS_OP
%token <string> TILDE
%token <string> BANG

%token <Fstar.Types.int32 * bool> INT32
%token <Fstar.Types.int64 * bool> INT64

%token <Fstar.Types.byte   > UINT8
%token <Fstar.Types.double > IEEE64

%token <char> CHAR

%token AMP_AMP
%token AND
%token ASSERT
%token ASSUME
%token ATSIGN
%token BAR
%token BAR_BAR
%token BAR_RBRACK
%token BEGIN
%token COLON
%token COLON_COLON
%token COLON_EQUALS
%token COMMA
%token CONJUNCTION
%token DEFINE
%token DISJUNCTION
%token DOT
%token EFFECT
%token ELSE
%token END
%token EOF
%token EQUALS
%token EQUALS_BANG_EQUALS
%token EQUALS_EQUALS
%token EXCEPTION
%token EXISTS
%token FALSE
%token FORALL
%token FUN
%token FUNCTION
%token GEQ
%token GREATER
%token HASH
%token HAT
%token IF
%token IFF
%token IMPLIES
%token IN
%token KIND
%token LBRACE
%token LBRACE_COLON_PTN
%token LBRACK
%token LBRACK_BAR
%token LENS_PAREN_LEFT
%token LENS_PAREN_RIGHT
%token LEQ
%token LESS
%token LESSGREATER
%token LET
%token LOGIC
%token LPAREN
%token LPAREN_RPAREN
%token MATCH
%token MODULE
%token MONADLATTICE
%token OF
%token OPEN
%token PIPE_LEFT
%token PIPE_RIGHT
%token PRAGMALIGHT
%token PRAGMAMONADIC
%token PRINT
%token QUERY
%token RARROW
%token RBRACE
%token RBRACK
%token REC
%token RPAREN
%token RRARROW
%token SEMICOLON
%token SEMICOLON_SEMICOLON
%token SQUIGGLY_RARROW
%token STAR
%token SUBKIND
%token SUBTYPE
%token THEN
%token TOTAL
%token TRUE
%token TRY
%token TYP_APP_LESS
%token TYPE
%token UNDERSCORE
%token VAL
%token WHEN
%token WITH

%nonassoc THEN
%nonassoc ELSE

%start file
%type <unit> file

%%

(* ==================================================================== *)
ident: x=loc(IDENT) { Ast.mk_ident x }
name : x=loc(NAME)  { Ast.mk_ident x }
tvar : x=loc(TVAR)  { Ast.mk_ident x }


eitherQname:
| nm=rlist0(suffix(name, DOT), empty) name=eitherName
    { nm@[name] }

lid:
| idpath
{};

qname:
| namepath
{};

eitherName:
| ident
| name
{};

namepath:
| name
| name DOT namepath
{};

idpath:
| ident
| name DOT idpath
{};


(* ==================================================================== *)
file:
| pg=pragmas ms=modul+ EOF
    { ignore (pg, ms) }

(* -------------------------------------------------------------------- *)
modul:
| MODULE name=qname decls=decls END?
    { Ast.mk_module (name, decls) }

(* -------------------------------------------------------------------- *)
pragma:
| PRAGMAMONADIC LPAREN
    x1=eitherQname COMMA
    x2=eitherQname COMMA
    x3=eitherQname
  RPAREN
    { [Ast.mk_monadic (x1, x2, x3)] }

| PRAGMALIGHT STRING
    { [] }

(* -------------------------------------------------------------------- *)
%inline pragmas:
| pgs=pragma* { List.flatten pgs }

(* -------------------------------------------------------------------- *)
decls:
| (* empty *)
    { [] }

| SEMICOLON_SEMICOLON t=term
    { [Ast.mk_decl ~rg:(mk_rg $startpos $endpos) t] }

| d=decl ds=decls
    { d :: ds }

(* -------------------------------------------------------------------- *)
decl:
| OPEN name=qname
    { Ast.mk_open name }

| ka=kind_abbrev
    { ka }

| tyc=tycon
    { tyc }

| LET rec_=REC? bds=plist1(letbinding, AND)
    { Ast.mk_top_let (rec_, bds) }

| ql=qualifiers VAL name=eitherName COLON ty=typ
    { Ast.mk_val (ql, name, ty) }

| tg=assumeTag name=name COLON f=formula
   { Ast.mk_assume (tg, name, f) }

| EXCEPTION name=name ty=prefix(OF, typ)?
   { Ast.mk_exception (name, ty) }

| MONADLATTICE LBRACE
    mds=plist1(monad, SEMICOLON)
    lifts=prefix(WITH, plist1(lift, SEMICOLON))?
  RBRACE
    { Ast.mk_monadlat (mds, lifts) }

(* -------------------------------------------------------------------- *)
tycon:
| ql=qualifiers TYPE defs=plist1(tyconDefinition, AND)
    { Ast.mk_tycon (ql, defs) }

| EFFECT def=tyconDefinition 
	  { Ast.mk_tycon ([`Effect], [def]) }

(* -------------------------------------------------------------------- *)
kind_abbrev:
| KIND name=name bds=binder* EQUALS kd=kind
    { Ast.mk_kind_abbrv (name, bds, kd) }

(* -------------------------------------------------------------------- *)
monad:
| name=name COLON_COLON t=TOTAL? dcls=monad_decl* WITH abbrvs=plist1(monad_abbrev, AND)
    { Ast.mk_monad (name, t, dcls, abbrvs) }

(* -------------------------------------------------------------------- *)
monad_decl:
| x=loc(kind_abbrev)
    { Ast.mk_decl ~rg:(range x) (desc x) }

| x=loc(tycon)
    { Ast.mk_decl ~rg:(range x) (desc x) }

(* -------------------------------------------------------------------- *)
monad_abbrev:
| name=name tvs=typars EQUALS ty=typ
    { Ast.mk_monad_abbrv (name, tvs, ty) }

(* -------------------------------------------------------------------- *)
lift:
| src=name SQUIGGLY_RARROW dst=name EQUALS t=atomicTerm
    { Ast.mk_lift (src, dst, t) }

(* -------------------------------------------------------------------- *)
qualifiers:
| empty        { [] } 
| LOGIC        { [`Logic] }
| ASSUME       { [`Assume] }
| ASSUME LOGIC { [`Assume; `Logic] }

(* -------------------------------------------------------------------- *)
assumeTag:
| ASSUME { [`Assumption] }
| QUERY  { [`Query] }
| DEFINE { [`Definition] }

(* -------------------------------------------------------------------- *)
tyconDefinition:
| name=eitherName tvs=typars asc=prefix(COLON, kind)? tyc=tyconDefn
    { tyc (name, tvs, asc) }

(* -------------------------------------------------------------------- *)
letbinding:
| pt=pattern asc=prefix(COLON, product)? EQUALS e=term
    { let pt =
        match asc with
        | None     -> pt
        | Some asc ->
            let rg = mk_rg $startpos(pt) $endpos(asc) in
              Ast.mk_pattern ~rg (Ast.mk_pat_ascribed (pt, asc))
      in (pt, e) }

(* -------------------------------------------------------------------- *)
pattern:
| pt=tuplePattern { pt }

(* -------------------------------------------------------------------- *)
tuplePattern:
| pts=loc(plist1(listPattern, COMMA))
    { match desc pts with
      | []   -> assert false
      | [pt] -> pt
      | _    ->
         let pt = Ast.mk_pat_tuple (desc pts, false) in
         Ast.mk_pattern ~rg:(range pts) pt }

(* -------------------------------------------------------------------- *)
listPattern:
| pta=appPattern ptc=loc(consPattern?)
    { match desc ptc with 
      | None     -> pta
      | Some ptc ->
          let pt = Ast.mk_pat_cons (pta, ptc) in
          Ast.mk_pattern ~rg:(mk_rg $startpos $endpos) pt }

(* -------------------------------------------------------------------- *)
consPattern:
| COLON_COLON pta=appPattern ptc=loc(consPattern?)
    { match desc ptc with 
      | None     -> Some pta
      | Some ptc ->
          let pt = Ast.mk_pat_cons (pta, ptc) in
          Some (Ast.mk_pattern ~rg:(mk_rg $startpos $endpos) pt) }

(* -------------------------------------------------------------------- *)
appPattern:
| pts=loc(atomicPattern+)
    { match desc pts with
      | []     -> assert false
      | [pt]   -> pt
      | hd::tl ->
          let pt = Ast.mk_pat_app (hd, tl) in
          Ast.mk_pattern ~rg:(range pts) pt }

(* -------------------------------------------------------------------- *)
atomicPattern:
| pt=tvar
| pt=nonTvarPattern { pt }

(* -------------------------------------------------------------------- *)
nonTvarPattern:
| UNDERSCORE
    { Ast.mk_pat_wild () }

| c=constant
    { Ast.mk_pat_const c }

| id=ident
    { Ast.mk_pat_var id }

| name=qname
    { Ast.mk_pat_name name }

| pt=brackets(plist0(appPattern, SEMICOLON))
    { Ast.mk_pat_list pt }

| pt=parens(ascriptionOrPattern)
    { pt }

| pt=braces(term1(sepby(lid, EQUALS, pattern), SEMICOLON))
    { Ast.mk_pat_record pt }

| LENS_PAREN_LEFT pts=plist1(listPattern, COMMA) LENS_PAREN_RIGHT
    { Ast.mk_pat_tuple pts }

(* -------------------------------------------------------------------- *)
ascriptionOrPattern:
| pt=nonTvarPattern COLON ty=typ
    { Ast.mk_pat_ascribed (pt, ty) }

| tv=loc(tvar) COLON k=kind
    { let pt = Ast.mk_pattern ~rg:(range tv) (Ast.mk_pat_tvar (desc tv)) in
      Ast.mk_pat_ascribed (pt, k) }

| pt=pattern
    { pt }                              (* FIXME *)

(* -------------------------------------------------------------------- *)
binder:
| x=loc(ident)
    { Ast.mk_binder ~rg:(range x) (Ast.mk_bd_var (desc x), `Type, false) }

| x=loc(tvar)
    { Ast.mk_binder ~rg:(range x) (Ast.mk_bd_tvar (desc x), `Kind, false) }

| LPAREN x=ident COLON at=appTerm r=refine? RPAREN
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_binder ~rg (Ast.mk_bd_refined (x, at, r), `Type, false) }

| LPAREN x=tvar COLON k=kind RPAREN
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_binder ~rg (Ast.mk_bd_tannot (x, k), `Kind, false) }

(* -------------------------------------------------------------------- *)
typars:
| x=tvarinsts { x }
| x=binder*   { x }

(* -------------------------------------------------------------------- *)
tvarinsts:
| TYP_APP_LESS tvs=plist1(loc(tvar), COMMA) GREATER
    { let for1 tv =
        let bdtv = Ast.mk_bd_tvar (desc tv) in
        Ast.mk_binder ~rg:(range tv) (bdtv, `Kind, false)
      in List.map for1 tvs }

(* -------------------------------------------------------------------- *)
tyconDefn:
| empty
    { fun (id, bds, k) -> Ast.mk_tycon_abs (id, bds, k) }

| EQUALS ty=typ
    { fun (id, bds, k) -> Ast.mk_tycon_abbrv (id, bds, k, ty) }

| EQUALS fields=braces(plist1(recordFieldDecl, SEMICOLON))
    { fun (id, bds, k) -> Ast.mk_tycon_record (id, bds, k, fields) }

| EQUALS ctors=prefix(BAR, plist1(constructorDecl, BAR))
    { fun (id, bds, k) -> Ast.mk_tycon_variant (id, bds, k, ctors) }

(* -------------------------------------------------------------------- *)
recordFieldDecl:
| x=ident COLON ty=tmTuple
    { (x, ty) }

(* -------------------------------------------------------------------- *)
constructorDecl:
| name=name COLON ty=typ        { (name, Some ty, false) }
| name=name ty=prefix(OF, typ)? { (name,      ty, true) }

(* -------------------------------------------------------------------- *)
kind      : x=product    { Ast.tm_set_level `Kind x }
atomicKind: x=atomicTerm { Ast.tm_set_level `Kind x }
typ       : x=simpleTerm { Ast.tm_set_level `Type x }

(* -------------------------------------------------------------------- *)
term:
| x=plist1(noSeqTerm, SEMICOLON)
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_seq x, `Expr) }

(* -------------------------------------------------------------------- *)
noSeqTerm:
| tm=simpleTerm
    { tm }

| IF cond=noSeqTerm THEN t1=noSeqTerm ELSE t2=noSeqTerm
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_if (cond, t1, t2), `Expr)}

| IF cond=noSeqTerm THEN t=noSeqTerm
    { let e  = Ast.mk_ct_unit () in
      let e  = Ast.mk_term ~rg:(mk_rg $startpos(t) $endpos(t)) (e, `Expr) in
      let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_if (cond, t, e), `Expr) }

| TRY t=term WITH BAR? pt=plist1(patternBranch, BAR)
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_try (t, pt), `Expr) }

| MATCH t=term WITH BAR? pt=plist1(patternBranch, BAR)
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_match (t, pt), `Expr) }

| LET r=boption(REC) bds=plist1(letbinding, AND) IN t=term
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_let (r, bds, t), `Expr) }

| FORALL bds=binder* DOT qp=qpat t=noSeqTerm
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_qforall (bds, qp, t), `Form) }

| EXISTS bds=binder* DOT qp=qpat t=noSeqTerm
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_qexists (bds, qp, t), `Form) }

| FUNCTION BAR? pt=plist1(patternBranch, BAR)
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_function pt, `Expr) }

| x=loc(ASSUME) t=atomicTerm
    { let a  = Ast.mk_term ~rg:(range x) (Ast.mk_tm_var "__assume", `Expr) in
      let rg = mk_rg $startpos $endpos in
      Ast.mk_tm_app ~rg (a, [t]) }

| x=loc(PRINT) ts=atomicTerm+
    { let p  = Ast.mk_term ~rg:(range x) (Ast.mk_tm_var "__print", `Expr) in
      let rg = mk_rg $startpos $endpos in
      Ast.mk_tm_app ~rg (p, ts) }

(* -------------------------------------------------------------------- *)
qpat:
| x=enclosed(LBRACE_COLON_PTN, plist1(appTerm, SEMICOLON), RBRACE)? { x }

(* -------------------------------------------------------------------- *)
simpleTerm:
| t=tmIff
    { t }

| FUN pts=atomicPattern+ fa=funArrow t=term
    { fa ~rg:(mk_rg $startpos $endpos) (Ast.mk_tm_abs (pts, t)) }

(* -------------------------------------------------------------------- *)
patternBranch:
| pts=loc(plist1(pattern, BAR)) cond=prefix(WHEN, appTerm)? RARROW e=term
    { let pts =
        match desc pts with
        | []   -> assert false
        | [pt] -> pt
        | _    -> Ast.mk_pattern ~rg:(range pts) (Ast.mk_pat_or (desc pts))
      in (pts, cond, e) }

(* -------------------------------------------------------------------- *)
funArrow:
| RARROW  { fun ~rg t -> Ast.mk_term ~rg (t, `Expr) }
| RRARROW { fun ~rg t -> Ast.mk_term ~rg (t, `Type) }

(* -------------------------------------------------------------------- *)
tmIff:
| t1=tmImplies IFF t2=tmIff
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("<==>", [t1; t2]), `Formula) }

| t=tmImplies
    { t }
;

(* -------------------------------------------------------------------- *)
tmImplies:
| t1=tmDisjunction IMPLIES t2=tmImplies
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("==>", [t1; t2]), `Formula) }

| t=tmDisjunction
    { t }

(* -------------------------------------------------------------------- *)
tmDisjunction:
| t1=tmDisjunction DISJUNCTION t2=tmConjunction
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("\\/", [t1; t2]), `Formula) }

| t=tmConjunction
    { t }

(* -------------------------------------------------------------------- *)
tmConjunction:
| t1=tmConjunction CONJUNCTION t2=tmTuple
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("/\\", [t1; t2]), `Formula) }

| t=tmTuple
    { t }

(* -------------------------------------------------------------------- *)
tmTuple:
| ts=loc(plist1(tmEq, COMMA))
    { match desc ts with
      | []  -> assert false
      | [t] -> t
      | _   -> Ast.mk_term ~rg:(range ts) (Ast.mk_tm_tuple (desc ts), `Expr) }

(* -------------------------------------------------------------------- *)
tmEq:
| t1=tmEq COLON_EQUALS t2=tmOr
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (":=", [t1; t2]), `Formula) }

| t=tmOr
    { t }

(* -------------------------------------------------------------------- *)
tmOr:
| t1=tmOr BAR_BAR t2=tmAnd
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("||", [t1; t2]), `Formula) }

| t=tmAnd
    { t }

(* -------------------------------------------------------------------- *)
tmAnd:
| t1=tmAnd AMP_AMP t2=cmpTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("&&", [t1; t2]), `Formula) }

| t=cmpTerm
    { t }

(* -------------------------------------------------------------------- *)
cmpTerm:
| t1=cmpTerm op=comparisonOp t2=tmCons
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (op, [t1; t2]), `Formula) }

| t=tmCons
    { t }

(* -------------------------------------------------------------------- *)
comparisonOp:
| PIPE_LEFT          { "<|"  }
| PIPE_RIGHT         { "|>"  }
| LESS               { "<"   }
| GREATER            { ">"   } 
| LEQ                { "<="  }
| GEQ                { ">="  }
| ATSIGN             { "@"   }
| HAT                { "^"   }
| EQUALS             { "="   }
| EQUALS_EQUALS      { "=="  }
| EQUALS_BANG_EQUALS { "=!=" }
| LESSGREATER        { "<>"  }

(* -------------------------------------------------------------------- *)
tmCons:
| t1=product COLON_COLON t2=tmCons      (* FIXME *)
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("::", [t1; t2]), `Formula) }

| t=product
    { t }

(* -------------------------------------------------------------------- *)
product:
| t1=productOrSumDomain pa=prodArrow t2=product
    { let rg = Ast.mk_rg $startpos $endpos in
      pa ~rg (Ast.mk_tm_product ([t1], t2)) }

| t1=loc(appTerm) pa=prodArrow t2=product
    { let rg = Ast.mk_rg $startpos $endpos in
      let bd = (Ast.mk_bd_anon (desc t1), `Un, false) in
      let bd = Ast.mk_binder ~rg:(range t1) bd in
      pa ~rg (Ast.mk_tm_product ([bd], t2)) }

| t=arithTerm
    { t }

(* -------------------------------------------------------------------- *)
prodArrow:
| RARROW  { fun ~rg r -> Ast.mk_term ~rg (r, `Type) }
| RRARROW { fun ~rg r -> Ast.mk_term ~rg (r, `Kind) }

(* -------------------------------------------------------------------- *)
arithTerm:
| t1=starDivModTerm op=PLUS_MINUS_OP t2=arithTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (op, [t1; t2]), `Formula) }

| t=starDivModTerm
    { t }

(* -------------------------------------------------------------------- *)
starDivModTerm:
| t1=sumType STAR t2=starDivModTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op ("*", [t1; t2]), `Formula) }

| t1=sumType op=DIV_MOD_OP t2=starDivModTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (op, [t1; t2]), `Formula) }

| t=sumType
    { t }

(* -------------------------------------------------------------------- *)
sumType:
| t1=productOrSumDomain STAR t2=sumTypeTail
    { let rg = Ast.mk_rg $startpos $endpos in
      let bds, t2 =
       match `Sum ([], t2) with         (* FIXME *)
       | `Sum (bds, t2) -> (bds, t2)
       | _              -> ([] , t2)
     in Ast.mk_term ~rg (`Sum (t1 :: bds, t2), `Type) }

| t=refinementTerm
    { t }

(* -------------------------------------------------------------------- *)
sumTypeTail:
| t1=loc(atomicTerm) STAR t2=sumType
    { let rg = Ast.mk_rg $startpos $endpos in
      let bds, t2 =
       match `Sum ([], t2) with         (* FIXME *)
       | `Sum (bds, t2) -> (bds, t2)
       | _              -> ([] , t2) in

      let bd = (Ast.mk_bd_anon (desc t1), `Type, false) in
      let bd = Ast.mk_binder ~rg:(range t1) bd in
      Ast.mk_term ~rg (`Sum (bd :: bds, t2), `Type) }

| t=sumType
    { t }

(* -------------------------------------------------------------------- *)
productOrSumDomain:
| x=ident COLON at=appTerm r=refine?
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_binder ~rg (Ast.mk_bd_refined (x, at, r), `Type, false) }

| HASH x=ident COLON at=appTerm r=refine?
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_binder ~rg (Ast.mk_bd_refined (x, at, r), `Type, true) }

| x=tvar COLON k=atomicKind
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_binder ~rg (Ast.mk_bd_tannot (x, k), `Kind, false) }

| HASH x=tvar COLON k=atomicKind
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_binder ~rg (Ast.mk_bd_tannot (x, k), `Kind, true) }

(* -------------------------------------------------------------------- *)
refinementTerm:
| x=ident COLON at=appTerm LBRACE f=formula RBRACE
    { let rg = mk_rg $startpos $endpos in
      let bd = (Ast.mk_bd_annot (x, at), `Type, false) in
      let bd = Ast.mk_binder ~rg:(mk_rg $startpos(x) $endpos(at)) bd in
      Ast.mk_term ~rg (Ast.mk_tm_refine (bd, f), `Type) }

| LBRACE t=recordExp RBRACE
    { t }

| t=unaryTerm
    { t }

(* -------------------------------------------------------------------- *)
unaryTerm:
| op=PLUS_MINUS_OP t=atomicTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (op, [t]), `Expr) }

| op=TILDE t=atomicTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (op, [t]), `Formula) }

| t=appTerm
    { t }

(* -------------------------------------------------------------------- *)
appTerm:
| t1=atomicTerm t2=hashAtomicTerms
    { let rg = mk_rg $startpos $endpos in
      Ast.mk_tm_app ~rg (t1, t2) }

(* -------------------------------------------------------------------- *)
formula:
| x=noSeqTerm { Ast.tm_set_level x `Formula }

(* -------------------------------------------------------------------- *)
refine:
| f=braces(formula) { f }

(* -------------------------------------------------------------------- *)
atomicTerm:
| x=loc(UNDERSCORE)
    { Ast.mk_term ~rg:(range x) (Ast.mk_tm_wild, `Un) }

| x=loc(ASSERT)
    { Ast.mk_term ~rg:(range x) (Ast.mk_tm_var "__assert", `Expr) }

| x=loc(tvar)
    { Ast.mk_term ~rg:(range x) (Ast.mk_tm_tvar (desc x), `Type) }

| c=loc(constant)
    { Ast.mk_term ~rg:(range c) (Ast.mk_tm_const (desc c), `Expr) }

| op=BANG t=atomicTerm
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_op (op, [t]), `Expr) }

| LENS_PAREN_LEFT ts=plist1(tmEq, COMMA) LENS_PAREN_RIGHT
    { match ts with
      | []  -> assert false
      | [t] -> t
      | _   ->
        let rg = Ast.mk_rg $startpos $endpos in
        Ast.mk_term ~rg (Ast.mk_tm_dtuple ts, `Expr) }

| t=projectionLHS pjs=maybeFieldProjections
    { let rg = Ast.mk_rg $startpos $endpos in
      List.fold_left (fun e p ->
        Ast.mk_term ~rg (Ast.mk_tm_proj (e, p), `Expr))
        t pjs }

| BEGIN t=term END
    { t }

(* -------------------------------------------------------------------- *)
maybeFieldProjections:
| (* empty *)
    { [] }

| ps=maybeFieldProjections DOT p=ident
    { ps @ [p] }

(* -------------------------------------------------------------------- *)
targs:
| ts=plist1(atomicTerm, COMMA) { ts }

(* -------------------------------------------------------------------- *)
projectionLHS:
| name=eitherQname ts=enclosed(TYP_APP_LESS, targs, GREATER)?
    { let rg = Ast.mk_rg $startpos $endpos in
      let tm = Ast.mk_tm_qname name in
      Ast.mk_term ~rg (Ast.mk_tm_app (tm, ts), `Un) }

| LPAREN t=term sort=pair(hasSort, simpleTerm)? RPAREN
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_term ~rg (Ast.mk_tm_parens (sort, t), Ast.tm_get_level t) }

| LBRACK_BAR ts=term0(noSeqTerm, SEMICOLON) BAR_RBRACK
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_tm_array ~rg (ts, `Expr) }

| LBRACK ts=term0(noSeqTerm, SEMICOLON) RBRACK
    { let rg = Ast.mk_rg $startpos $endpos in
      Ast.mk_tm_list ~rg (ts, `Expr) }

(* -------------------------------------------------------------------- *)
recordExp:
| t=appTerm r=recordExpRest
     { let rg = Ast.mk_rg $startpos $endpos in
       Ast.mk_term ~rg (Ast.mk_tm_record (t, r), `Expr) }

(* -------------------------------------------------------------------- *)
recordExpRest:
| WITH fs=recordFieldAssignments1
    { `RecordWith fs }

| EQUALS t=tmTuple fs=recordFieldAssignments0
    { `RecordLiteral (t, fs) }

(* -------------------------------------------------------------------- *)
recordFieldAssignment:
| x=lid EQUALS t=tmTuple { (x, t) }

(* -------------------------------------------------------------------- *)
recordFieldAssignments0:
| empty | SEMICOLON
    { [] }

| SEMICOLON r=recordFieldAssignment rs=recordFieldAssignments0
    { r :: rs }

(* -------------------------------------------------------------------- *)
recordFieldAssignments1:
| r=recordFieldAssignment rs=recordFieldAssignments0  { r :: rs }

(* -------------------------------------------------------------------- *)
hasSort:
| SUBTYPE { `Expr }
| SUBKIND { `Type }

(* -------------------------------------------------------------------- *)
hashAtomicTerms:
| (* empty *)
    { [] }

| HASH? t1=atomicTerm t2=hashAtomicTerms
    { t1 :: t2 }

(* -------------------------------------------------------------------- *)
constant:
|   LPAREN_RPAREN { Ast.mk_ct_unit      () }
| x=INT32         { Ast.mk_ct_int32     x  }
| x=UINT8         { Ast.mk_ct_uint8     x  }
| x=CHAR          { Ast.mk_ct_char      x  }
| x=STRING        { Ast.mk_ct_string    x  }
| x=BYTEARRAY     { Ast.mk_ct_bytearray x  }
|   TRUE          { Ast.mk_ct_true      () }
|   FALSE         { Ast.mk_ct_false     () }
|   IEEE64        { Ast.mk_ct_ieee64    () }
| x=INT64         { Ast.mk_ct_int64     x  }

(*-------------------------------------------------------------------- *)
%inline braces(X):
| LBRACE x=X RBRACE { x }

%inline brackets(X):
| LBRACK x=X RBRACK { x }

%inline parens(X):
| LPAREN x=X RPAREN { x }

(* -------------------------------------------------------------------- *)
%inline sepby(X1, S, X2):
| x1=X1 S x2=X2 { (x1, x2) }

(* -------------------------------------------------------------------- *)
%inline plist0(X, S):
| aout=separated_list(S, X) { aout }

%inline plist1(X, S):
| aout=separated_nonempty_list(S, X) { aout }

(* -------------------------------------------------------------------- *)
%inline term1(X, S):
| aout=rlist1(X, S) S? { aout }

%inline term0(X, S):
| aout=rlist1(X, S) S? { aout }

(* -------------------------------------------------------------------- *)
__rlist1(X, S):                         (* left-recursive *)
| x=X { [x] }
| xs=__rlist1(X, S) S x=X { x :: xs }

%inline rlist0(X, S):
| /* empty */     { [] }
| xs=rlist1(X, S) { xs }

%inline rlist1(X, S):
| xs=__rlist1(X, S) { List.rev xs }

(* -------------------------------------------------------------------- *)
%inline prefix(S, X):
| S x=X { x }

%inline suffix(S, X):
| x=X S { x }

%inline enclosed(S1, X, S2):
| S1 x=X S2 { x }

(* -------------------------------------------------------------------- *)
%inline empty:
| (* empty *) {}

(* -------------------------------------------------------------------- *)
%inline loc(X):
| x=X { Ast.mk_loc (mk_rg $startpos $endpos) x }
