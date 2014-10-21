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
%token LBRACE_COLON_PATTERN
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

(* -------------------------------------------------------------------- *)
file: 
| pragmas moduleList
{};

(* -------------------------------------------------------------------- *)
moduleList:
| modul moduleList
| EOF
{};      
      
(* -------------------------------------------------------------------- *)
modul:    
| MODULE qname decls endopt
{};

(* -------------------------------------------------------------------- *)
endopt:
| (* empty *)
| END   
{};

(* -------------------------------------------------------------------- *)
pragmas: 
| (* empty *)
| pragmas pragma
{};

(* -------------------------------------------------------------------- *)
pragma: 
| PRAGMAMONADIC LPAREN eitherQname COMMA eitherQname COMMA eitherQname RPAREN
| PRAGMALIGHT STRING
{};

(* -------------------------------------------------------------------- *)
decls:
| (* empty *)
| SEMICOLON_SEMICOLON term 
| decl decls
{};

(* -------------------------------------------------------------------- *)
decl:
| decl_r
{};

(* -------------------------------------------------------------------- *)
decl_r:
| OPEN qname
| kind_abbrev 
| tycon 
| LET recopt letbinding letbindings
| qualifiers VAL eitherName COLON typ
| assumeTag name COLON formula
| EXCEPTION name of_typ
| MONADLATTICE LBRACE monads with_lifts RBRACE
{};

(* -------------------------------------------------------------------- *)
tycon:
| qualifiers TYPE tyconDefinition tyconDefinitions 
| EFFECT tyconDefinition 
{};

(* -------------------------------------------------------------------- *)
kind_abbrev: 
| KIND name binders EQUALS kind
{};

(* -------------------------------------------------------------------- *)
monads:
| monad moreMonads
{};

(* -------------------------------------------------------------------- *)
moreMonads:
| (* empty *)
| SEMICOLON monad moreMonads 
{};

(* -------------------------------------------------------------------- *)
maybeTotal:
| (* empty *)
| TOTAL 
{};

(* -------------------------------------------------------------------- *)
monad:
| name COLON_COLON maybeTotal monad_decls WITH monad_abbrevs
{};

(* -------------------------------------------------------------------- *)
monad_decl: 
| kind_abbrev
| tycon 
{};

(* -------------------------------------------------------------------- *)
monad_decls:
| (* empty *)
| monad_decl monad_decls 
{};

(* -------------------------------------------------------------------- *)
monad_abbrev: 
| name typars EQUALS typ
{};

(* -------------------------------------------------------------------- *)
monad_abbrevs:
| monad_abbrev more_monad_abbrevs 
{};

(* -------------------------------------------------------------------- *)
more_monad_abbrevs: 
| (* empty *)
| AND monad_abbrev more_monad_abbrevs 
{};

(* -------------------------------------------------------------------- *)
with_lifts:
| (* empty *)
| WITH lifts 
{};

(* -------------------------------------------------------------------- *)
lifts:
| lift moreLifts
{};

(* -------------------------------------------------------------------- *)
moreLifts:
| (* empty *)
| SEMICOLON lift moreLifts 
{};

(* -------------------------------------------------------------------- *)
lift:
| name SQUIGGLY_RARROW name EQUALS atomicTerm
{};

(* -------------------------------------------------------------------- *)
qualifiers:
| (* empty *)
| LOGIC        
| ASSUME       
| ASSUME LOGIC 
{};

(* -------------------------------------------------------------------- *)
assumeTag:
| ASSUME 
| QUERY  
| DEFINE 
{};

(* -------------------------------------------------------------------- *)
tyconDefinition:
| eitherName typars ascribeKindOpt tyconDefn
{};

(* -------------------------------------------------------------------- *)
tyconDefinitions:
| (* empty *)
| AND tyconDefinition tyconDefinitions
{};

(* -------------------------------------------------------------------- *)
recopt:
| (* empty *)
| REC 
{};

(* -------------------------------------------------------------------- *)
letbindings:
| (* empty *)
| AND letbinding letbindings 
{};

(* -------------------------------------------------------------------- *)
letbinding:
| pattern ascribeTypOpt EQUALS term 
{};      
      
(* -------------------------------------------------------------------- *)
pattern:
| tuplePattern 
{};

(* -------------------------------------------------------------------- *)
tuplePattern:
| listPattern patternListComma 
{};

(* -------------------------------------------------------------------- *)
patternListComma:
| (* empty *)
| COMMA listPattern patternListComma 
{};

(* -------------------------------------------------------------------- *)
listPattern:
| appPattern consPattern
{};

(* -------------------------------------------------------------------- *)
consPattern:
| (* empty *)
| COLON_COLON appPattern consPattern 
{};

(* -------------------------------------------------------------------- *)
appPattern:
| atomicPattern atomicPatterns
{};

(* -------------------------------------------------------------------- *)
atomicPatterns:
| (* empty *)
| atomicPattern atomicPatterns 
{};

(* -------------------------------------------------------------------- *)
atomicPattern: 
| atomicPattern_r
{};

(* -------------------------------------------------------------------- *)
atomicPattern_r:
| nonTvarPattern_r 
| tvar  
{};

(* -------------------------------------------------------------------- *)
nonTvarPattern:
| nonTvarPattern_r 
{};

(* -------------------------------------------------------------------- *)
nonTvarPattern_r:      
| UNDERSCORE 
| constant 
| ident 
| qname 
| LBRACK patternListSemiColon RBRACK 
| LPAREN ascriptionOrPattern RPAREN  
| LBRACE recordPattern RBRACE 
| LENS_PAREN_LEFT listPattern COMMA listPattern patternListComma LENS_PAREN_RIGHT 
{};

(* -------------------------------------------------------------------- *)
ascriptionOrPattern:
| nonTvarPattern COLON typ 
| tvar COLON  kind        
| pattern 
{};

(* -------------------------------------------------------------------- *)
patternListSemiColon:
| (* empty *)
| appPattern patternListSemiColonRest 
{};

(* -------------------------------------------------------------------- *)
patternListSemiColonRest:
| (* empty *)
| SEMICOLON appPattern patternListSemiColonRest 
{};

(* -------------------------------------------------------------------- *)
recordPattern:
| lid EQUALS pattern moreFieldPatterns 
{};
      
(* -------------------------------------------------------------------- *)
moreFieldPatterns:
| (* empty *)
| SEMICOLON lid EQUALS pattern moreFieldPatterns 
{};

(* -------------------------------------------------------------------- *)
binder:
| ident 
| tvar  
| LPAREN ident COLON appTerm refineOpt RPAREN 
| LPAREN tvar COLON  kind RPAREN 
{};

(* -------------------------------------------------------------------- *)
typars:
| tvarinsts              
| binders                
{};

(* -------------------------------------------------------------------- *)
tvarinsts: 
| TYP_APP_LESS tvars GREATER    
{};

(* -------------------------------------------------------------------- *)
binders: 
| (* empty *)
| binder binders 
{};

(* -------------------------------------------------------------------- *)
tyconDefn: 
| (* empty *)
| EQUALS typ    
| EQUALS LBRACE recordFieldDecl recordFields RBRACE 
| EQUALS constructors 
{};

(* -------------------------------------------------------------------- *)
recordFields:
| (* empty *)
| SEMICOLON recordFieldDecl recordFields
| SEMICOLON 
{};

(* -------------------------------------------------------------------- *)
constructors:
| (* empty *)
| constructors constructorDecl
{};

(* -------------------------------------------------------------------- *)
recordFieldDecl:
| ident COLON tmTuple
{};

(* -------------------------------------------------------------------- *)
constructorDecl:
| BAR name COLON typ
| BAR name of_typ
{};

(* -------------------------------------------------------------------- *)
of_typ:
| (* empty *)
| OF typ 
{};

(* -------------------------------------------------------------------- *)
eitherQname: 
| eitherQname_r 
{};

(* -------------------------------------------------------------------- *)
eitherQname_r: 
| eitherName 
| name DOT eitherQname_r 
{};

(* -------------------------------------------------------------------- *)
lid:
| idpath 
{};

(* -------------------------------------------------------------------- *)
qname:
| namepath 
{};

(* -------------------------------------------------------------------- *)
eitherName:
| ident  
| name  
{};

(* -------------------------------------------------------------------- *)
ident:
| IDENT 
{};

(* -------------------------------------------------------------------- *)
name:
| NAME 
{};

(* -------------------------------------------------------------------- *)
tvars:
| TVAR                
| TVAR COMMA tvars    
{};

(* -------------------------------------------------------------------- *)
tvar:
| TVAR 
{};

(* -------------------------------------------------------------------- *)
namepath:
| name 
| name DOT namepath
{};

(* -------------------------------------------------------------------- *)
idpath:
| ident 
| name DOT idpath
{};      
      
(* -------------------------------------------------------------------- *)
ascribeTypOpt:
| (* empty *)
| COLON product 
{};

(* -------------------------------------------------------------------- *)
ascribeKindOpt: 
| (* empty *)
| COLON  kind 
{};

(* -------------------------------------------------------------------- *)
kind:
| product
{};

(* -------------------------------------------------------------------- *)
atomicKind:
| atomicTerm
{};
      
(* -------------------------------------------------------------------- *)
typ: 
| simpleTerm
{};

(* -------------------------------------------------------------------- *)
term:
| noSeqTerm 
| noSeqTerm SEMICOLON term 
{};

(* -------------------------------------------------------------------- *)
noSeqTerm:
| simpleTerm 
| IF noSeqTerm THEN noSeqTerm ELSE noSeqTerm
| IF noSeqTerm THEN noSeqTerm
| TRY term WITH firstPatternBranch patternBranches 
| MATCH term WITH firstPatternBranch patternBranches 
| LET recopt letbinding letbindings IN term
| FORALL binders DOT qpat noSeqTerm
| EXISTS binders DOT qpat noSeqTerm
| FUNCTION firstPatternBranch patternBranches 
| ASSUME atomicTerm 
| PRINT atomicTerm atomicTerms
{};

(* -------------------------------------------------------------------- *)
qpat: 
| (* empty *)
| LBRACE_COLON_PATTERN appTerm morePats RBRACE
{};

(* -------------------------------------------------------------------- *)
morePats:
| (* empty *)
| SEMICOLON appTerm morePats  
{};

(* -------------------------------------------------------------------- *)
simpleTerm:
| tmIff 
| FUN atomicPattern atomicPatterns funArrow term
{};

(* -------------------------------------------------------------------- *)
patternBranches:
| (* empty *)
| patternBranches patternBranch
{};

(* -------------------------------------------------------------------- *)
maybeBar:
| (* empty *)
| BAR 
{};

(* -------------------------------------------------------------------- *)
firstPatternBranch: /* shift/reduce conflict on BAR ... expected for nested matches */
| maybeBar disjunctivePattern maybeWhen RARROW term 
{};

(* -------------------------------------------------------------------- *)
patternBranch: /* shift/reduce conflict on BAR ... expected for nested matches */
| BAR disjunctivePattern maybeWhen RARROW term 
{};

(* -------------------------------------------------------------------- *)
disjunctivePattern:
| pattern     
| pattern BAR disjunctivePattern 
{};

(* -------------------------------------------------------------------- *)
maybeWhen:
| (* empty *)
| WHEN appTerm        
{};

(* -------------------------------------------------------------------- *)
funArrow:
| RARROW 
| RRARROW 
{};

(* -------------------------------------------------------------------- *)
tmIff:
| tmImplies IFF tmIff
| tmImplies
{};

(* -------------------------------------------------------------------- *)
tmImplies:
| tmDisjunction IMPLIES tmImplies
| tmDisjunction
{};

(* -------------------------------------------------------------------- *)
tmDisjunction:
| tmDisjunction DISJUNCTION tmConjunction
| tmConjunction
{};

(* -------------------------------------------------------------------- *)
tmConjunction:
| tmConjunction CONJUNCTION tmTuple
| tmTuple
{};

(* -------------------------------------------------------------------- *)
tmTuple:
| tupleN
{};

(* -------------------------------------------------------------------- *)
tmEq:
| tmEq COLON_EQUALS tmOr
| tmOr
{};

(* -------------------------------------------------------------------- *)
tmOr:
| tmOr BAR_BAR tmAnd
| tmAnd
{};

(* -------------------------------------------------------------------- *)
tmAnd:
| tmAnd AMP_AMP cmpTerm
| cmpTerm
{};      
      
(* -------------------------------------------------------------------- *)
cmpTerm:
| cmpTerm comparisonOp tmCons
| tmCons
{};

(* -------------------------------------------------------------------- *)
comparisonOp:
| PIPE_LEFT 
| PIPE_RIGHT 
| LESS 
| GREATER  
| LEQ 
| GEQ 
| ATSIGN 
| HAT 
| EQUALS 
| EQUALS_EQUALS 
| EQUALS_BANG_EQUALS 
| LESSGREATER 
{};

(* -------------------------------------------------------------------- *)
tmCons:
| product COLON_COLON tmCons
| product
{};

(* -------------------------------------------------------------------- *)
product: 
| productOrSumDomain prodArrow product
| appTerm prodArrow product
| arithTerm
{};

(* -------------------------------------------------------------------- *)
prodArrow:
| RARROW 
| RRARROW 
{};

(* -------------------------------------------------------------------- *)
arithTerm:
| starDivModTerm PLUS_MINUS_OP arithTerm
| starDivModTerm 
{};

(* -------------------------------------------------------------------- *)
starDivModTerm:
| sumType STAR starDivModTerm 
| sumType DIV_MOD_OP starDivModTerm
| sumType
{};

(* -------------------------------------------------------------------- *)
sumType:
| productOrSumDomain STAR sumTypeTail
| refinementTerm
{};

(* -------------------------------------------------------------------- *)
sumTypeTail:
| atomicTerm STAR sumType
| sumType
{};

(* -------------------------------------------------------------------- *)
productOrSumDomain:
| ident COLON appTerm refineOpt
| HASH ident COLON appTerm refineOpt
| tvar COLON atomicKind
| HASH tvar COLON atomicKind
{};

(* -------------------------------------------------------------------- *)
refineOpt:
| (* empty *)
| LBRACE formula RBRACE 
{};

(* -------------------------------------------------------------------- *)
refinementTerm:
| ident COLON appTerm LBRACE formula RBRACE 
| LBRACE recordExp RBRACE
| unaryTerm
{};

(* -------------------------------------------------------------------- *)
unaryTerm: 
| PLUS_MINUS_OP atomicTerm
| TILDE atomicTerm
| appTerm 
{};

(* -------------------------------------------------------------------- *)
appTerm:
| atomicTerm hashAtomicTerms
{};      

(* -------------------------------------------------------------------- *)
formula:
| noSeqTerm
{};

(* -------------------------------------------------------------------- *)
atomicTerm:
| UNDERSCORE
| ASSERT
| tvar
| constant
| LENS_PAREN_LEFT tupleN LENS_PAREN_RIGHT 
| projectionLHS maybeFieldProjections 
| BANG atomicTerm
| BEGIN term END 
{};

(* -------------------------------------------------------------------- *)
maybeFieldProjections:
| (* empty *)
| maybeFieldProjections DOT ident 
{};

(* -------------------------------------------------------------------- *)
targs:
| atomicTerm
| atomicTerm COMMA targs
{};

(* -------------------------------------------------------------------- *)
maybeInsts:
| (* empty *)
| TYP_APP_LESS targs GREATER 
{};

(* -------------------------------------------------------------------- *)
projectionLHS:
| eitherQname maybeInsts
| LPAREN term maybeWithSort RPAREN 
| LBRACK_BAR semiColonTermList BAR_RBRACK
| LBRACK semiColonTermList RBRACK
{};

(* -------------------------------------------------------------------- *)
semiColonTermList:
| (* empty *)
| noSeqTerm moreSemiColonTerms
{};

(* -------------------------------------------------------------------- *)
moreSemiColonTerms:
| (* empty *)
| SEMICOLON
| SEMICOLON noSeqTerm moreSemiColonTerms 
{};

(* -------------------------------------------------------------------- *)
recordExp: 
| appTerm recordExpRest 
{};

(* -------------------------------------------------------------------- *)
recordExpRest:
| WITH recordFieldAssignment recordFieldAssignments
| EQUALS tmTuple recordFieldAssignments
{};

(* -------------------------------------------------------------------- *)
recordFieldAssignment:
| lid EQUALS tmTuple 
{};

(* -------------------------------------------------------------------- *)
recordFieldAssignments:
| (* empty *)
| SEMICOLON
| SEMICOLON recordFieldAssignment recordFieldAssignments
{};

(* -------------------------------------------------------------------- *)
maybeWithSort:
| (* empty *)
| hasSort simpleTerm
{};

(* -------------------------------------------------------------------- *)
hasSort:
| SUBTYPE
| SUBKIND
{};

(* -------------------------------------------------------------------- *)
maybeHash: 
| (* empty *)
| HASH
{};

(* -------------------------------------------------------------------- *)
hashAtomicTerms:
| (* empty *)
| maybeHash atomicTerm hashAtomicTerms
{};

(* -------------------------------------------------------------------- *)
atomicTerms: 
|
| atomicTerm atomicTerms
{};

(* -------------------------------------------------------------------- *)
tupleN:
| tmEq
| tmEq COMMA tupleN
{};

(* -------------------------------------------------------------------- *)
constant:
| LPAREN_RPAREN
| INT32
| UINT8
| CHAR
| STRING
| BYTEARRAY
| TRUE
| FALSE
| IEEE64
| INT64
{};
