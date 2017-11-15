#light "off"
module FStar.Errors
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Util
open FStar.Range

type raw_error =
  | ReservedPrefix
  | NotValidFStarFile
  | NotValidIncludeDirectory
  | ModuleFileNotFound
  | UnknowToolForDep
  | UnrecognizedExtension
  | UnableToReadFile
  | Uninstantiated 
  | IllTyped of string
  | ValueRestriction 
  | UnexpectedEffect 
  | NotTopLevelModule
  | NonSingletonTopLevel 
  | MissingPrimsModule 
  | IDEMissingFileName 
  | IDETooManyFiels 
  | NotSupported 
  | OptionsNotCompatible 
  | NoFileProvided
  | NonSingletonTopLevelModule 
  | PreModuleMismatch 
  | ModuleFirstStatement 
  | ParseErrors 
  | MultipleLetBinding 
  | UnexpectedIdentifier 
  | InlineRenamedAsUnfold 
  | UnfoldableDeprecated 
  | DeprecatedEqualityOnBinder
  | MissingQuantifierBinder 
  | OutOfRange of string (* the type of the integer *)
  | OpPlusInUniverse 
  | InvalidUniverseVar 
  | InvalidIdentifier 
  | MoreThanOneDeclaration 
  | Filtered 
  | UnexpectedModuleDeclaration 
  | UnexpectedOperatorSymbol 
  | UnexpectedTerm 
  | ModuleFileNameMismatch 
  | LetOpenModuleOnly 
  | ModuleOrFileNotFound 
  | ModuleOrFileNotFoundWarning
  | UnboundModuleReference 
  | OneModulePerFile 
  | SyntaxError 
  | ParseItError 
  | ModuleExpected 
  | DefinitionNotFound 
  | AbstractTypeNotAllowed 
  | DuplicateInImplementation 
  | InterfaceWithTypeImplementation 
  | BothValLetInInterface 
  | AssumedDeclNotAllowed 
  | OutOfOrder 
  | IllegalCharInByteArray 
  | IllegalCharInOperatorName 
  | InvalidFloatingPointNumber 
  | InvalidNumericLiteral 
  | InvalidUnicodeInStringLiteral 
  | InvalidFSDocKeyword 
  | UnexpectedChar 
  | UnexpectedPosition 
  | UnprotectedTerm 
  | NotEmbedded of string (* the nature of the term *)
  | FunctionLiteralPrecisionLoss 
  | NonTopRecFunctionNotFullyEncoded 
  | NonListLiteralSMTPattern 
  | SMTPatternMissingBoundVar 
  | NonVaribleInductiveTypeParameter 
  | UnexpectedConstructorType 
  | SMTSolverError 
  | Z3InvocationError 
  | Z3InvocationWarning
  | SMTOutputParseError 
  | UnexpectedZ3Output 
  | CycleInRecTypeAbbreviation 
  | ImpossibleAbbrevLidBundle 
  | ImpossibleAbbrevRenameBundle 
  | ImpossibleTypeAbbrevSigeltBundle 
  | ImpossibleTypeAbbrevBundle 
  | ImpossibleInductiveWithAbbrev 
  | InaccessibleArgument 
  | WrongDataAppHeadFormat 
  | TacticGotStuck
  | UserTacticFailure 
  | OpenGoalsInSynthesis 
  | UninstantiatedVarInTactic 
  | ForbiddenReferenceToCurrentModule 
  | DuplicateTopLevelNames 
  | NameSpaceNotFound 
  | IncludeModuleNotPrepared 
  | ModuleNotFound 
  | DocOverwrite 
  | AdmitWithoutDefinition 
  | DuplicateModuleOrInterface 
  | MonadAlreadyDefined 
  | IdentifierNotFound 
  | AbstractTypeDeclarationInInterface 
  | WrongDefinitionOrder 
  | BothValAndLetInInterface 
  | AssumeValInInterface 
  | InterfaceNotImplementedByModule 
  | InterfaceAlreadyProcessed 
  | DeprecatedOpaqueQualifier 
  | ReflectOnlySupportedOnEffects 
  | DefaultQualifierNotAllowedOnEffects 
  | UnsupportedQualifier 
  | NegativeUniverseConstNotSupported 
  | UniverseMightContainSumOfTwoUnivVars 
  | FieldsNotBelongToSameRecordType 
  | LetMutableForVariablesOnly 
  | TypeWithinPatternsAllowedOnVariablesOnly 
  | UnexpectedPattern 
  | UnexpectedNumericLiteral 
  | UnknownAttribute 
  | UnepxectedOrUnboundOperator 
  | AssignToImmutableValues 
  | EffectNotFound 
  | DataContructorNotFound 
  | ConstructorNotFound 
  | UnsupportedDisjuctivePatterns 
  | ComputationTypeNotAllowed 
  | UnexpectedEmptyRecord 
  | MissingFieldInRecord 
  | InvalidLemmaArgument 
  | NotEnoughArgsToEffect 
  | UnexpectedLetBinding 
  | UnexpectedTermInUniverse 
  | UnexpectedUniverseVariable 
  | UseDefaultEffect 
  | AddImplicitAssumeNewQualifier 
  | MissingNameInBinder 
  | UnexpectedBinder 
  | MalformedActionDeclaration 
  | ArgumentLengthMismatch 
  | WrongTerm 
  | TermOutsideOfDefLanguage 
  | LetBoundMonadicMismatch 
  | TypeMismatch 
  | EffectfulAndPureComputationMismatch 
  | NotFunctionType 
  | BinderAndArgsLengthMismatch 
  | WhenClauseNotSupported 
  | NameNotFound 
  | VariableNotFound 
  | EffectsCannotBeComposed 
  | DivergentComputationCannotBeIncludedInTotal 
  | ConstructorArgLengthMismatch 
  | NotEnoughArgumentsForEffect 
  | UnexpectedSignatureForMonad 
  | ExpectTermGotFunction 
  | UnexpectedImplicitArgument 
  | UnexpectedExpressionType 
  | UnexpectedFunctionParameterType 
  | TypeError 
  | PossibleInfiniteTyp 
  | UnificationNotWellFormed 
  | IncompatibleKinds 
  | ConstsructorBuildWrongType 
  | ConstructorFailedCheck 
  | DuplicateTypeAnnotationAndValDecl 
  | InferredTypeCauseVarEscape 
  | FunctionTypeExpected 
  | PolyTypeExpected 
  | NonLinearPatternVars 
  | DisjuctivePatternVarsMismatch 
  | ComputedTypeNotMatchAnnotation 
  | UnExpectedPreCondition 
  | ExpectedPureExpression 
  | ExpectedGhostExpression 
  | TypeCheckerFailToProve 
  | TopLevelEffect 
  | CardinalityConstraintViolated 
  | MetaAlienNotATmUnknow
  | NotApplicationOrFv
  | InductiveTypeNotSatisfyPositivityCondition
  | PatternMissingBoundVar
  | UncontrainedUnificationVar
  | IrrelevantQualifierOnArgumentToReify
  | IrrelevantQualifierOnArgumentToReflect
  | RedundantExplicitCurrying
  | ActionMustHaveFunctionType
  | InvalidRedefinitionOfLexT
  | FailToProcessPragma
  | EffectCannotBeReified
  | TooManyUniverse
  | InconsistentQualifierAnnotation
  | AlreadyDefinedTopLevelDeclaration
  | IncoherentInlineUniverse
  | WrongResultTypeAfterConstrutor
  | NonInductiveInMutuallyDefinedType
  | UnexpectedComputationTypeForLetRec
  | InsufficientPatternArguments
  | NonTrivialPreConditionInPrims
  | EffectConstructorNotFullyApplied
  | UnexpectedGeneralizedUniverse
  | MissingImplicitArguments
  | IncompatibleNumberOfTypes
  | QulifierListNotPermitted
  | UnexpectedDataConstructor
  | BadSignatureShape
  | ComputationNotTotal
  | WrongBodyTypeForReturnWP
  | UnexpectedReturnShape
  | UnexpectedBindShape
  | ImpossibleToGenerateDMEffect
  | ImpossiblePrePostArrow
  | ImpossiblePrePostAbs
  | ExpectNormalizedEffect
  | IncompatibleUniverse
  | FailToSolveUniverseInEquality
  | ErrorInSolveDeferredConstraints
  | ExpectTrivialPreCondition
  | FailToResolveImplicitArgument
  | UnexpectedGTotComputation
  | UnexpectedInstance
  | IncompatibleSetOfUniverse
  | TooManyPatternArguments
  | UnexpectedUniversePolymorphicReturn
  | MismatchUniversePolymorphic
  | EscapedBoundVar
  | ExpectedArrowAnnotatedType
  | SynthByTacticError
  | MissingDataConstructor
  | BadlyInstantiatedSynthByTactic
  | UnexpectedNumberOfUniverse
  | UnsupportedConstant
  | InconsistentImplicitArgumentAnnotation
  | ToManyArgumentToFunction
  | InconsistentImplicitQualifier
  | LetRecArgumentMismatch
  | RecursiveFunctionLiteral
  | UnexpectedGTotForLetRec
  | UnexpectedImplictArgument
  | UnexpectedTermType
  | UniversePolymorphicInnerLetBound
  | UnresolvedPatternVar
  | HintFailedToReplayProof
  | HitReplayFailed
  | ProofObligationFailed
  | UnknowAssertionFailure
  | Z3SolverError
  | UninstantiatedUnificationVarInTactic
  | AssertionFailure
  | MissingInterface
  | MissingImplementation
  | TooManyOrTooFewFileMatch
  | UnexpectedGuard
  | ErrorsReported
  | TcOneFragmentFailed
  | MissingExposeInterfacesOption
  | NonLinearPatternNotPermitted
  | SMTPatTDeprecated
  | IllAppliedConstant
  | MismatchedPatternType
  | FreeVariables of string
  | UnexpectedInductivetype
  | IllFormedGoal
  | CachedFile
  | FileNotWritten
  | InvalidUTF8Encoding
  | FailToCompileNativeTactic

exception Err of raw_error* string
exception Error of raw_error * string * Range.range
exception Warning of raw_error * string * Range.range
exception Stop

(* Raised when an empty fragment is parsed *)
exception Empty_frag

module BU = FStar.Util

type issue_level =
| ENotImplemented
| EInfo
| EWarning
| EError

type issue = {
    issue_message: string;
    issue_level: issue_level;
    issue_range: option<Range.range>
}

type error_handler = {
    eh_add_one: issue -> unit;
    eh_count_errors: unit -> int;
    eh_report: unit -> list<issue>;
    eh_clear: unit -> unit
}

let format_issue issue =
    let level_header =
        match issue.issue_level with
        | EInfo -> "(Info) "
        | EWarning -> "(Warning) "
        | EError -> "(Error) "
        | ENotImplemented -> "Feature not yet implemented: " in
    let range_str, see_also_str =
        match issue.issue_range with
        | None -> "", ""
        | Some r ->
          (BU.format1 "%s: " (Range.string_of_use_range r),
           (if use_range r = def_range r then ""
            else BU.format1 " (see also %s)" (Range.string_of_range r))) in
    BU.format4 "%s%s%s%s\n" range_str level_header issue.issue_message see_also_str

let print_issue issue =
    BU.print_error (format_issue issue)

let compare_issues i1 i2 =
    match i1.issue_range, i2.issue_range with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some r1, Some r2 -> Range.compare_use_range r1 r2

let default_handler =
    let errs : ref<list<issue>> = BU.mk_ref [] in
    let add_one (e: issue) =
        match e.issue_level with
        | EError -> errs := e :: !errs
        | _ -> print_issue e in
    let count_errors () =
        List.length !errs in
    let report () =
        let sorted = List.sortWith compare_issues !errs in
        List.iter print_issue sorted;
        sorted in
    let clear () =
        errs := [] in
    { eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear }

let current_handler =
    BU.mk_ref default_handler

let mk_issue level range msg =
    { issue_level = level; issue_range = range; issue_message = msg }

let get_err_count () = (!current_handler).eh_count_errors ()

let add_one issue =
    atomically (fun () -> (!current_handler).eh_add_one issue)

let add_many issues =
    atomically (fun () -> List.iter (!current_handler).eh_add_one issues)

let report_all () =
    (!current_handler).eh_report ()

let clear () =
    (!current_handler).eh_clear ()

let set_handler handler =
    let issues = report_all () in
    clear (); current_handler := handler; add_many issues


type error_message_prefix = {
    set_prefix: string -> unit;
    append_prefix: string -> string;
    clear_prefix: unit -> unit;
}

let message_prefix =
    let pfx = BU.mk_ref None in
    let set_prefix s = pfx := Some s in
    let clear_prefix () = pfx := None in
    let append_prefix s = match !pfx with
        | None -> s
        | Some p -> p ^ ": " ^ s in
    {set_prefix=set_prefix;
     clear_prefix=clear_prefix;
     append_prefix=append_prefix}

let errno_of_error = function
  | OutOfRange _ -> 1
  | OpPlusInUniverse -> 2
  | InvalidUniverseVar -> 3
  | Z3InvocationError -> 4
  | TypeError -> 5
  | TypeCheckerFailToProve -> 6
  | InductiveTypeNotSatisfyPositivityCondition -> 7
  | UncontrainedUnificationVar -> 8
  | UnexpectedGTotComputation -> 9
  | UnexpectedInstance -> 10
  | ProofObligationFailed -> 11
  | UnknowAssertionFailure -> 12
  | UninstantiatedUnificationVarInTactic -> 13
  | AssertionFailure -> 14
  | MissingInterface -> 15
  | MissingImplementation -> 16
  | TooManyOrTooFewFileMatch -> 17
  | DeprecatedEqualityOnBinder -> 18
  | Filtered -> 19
  | ModuleFileNameMismatch -> 20
  | ModuleOrFileNotFoundWarning -> 21
  | UnboundModuleReference -> 22
  | UnprotectedTerm -> 23 
  | NotEmbedded _ -> 24
  | FunctionLiteralPrecisionLoss -> 25 
  | NonListLiteralSMTPattern -> 26
  | SMTPatternMissingBoundVar -> 27
  | UnexpectedConstructorType -> 28
  | Z3InvocationWarning -> 29
  | UnexpectedZ3Output -> 30
  | InaccessibleArgument -> 31
  | DocOverwrite -> 32
  | AdmitWithoutDefinition -> 33 
  | DeprecatedOpaqueQualifier -> 34
  | UseDefaultEffect -> 35
  | AddImplicitAssumeNewQualifier -> 36 
  | TopLevelEffect -> 37
  | MetaAlienNotATmUnknow -> 38
  | PatternMissingBoundVar -> 39
  | IrrelevantQualifierOnArgumentToReify -> 40
  | IrrelevantQualifierOnArgumentToReflect -> 41
  | RedundantExplicitCurrying -> 42
  | HintFailedToReplayProof -> 43
  | HitReplayFailed -> 44
  | SMTPatTDeprecated -> 45
  | CachedFile -> 46
  | FileNotWritten -> 47
  | IllFormedGoal -> 48 (* when new entries are added, need to update "next_errno" and default "warn_error" in Options.fs *)
  | _ -> 0 (** Things that cannot be silenced! *)

type flag =
  | CError | CWarning | CSilent

let next_errno = 49 // the number needs to match the number of entries in "errno_of_error"
let flags: ref<list<flag>> = mk_ref []

let update_flags l =
  let compare (_, (a, _)) (_, (b, _)) =
    if a > b then 1 
    else if a < b then -1
    else 0
  in
  let sorted = List.sortWith compare l in
  let rec set_flag i l= 
    match l with 
    | [] -> List.nth !flags i
    | (f, (l, h))::tl -> 
      if (i>=l && i <= h) then f
      else if (i<l) then List.nth !flags i
      else set_flag i tl
  in
  let rec aux f i l = match l with
    | [] -> f
    | hd::tl -> aux (f@[set_flag i sorted]) (i+1) tl
  in
  let rec init_flags l i = 
    if i > 0 then init_flags (l@[CError]) (i-1) else l
  in
  let rec check_range l = match l with
    | [] -> ()
    | (_, (l, h))::tl -> 
      if l < 0 || h > next_errno then  failwith (BU.format2 "No error for warn_error %s..%s" (string_of_int l) (string_of_int h))
  in
  check_range l;
  if !flags = [] then flags := init_flags [] next_errno;
  flags := aux [] 0 !flags

let diag r msg = 
  if Options.debug_any() then add_one (mk_issue EInfo (Some r) msg)

let maybe_fatal_error r (e, msg) =
  let errno = errno_of_error (e) in
  match List.nth !flags errno with
  | CError ->
     add_one (mk_issue EError (Some r) msg)
  | CWarning ->
     add_one (mk_issue EWarning (Some r) msg)
  | CSilent ->
      ()

let add_errors errs =
    atomically (fun () -> List.iter (fun (e, msg, r) -> maybe_fatal_error r (e, (message_prefix.append_prefix msg))) errs)

let issue_of_exn = function
    | Error(e, msg, r) ->
      Some (mk_issue EError (Some r) (message_prefix.append_prefix msg))
    | NYI msg ->
      Some (mk_issue ENotImplemented None (message_prefix.append_prefix msg))
    | Err (e, msg) ->
      Some (mk_issue EError None (message_prefix.append_prefix msg))
    | _ -> None

let err_exn exn =
    if exn = Stop then ()
    else
    match issue_of_exn exn with
    | Some issue -> add_one issue
    | None -> raise exn

let handleable = function
  | Error _
  | NYI _
  | Stop
  | Err _ -> true
  | _ -> false

let stop_if_err () =
    if get_err_count () > 0
    then raise Stop

let raise_error (e, msg) r =
  raise (Error (e, msg, r))

let raise_err (e, msg) =
  raise (Err (e, msg))

