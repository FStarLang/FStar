#light "off"
module FStar.Errors
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Util
open FStar.Range

type raw_error =
  | AbstractTypeNotAllowed
  | AddImplicitAssumeNewQualifier
  | AdmitWithoutDefinition
  | AssumedDeclNotAllowed
  | BothValLetInInterface
  | CachedFile
  | CardinalityConstraintViolated
  | ComputedTypeNotMatchAnnotation
  | ConstructorFailedCheck
  | ConstructorNotFound
  | ConstsructorBuildWrongType
  | DefinitionNotFound
  | DefinitionNotTranslated
  | DependencyAnalysisFailed
  | DependencyFound
  | DeprecatedEqualityOnBinder
  | DeprecatedOpaqueQualifier
  | DisjuctivePatternVarsMismatch
  | DocOverwrite
  | DuplicateInImplementation
  | DuplicateTypeAnnotationAndValDecl
  | ExpectTermGotFunction
  | ExpectedGhostExpression
  | ExpectedPureExpression
  | FailToCompileNativeTactic
  | Fatal_AbstractTypeDeclarationInInterface
  | Fatal_ActionMustHaveFunctionType
  | Fatal_AlreadyDefinedTopLevelDeclaration
  | Fatal_ArgumentLengthMismatch
  | Fatal_AssertionFailure
  | Fatal_AssignToImmutableValues
  | Fatal_AssumeValInInterface
  | Fatal_BadSignatureShape
  | Fatal_BadlyInstantiatedSynthByTactic
  | Fatal_BinderAndArgsLengthMismatch
  | Fatal_BothValAndLetInInterface
  | Fatal_CallNotImplemented
  | Fatal_ComputationNotTotal
  | Fatal_ComputationTypeNotAllowed
  | Fatal_ConstructorArgLengthMismatch
  | Fatal_CycleInRecTypeAbbreviation
  | Fatal_DataContructorNotFound
  | Fatal_DefaultQualifierNotAllowedOnEffects
  | Fatal_DivergentComputationCannotBeIncludedInTotal
  | Fatal_DuplicateModuleOrInterface
  | Fatal_DuplicateTopLevelNames
  | Fatal_EffectCannotBeReified
  | Fatal_EffectConstructorNotFullyApplied
  | Fatal_EffectNotFound
  | Fatal_EffectfulAndPureComputationMismatch
  | Fatal_EffectsCannotBeComposed
  | Fatal_ErrorInSolveDeferredConstraints
  | Fatal_ErrorsReported
  | Fatal_EscapedBoundVar
  | Fatal_ExpectNormalizedEffect
  | Fatal_ExpectTrivialPreCondition
  | Fatal_ExpectedArrowAnnotatedType
  | Fatal_FailToProcessPragma
  | Fatal_FailToResolveImplicitArgument
  | Fatal_FailToSolveUniverseInEquality
  | Fatal_Fatal_NonSingletonTopLevelModule
  | Fatal_Fatal_UnexpectedTermInUniverse
  | Fatal_Fatal_UnexpectedTermType
  | Fatal_FieldsNotBelongToSameRecordType
  | Fatal_ForbiddenReferenceToCurrentModule
  | Fatal_IdentifierNotFound
  | Fatal_IllAppliedConstant
  | Fatal_IllegalCharInOperatorName
  | Fatal_ImpossiblePrePostAbs
  | Fatal_ImpossiblePrePostArrow
  | Fatal_ImpossibleToGenerateDMEffect
  | Fatal_IncludeModuleNotPrepared
  | Fatal_IncoherentInlineUniverse
  | Fatal_IncompatibleNumberOfTypes
  | Fatal_IncompatibleSetOfUniverse
  | Fatal_IncompatibleUniverse
  | Fatal_InconsistentImplicitArgumentAnnotation
  | Fatal_InconsistentImplicitQualifier
  | Fatal_InconsistentQualifierAnnotation
  | Fatal_InlineRenamedAsUnfold
  | Fatal_InsufficientPatternArguments
  | Fatal_InterfaceAlreadyProcessed
  | Fatal_InterfaceNotImplementedByModule
  | Fatal_InvalidIdentifier
  | Fatal_InvalidLemmaArgument
  | Fatal_InvalidRedefinitionOfLexT
  | Fatal_InvalidUnicodeInStringLiteral
  | Fatal_LetBoundMonadicMismatch
  | Fatal_LetMutableForVariablesOnly
  | Fatal_LetRecArgumentMismatch
  | Fatal_MalformedActionDeclaration
  | Fatal_MismatchUniversePolymorphic
  | Fatal_MismatchedPatternType
  | Fatal_MissingDataConstructor
  | Fatal_MissingExposeInterfacesOption
  | Fatal_MissingFieldInRecord
  | Fatal_MissingImplementation
  | Fatal_MissingImplicitArguments
  | Fatal_MissingInterface
  | Fatal_MissingInterfaceOrImplementation
  | Fatal_MissingNameInBinder
  | Fatal_MissingQuantifierBinder
  | Fatal_ModuleExpected
  | Fatal_ModuleFirstStatement
  | Fatal_ModuleNotFound
  | Fatal_ModuleOrFileNotFound
  | Fatal_ModuleOrFileNotFoundWarning
  | Fatal_MonadAlreadyDefined
  | Fatal_MoreThanOneDeclaration
  | Fatal_MultipleLetBinding
  | Fatal_NameSpaceNotFound
  | Fatal_NegativeUniverseConstFatal_NotSupported
  | Fatal_NonInductiveInMutuallyDefinedType
  | Fatal_NonLinearPatternNotPermitted
  | Fatal_NonSingletonTopLevel
  | Fatal_NonTrivialPreConditionInPrims
  | Fatal_NonVaribleInductiveTypeParameter
  | Fatal_NotApplicationOrFv
  | Fatal_NotEnoughArgumentsForEffect
  | Fatal_NotFunctionType
  | Fatal_NotSupported
  | Fatal_NotTopLevelModule
  | Fatal_NotValidFStarFile
  | Fatal_NotValidIncludeDirectory
  | Fatal_OneModulePerFile
  | Fatal_OpenGoalsInSynthesis
  | Fatal_ParseErrors
  | Fatal_PreModuleMismatch
  | Fatal_QulifierListNotPermitted
  | Fatal_RecursiveFunctionLiteral
  | Fatal_ReflectOnlySupportedOnEffects
  | Fatal_ReservedPrefix
  | Fatal_SynthByTacticError
  | Fatal_TacticGotStuck
  | Fatal_TcOneFragmentFailed
  | Fatal_TermOutsideOfDefLanguage
  | Fatal_ToManyArgumentToFunction
  | Fatal_TooManyOrTooFewFileMatch
  | Fatal_TooManyPatternArguments
  | Fatal_TooManyUniverse
  | Fatal_TypeMismatch
  | Fatal_TypeWithinPatternsAllowedOnVariablesOnly
  | Fatal_UnableToReadFile
  | Fatal_UnepxectedOrUnboundOperator
  | Fatal_UnexpectedBindShape
  | Fatal_UnexpectedBinder
  | Fatal_UnexpectedChar
  | Fatal_UnexpectedComputationTypeForLetRec
  | Fatal_UnexpectedConstructorType
  | Fatal_UnexpectedDataConstructor
  | Fatal_UnexpectedEmptyRecord
  | Fatal_UnexpectedGTotForLetRec
  | Fatal_UnexpectedGeneralizedUniverse
  | Fatal_UnexpectedGuard
  | Fatal_UnexpectedIdentifier
  | Fatal_UnexpectedImplictArgument
  | Fatal_UnexpectedInductivetype
  | Fatal_UnexpectedLetBinding
  | Fatal_UnexpectedModuleDeclaration
  | Fatal_UnexpectedNumberOfUniverse
  | Fatal_UnexpectedNumericLiteral
  | Fatal_UnexpectedOperatorSymbol
  | Fatal_UnexpectedPattern
  | Fatal_UnexpectedPosition
  | Fatal_UnexpectedReturnShape
  | Fatal_UnexpectedTerm
  | Fatal_UnexpectedUniversePolymorphicReturn
  | Fatal_UnexpectedUniverseVariable
  | Fatal_UnfoldableDeprecated
  | Fatal_UniverseMightContainSumOfTwoUnivVars
  | Fatal_UniversePolymorphicInnerLetBound
  | Fatal_UnknownAttribute
  | Fatal_UnknownToolForDep
  | Fatal_UnrecognizedExtension
  | Fatal_UnresolvedPatternVar
  | Fatal_UnsupportedConstant
  | Fatal_UnsupportedDisjuctivePatterns
  | Fatal_UnsupportedQualifier
  | Fatal_WrongBodyTypeForReturnWP
  | Fatal_WrongDataAppHeadFormat
  | Fatal_WrongDefinitionOrder
  | Fatal_WrongResultTypeAfterConstrutor
  | Fatal_WrongTerm
  | FileNotWritten
  | Filtered
  | FreeVariables of string
  | FunctionLiteralPrecisionLoss
  | FunctionNotExtacted
  | FunctionTypeExpected
  | HintFailedToReplayProof
  | HitReplayFailed
  | IDEIgnoreCodeGen
  | IDETooManyPops
  | IDEUnrecognized of string
  | IllFormedGoal
  | IllTyped of string
  | IllegalCharInByteArray
  | ImpossibleAbbrevLidBundle
  | ImpossibleAbbrevRenameBundle
  | ImpossibleInductiveWithAbbrev
  | ImpossibleTypeAbbrevBundle
  | ImpossibleTypeAbbrevSigeltBundle
  | InaccessibleArgument
  | IncoherentImplicitQualifier
  | IncompatibleKinds
  | InductiveTypeNotSatisfyPositivityCondition
  | InferredTypeCauseVarEscape
  | InterfaceWithTypeImplementation
  | InvalidFSDocKeyword
  | InvalidFloatingPointNumber
  | InvalidNumericLiteral
  | InvalidUTF8Encoding
  | InvalidUniverseVar
  | IrrelevantQualifierOnArgumentToReflect
  | IrrelevantQualifierOnArgumentToReify
  | LetOpenModuleOnly
  | MalformedWarnErrorList
  | MetaAlienNotATmUnknown
  | MissingFileName
  | MissingPrimsModule
  | ModuleFileNameMismatch
  | ModuleFileNotFound
  | MultipleAscriptions
  | Fatal_NameNotFound
  | NoFileProvided
  | NonLinearPatternVars
  | NonListLiteralSMTPattern
  | NonTopRecFunctionNotFullyEncoded
  | NondependentUserDefinedDataType
  | NormalizationFailure
  | NotDependentArrow
  | NotEmbedded of string (* the nature of the term *)
  | NotEnoughArgsToEffect
  | OpPlusInUniverse
  | OptionsNotCompatible
  | OutOfOrder
  | OutOfRange of string (* the type of the integer *)
  | ParseItError
  | PatternMissingBoundVar
  | PolyTypeExpected
  | PossibleInfiniteTyp
  | ProofObligationFailed
  | RecursiveDependency
  | RedundantExplicitCurrying
  | SMTOutputParseError
  | SMTPatTDeprecated
  | SMTPatternMissingBoundVar
  | SMTSolverError
  | SyntaxError
  | TooManyFiles
  | TopLevelEffect
  | TypeCheckerFailToProve
  | TypeError
  | UnExpectedPreCondition
  | UnboundModuleReference
  | UncontrainedUnificationVar
  | UnexpectedEffect
  | UnexpectedExpressionType
  | UnexpectedFile
  | UnexpectedFsTypApp
  | UnexpectedFunctionParameterType
  | UnexpectedGTotComputation
  | UnexpectedImplicitArgument
  | UnexpectedInstance
  | UnexpectedSignatureForMonad
  | UnexpectedZ3Output
  | UnificationNotWellFormed
  | Uninstantiated
  | UninstantiatedUnificationVarInTactic
  | UninstantiatedVarInTactic
  | UnknownFatal_AssertionFailure
  | UnprotectedTerm
  | UnrecognizedAttribute
  | UpperBoundCandidateAlreadyVisited
  | UseDefaultEffect
  | UserTacticFailure
  | ValueRestriction
  | Fatal_VariableNotFound
  | WhenClauseFatal_NotSupported
  | WrongErrorLocation
  | Z3InvocationError
  | Z3InvocationWarning
  | Z3SolverError

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
  (* the errors below are default to error *)
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
  | UnknownFatal_AssertionFailure -> 12
  | Fatal_AssertionFailure -> 13
  | Fatal_MissingInterface -> 14
  | Fatal_MissingImplementation -> 15
  | Fatal_TooManyOrTooFewFileMatch -> 16
  | Fatal_CallNotImplemented -> 17
  | IDEUnrecognized _ -> 18
  | DependencyAnalysisFailed -> 19
  | ModuleFileNameMismatch -> 20
  (* the errors below are default to warning *)
  | Fatal_ModuleOrFileNotFoundWarning -> 21
  | UnboundModuleReference -> 22
  | UnprotectedTerm -> 23
  | NotEmbedded _ -> 24
  | FunctionLiteralPrecisionLoss -> 25
  | NonListLiteralSMTPattern -> 26
  | SMTPatternMissingBoundVar -> 27
  | Fatal_UnexpectedConstructorType -> 28
  | Z3InvocationWarning -> 29
  | UnexpectedZ3Output -> 30
  | InaccessibleArgument -> 31
  | DocOverwrite -> 32
  | AdmitWithoutDefinition -> 33
  | DeprecatedOpaqueQualifier -> 34
  | UseDefaultEffect -> 35
  | AddImplicitAssumeNewQualifier -> 36
  | TopLevelEffect -> 37
  | MetaAlienNotATmUnknown -> 38
  | PatternMissingBoundVar -> 39
  | IrrelevantQualifierOnArgumentToReify -> 40
  | IrrelevantQualifierOnArgumentToReflect -> 41
  | RedundantExplicitCurrying -> 42
  | HintFailedToReplayProof -> 43
  | HitReplayFailed -> 44
  | SMTPatTDeprecated -> 45
  | CachedFile -> 46
  | FileNotWritten -> 47
  | IllFormedGoal -> 48
  | MalformedWarnErrorList -> 49
  | IDEIgnoreCodeGen -> 50
  | Fatal_MissingInterfaceOrImplementation -> 51
  | UnexpectedFile -> 52
  | WrongErrorLocation -> 53
  | DeprecatedEqualityOnBinder -> 54
  | UnexpectedFsTypApp -> 55
  | UpperBoundCandidateAlreadyVisited -> 56
  | DefinitionNotTranslated -> 57
  | FunctionNotExtacted -> 58
  | UnrecognizedAttribute -> 59
  | NotDependentArrow -> 60
  | NondependentUserDefinedDataType -> 61
  | IncoherentImplicitQualifier -> 62
  | DependencyFound -> 63
  | MultipleAscriptions -> 64
  | RecursiveDependency -> 65
  | NormalizationFailure -> 66
  | Filtered -> 67
  (* when new entries are added, need to update "next_errno" and default "warn_error" in Options.fs *)
  | _ -> 0 (** Things that cannot be silenced! *)

type flag =
  | CError | CWarning | CSilent

let next_errno = 68 // the number needs to match the number of entries in "errno_of_error"
let flags: ref<list<flag>> = mk_ref []

let update_flags l =
  let compare (_, (a, _)) (_, (b, _)) =
    if a > b then 1
    else if a < b then -1
    else 0
  in
  let rec set_flag i l=
    match l with
    | [] -> List.nth !flags i
    | (f, (l, h))::tl ->
      if (i>=l && i <= h) then f
      else if (i<l) then List.nth !flags i
      else set_flag i tl
  in
  let rec aux f i l sorted = match l with
    | [] -> f
    | hd::tl -> aux (f@[set_flag i sorted]) (i+1) tl sorted
  in
  let rec init_flags l i =
    if i > 0 then init_flags (l@[CError]) (i-1) else l
  in
  let rec compute_range result l = match l with
    | [] -> result
    | (f, s)::tl ->
      let r = Util.split s ".." in
      let (l,h) = match r with
        | [r1; r2] -> (int_of_string r1, int_of_string r2)
        | _ -> failwith (BU.format1 "Malformed warn-error range %s" s)
      in
      if (l < 0)  || (h > next_errno)  then  failwith (BU.format2 "No error for warn_error %s..%s" (string_of_int l) (string_of_int h));
      compute_range (result@[(f, (l, h))]) tl
  in
  if !flags = [] then flags := init_flags [] next_errno;
  if l <> [] then
    let range = compute_range [] l in
    let sorted = List.sortWith compare range in
    flags := aux [] 0 !flags sorted

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

let maybe_fatal_err e =
  maybe_fatal_error Range.dummyRange e

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

