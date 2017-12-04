#light "off"
module FStar.Errors
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Util
open FStar.Range

type raw_error =
  | AbstractTypeNotAllowed
  | Warning_AddImplicitAssumeNewQualifier
  | Warning_AdmitWithoutDefinition
  | AssumedDeclNotAllowed
  | BothValLetInInterface
  | Warning_CachedFile
  | CardinalityConstraintViolated
  | ComputedTypeNotMatchAnnotation
  | ConstructorFailedCheck
  | ConstructorNotFound
  | ConstsructorBuildWrongType
  | DefinitionNotFound
  | Warning_DefinitionNotTranslated
  | Error_DependencyAnalysisFailed
  | Warning_DependencyFound
  | Warning_DeprecatedEqualityOnBinder
  | Warning_DeprecatedOpaqueQualifier
  | DisjuctivePatternVarsMismatch
  | Warning_DocOverwrite
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
  | Warning_FileNotWritten
  | Warning_Filtered
  | FreeVariables of string
  | Warning_FunctionLiteralPrecisionLoss
  | Warning_FunctionNotExtacted
  | FunctionTypeExpected
  | Warning_HintFailedToReplayProof
  | Warning_HitReplayFailed
  | Warning_IDEIgnoreCodeGen
  | IDETooManyPops
  | Error_IDEUnrecognized of string
  | Warning_IllFormedGoal
  | IllTyped of string
  | IllegalCharInByteArray
  | ImpossibleAbbrevLidBundle
  | ImpossibleAbbrevRenameBundle
  | ImpossibleInductiveWithAbbrev
  | ImpossibleTypeAbbrevBundle
  | ImpossibleTypeAbbrevSigeltBundle
  | Warning_InaccessibleArgument
  | Warning_IncoherentImplicitQualifier
  | IncompatibleKinds
  | Error_InductiveTypeNotSatisfyPositivityCondition
  | InferredTypeCauseVarEscape
  | InterfaceWithTypeImplementation
  | InvalidFSDocKeyword
  | InvalidFloatingPointNumber
  | InvalidNumericLiteral
  | InvalidUTF8Encoding
  | Error_InvalidUniverseVar
  | Warning_IrrelevantQualifierOnArgumentToReflect
  | Warning_IrrelevantQualifierOnArgumentToReify
  | LetOpenModuleOnly
  | Warning_MalformedWarnErrorList
  | Warning_MetaAlienNotATmUnknown
  | MissingFileName
  | MissingPrimsModule
  | Error_ModuleFileNameMismatch
  | ModuleFileNotFound
  | Warning_MultipleAscriptions
  | Fatal_NameNotFound
  | NoFileProvided
  | NonLinearPatternVars
  | Warning_NonListLiteralSMTPattern
  | NonTopRecFunctionNotFullyEncoded
  | Warning_NondependentUserDefinedDataType
  | Warning_NormalizationFailure
  | Warning_NotDependentArrow
  | Warning_NotEmbedded of string (* the nature of the term *)
  | NotEnoughArgsToEffect
  | Error_OpPlusInUniverse
  | OptionsNotCompatible
  | OutOfOrder
  | Error_OutOfRange of string (* the type of the integer *)
  | ParseItError
  | Warning_PatternMissingBoundVar
  | PolyTypeExpected
  | PossibleInfiniteTyp
  | Error_ProofObligationFailed
  | Warning_RecursiveDependency
  | Warning_RedundantExplicitCurrying
  | SMTOutputParseError
  | Warning_SMTPatTDeprecated
  | Warning_SMTPatternMissingBoundVar
  | SMTSolverError
  | SyntaxError
  | TooManyFiles
  | Warning_TopLevelEffect
  | Error_TypeCheckerFailToProve
  | Error_TypeError
  | UnExpectedPreCondition
  | Warning_UnboundModuleReference
  | Error_UncontrainedUnificationVar
  | UnexpectedEffect
  | UnexpectedExpressionType
  | Warning_UnexpectedFile
  | Warning_UnexpectedFsTypApp
  | UnexpectedFunctionParameterType
  | Error_UnexpectedGTotComputation
  | UnexpectedImplicitArgument
  | Error_UnexpectedInstance
  | UnexpectedSignatureForMonad
  | Warning_UnexpectedZ3Output
  | UnificationNotWellFormed
  | Uninstantiated
  | UninstantiatedUnificationVarInTactic
  | UninstantiatedVarInTactic
  | Error_UnknownFatal_AssertionFailure
  | Warning_UnprotectedTerm
  | Warning_UnrecognizedAttribute
  | Warning_UpperBoundCandidateAlreadyVisited
  | Warning_UseDefaultEffect
  | UserTacticFailure
  | ValueRestriction
  | Fatal_VariableNotFound
  | WhenClauseFatal_NotSupported
  | Warning_WrongErrorLocation
  | Error_Z3InvocationError
  | Warning_Z3InvocationWarning
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
  | Error_OutOfRange _ -> 1
  | Error_OpPlusInUniverse -> 2
  | Error_InvalidUniverseVar -> 3
  | Error_Z3InvocationError -> 4
  | Error_TypeError -> 5
  | Error_TypeCheckerFailToProve -> 6
  | Error_InductiveTypeNotSatisfyPositivityCondition -> 7
  | Error_UncontrainedUnificationVar -> 8
  | Error_UnexpectedGTotComputation -> 9
  | Error_UnexpectedInstance -> 10
  | Error_ProofObligationFailed -> 11
  | Error_UnknownFatal_AssertionFailure -> 12
  | Fatal_AssertionFailure -> 13
  | Fatal_MissingInterface -> 14
  | Fatal_MissingImplementation -> 15
  | Fatal_TooManyOrTooFewFileMatch -> 16
  | Fatal_CallNotImplemented -> 17
  | Error_IDEUnrecognized _ -> 18
  | Error_DependencyAnalysisFailed -> 19
  | Error_ModuleFileNameMismatch -> 20
  (* the errors below are default to warning *)
  | Fatal_ModuleOrFileNotFoundWarning -> 21
  | Warning_UnboundModuleReference -> 22
  | Warning_UnprotectedTerm -> 23
  | Warning_NotEmbedded _ -> 24
  | Warning_FunctionLiteralPrecisionLoss -> 25
  | Warning_NonListLiteralSMTPattern -> 26
  | Warning_SMTPatternMissingBoundVar -> 27
  | Fatal_UnexpectedConstructorType -> 28
  | Warning_Z3InvocationWarning -> 29
  | Warning_UnexpectedZ3Output -> 30
  | Warning_InaccessibleArgument -> 31
  | Warning_DocOverwrite -> 32
  | Warning_AdmitWithoutDefinition -> 33
  | Warning_DeprecatedOpaqueQualifier -> 34
  | Warning_UseDefaultEffect -> 35
  | Warning_AddImplicitAssumeNewQualifier -> 36
  | Warning_TopLevelEffect -> 37
  | Warning_MetaAlienNotATmUnknown -> 38
  | Warning_PatternMissingBoundVar -> 39
  | Warning_IrrelevantQualifierOnArgumentToReify -> 40
  | Warning_IrrelevantQualifierOnArgumentToReflect -> 41
  | Warning_RedundantExplicitCurrying -> 42
  | Warning_HintFailedToReplayProof -> 43
  | Warning_HitReplayFailed -> 44
  | Warning_SMTPatTDeprecated -> 45
  | Warning_CachedFile -> 46
  | Warning_FileNotWritten -> 47
  | Warning_IllFormedGoal -> 48
  | Warning_MalformedWarnErrorList -> 49
  | Warning_IDEIgnoreCodeGen -> 50
  | Fatal_MissingInterfaceOrImplementation -> 51
  | Warning_UnexpectedFile -> 52
  | Warning_WrongErrorLocation -> 53
  | Warning_DeprecatedEqualityOnBinder -> 54
  | Warning_UnexpectedFsTypApp -> 55
  | Warning_UpperBoundCandidateAlreadyVisited -> 56
  | Warning_DefinitionNotTranslated -> 57
  | Warning_FunctionNotExtacted -> 58
  | Warning_UnrecognizedAttribute -> 59
  | Warning_NotDependentArrow -> 60
  | Warning_NondependentUserDefinedDataType -> 61
  | Warning_IncoherentImplicitQualifier -> 62
  | Warning_DependencyFound -> 63
  | Warning_MultipleAscriptions -> 64
  | Warning_RecursiveDependency -> 65
  | Warning_NormalizationFailure -> 66
  | Warning_Filtered -> 67
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

