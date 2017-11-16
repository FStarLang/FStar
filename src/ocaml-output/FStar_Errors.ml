open Prims
type raw_error =
  | ReservedPrefix
  | NotValidFStarFile
  | NotValidIncludeDirectory
  | ModuleFileNotFound
  | UnknowToolForDep
  | UnrecognizedExtension
  | UnableToReadFile
  | Uninstantiated
  | IllTyped of Prims.string
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
  | OutOfRange of Prims.string
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
  | NotEmbedded of Prims.string
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
  | FreeVariables of Prims.string
  | UnexpectedInductivetype
  | IllFormedGoal
  | CachedFile
  | FileNotWritten
  | InvalidUTF8Encoding
  | FailToCompileNativeTactic[@@deriving show]
let uu___is_ReservedPrefix: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ReservedPrefix  -> true | uu____20 -> false
let uu___is_NotValidFStarFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NotValidFStarFile  -> true | uu____24 -> false
let uu___is_NotValidIncludeDirectory: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NotValidIncludeDirectory  -> true
    | uu____28 -> false
let uu___is_ModuleFileNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleFileNotFound  -> true | uu____32 -> false
let uu___is_UnknowToolForDep: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnknowToolForDep  -> true | uu____36 -> false
let uu___is_UnrecognizedExtension: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnrecognizedExtension  -> true | uu____40 -> false
let uu___is_UnableToReadFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnableToReadFile  -> true | uu____44 -> false
let uu___is_Uninstantiated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Uninstantiated  -> true | uu____48 -> false
let uu___is_IllTyped: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IllTyped _0 -> true | uu____53 -> false
let __proj__IllTyped__item___0: raw_error -> Prims.string =
  fun projectee  -> match projectee with | IllTyped _0 -> _0
let uu___is_ValueRestriction: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ValueRestriction  -> true | uu____64 -> false
let uu___is_UnexpectedEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedEffect  -> true | uu____68 -> false
let uu___is_NotTopLevelModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NotTopLevelModule  -> true | uu____72 -> false
let uu___is_NonSingletonTopLevel: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NonSingletonTopLevel  -> true | uu____76 -> false
let uu___is_MissingPrimsModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | MissingPrimsModule  -> true | uu____80 -> false
let uu___is_IDEMissingFileName: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IDEMissingFileName  -> true | uu____84 -> false
let uu___is_IDETooManyFiels: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IDETooManyFiels  -> true | uu____88 -> false
let uu___is_NotSupported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NotSupported  -> true | uu____92 -> false
let uu___is_OptionsNotCompatible: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | OptionsNotCompatible  -> true | uu____96 -> false
let uu___is_NoFileProvided: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NoFileProvided  -> true | uu____100 -> false
let uu___is_NonSingletonTopLevelModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonSingletonTopLevelModule  -> true
    | uu____104 -> false
let uu___is_PreModuleMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | PreModuleMismatch  -> true | uu____108 -> false
let uu___is_ModuleFirstStatement: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleFirstStatement  -> true | uu____112 -> false
let uu___is_ParseErrors: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ParseErrors  -> true | uu____116 -> false
let uu___is_MultipleLetBinding: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | MultipleLetBinding  -> true | uu____120 -> false
let uu___is_UnexpectedIdentifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedIdentifier  -> true | uu____124 -> false
let uu___is_InlineRenamedAsUnfold: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InlineRenamedAsUnfold  -> true
    | uu____128 -> false
let uu___is_UnfoldableDeprecated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnfoldableDeprecated  -> true | uu____132 -> false
let uu___is_DeprecatedEqualityOnBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DeprecatedEqualityOnBinder  -> true
    | uu____136 -> false
let uu___is_MissingQuantifierBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingQuantifierBinder  -> true
    | uu____140 -> false
let uu___is_OutOfRange: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | OutOfRange _0 -> true | uu____145 -> false
let __proj__OutOfRange__item___0: raw_error -> Prims.string =
  fun projectee  -> match projectee with | OutOfRange _0 -> _0
let uu___is_OpPlusInUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | OpPlusInUniverse  -> true | uu____156 -> false
let uu___is_InvalidUniverseVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | InvalidUniverseVar  -> true | uu____160 -> false
let uu___is_InvalidIdentifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | InvalidIdentifier  -> true | uu____164 -> false
let uu___is_MoreThanOneDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MoreThanOneDeclaration  -> true
    | uu____168 -> false
let uu___is_Filtered: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Filtered  -> true | uu____172 -> false
let uu___is_UnexpectedModuleDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedModuleDeclaration  -> true
    | uu____176 -> false
let uu___is_UnexpectedOperatorSymbol: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedOperatorSymbol  -> true
    | uu____180 -> false
let uu___is_UnexpectedTerm: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedTerm  -> true | uu____184 -> false
let uu___is_ModuleFileNameMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ModuleFileNameMismatch  -> true
    | uu____188 -> false
let uu___is_LetOpenModuleOnly: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | LetOpenModuleOnly  -> true | uu____192 -> false
let uu___is_ModuleOrFileNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleOrFileNotFound  -> true | uu____196 -> false
let uu___is_ModuleOrFileNotFoundWarning: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ModuleOrFileNotFoundWarning  -> true
    | uu____200 -> false
let uu___is_UnboundModuleReference: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnboundModuleReference  -> true
    | uu____204 -> false
let uu___is_OneModulePerFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | OneModulePerFile  -> true | uu____208 -> false
let uu___is_SyntaxError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxError  -> true | uu____212 -> false
let uu___is_ParseItError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ParseItError  -> true | uu____216 -> false
let uu___is_ModuleExpected: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleExpected  -> true | uu____220 -> false
let uu___is_DefinitionNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | DefinitionNotFound  -> true | uu____224 -> false
let uu___is_AbstractTypeNotAllowed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AbstractTypeNotAllowed  -> true
    | uu____228 -> false
let uu___is_DuplicateInImplementation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DuplicateInImplementation  -> true
    | uu____232 -> false
let uu___is_InterfaceWithTypeImplementation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InterfaceWithTypeImplementation  -> true
    | uu____236 -> false
let uu___is_BothValLetInInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | BothValLetInInterface  -> true
    | uu____240 -> false
let uu___is_AssumedDeclNotAllowed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AssumedDeclNotAllowed  -> true
    | uu____244 -> false
let uu___is_OutOfOrder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | OutOfOrder  -> true | uu____248 -> false
let uu___is_IllegalCharInByteArray: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IllegalCharInByteArray  -> true
    | uu____252 -> false
let uu___is_IllegalCharInOperatorName: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IllegalCharInOperatorName  -> true
    | uu____256 -> false
let uu___is_InvalidFloatingPointNumber: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidFloatingPointNumber  -> true
    | uu____260 -> false
let uu___is_InvalidNumericLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidNumericLiteral  -> true
    | uu____264 -> false
let uu___is_InvalidUnicodeInStringLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidUnicodeInStringLiteral  -> true
    | uu____268 -> false
let uu___is_InvalidFSDocKeyword: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | InvalidFSDocKeyword  -> true | uu____272 -> false
let uu___is_UnexpectedChar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedChar  -> true | uu____276 -> false
let uu___is_UnexpectedPosition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedPosition  -> true | uu____280 -> false
let uu___is_UnprotectedTerm: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnprotectedTerm  -> true | uu____284 -> false
let uu___is_NotEmbedded: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEmbedded _0 -> true | uu____289 -> false
let __proj__NotEmbedded__item___0: raw_error -> Prims.string =
  fun projectee  -> match projectee with | NotEmbedded _0 -> _0
let uu___is_FunctionLiteralPrecisionLoss: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | FunctionLiteralPrecisionLoss  -> true
    | uu____300 -> false
let uu___is_NonTopRecFunctionNotFullyEncoded: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonTopRecFunctionNotFullyEncoded  -> true
    | uu____304 -> false
let uu___is_NonListLiteralSMTPattern: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonListLiteralSMTPattern  -> true
    | uu____308 -> false
let uu___is_SMTPatternMissingBoundVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | SMTPatternMissingBoundVar  -> true
    | uu____312 -> false
let uu___is_NonVaribleInductiveTypeParameter: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonVaribleInductiveTypeParameter  -> true
    | uu____316 -> false
let uu___is_UnexpectedConstructorType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedConstructorType  -> true
    | uu____320 -> false
let uu___is_SMTSolverError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | SMTSolverError  -> true | uu____324 -> false
let uu___is_Z3InvocationError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3InvocationError  -> true | uu____328 -> false
let uu___is_Z3InvocationWarning: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3InvocationWarning  -> true | uu____332 -> false
let uu___is_SMTOutputParseError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | SMTOutputParseError  -> true | uu____336 -> false
let uu___is_UnexpectedZ3Output: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedZ3Output  -> true | uu____340 -> false
let uu___is_CycleInRecTypeAbbreviation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CycleInRecTypeAbbreviation  -> true
    | uu____344 -> false
let uu___is_ImpossibleAbbrevLidBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossibleAbbrevLidBundle  -> true
    | uu____348 -> false
let uu___is_ImpossibleAbbrevRenameBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossibleAbbrevRenameBundle  -> true
    | uu____352 -> false
let uu___is_ImpossibleTypeAbbrevSigeltBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossibleTypeAbbrevSigeltBundle  -> true
    | uu____356 -> false
let uu___is_ImpossibleTypeAbbrevBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossibleTypeAbbrevBundle  -> true
    | uu____360 -> false
let uu___is_ImpossibleInductiveWithAbbrev: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossibleInductiveWithAbbrev  -> true
    | uu____364 -> false
let uu___is_InaccessibleArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | InaccessibleArgument  -> true | uu____368 -> false
let uu___is_WrongDataAppHeadFormat: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | WrongDataAppHeadFormat  -> true
    | uu____372 -> false
let uu___is_TacticGotStuck: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | TacticGotStuck  -> true | uu____376 -> false
let uu___is_UserTacticFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UserTacticFailure  -> true | uu____380 -> false
let uu___is_OpenGoalsInSynthesis: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | OpenGoalsInSynthesis  -> true | uu____384 -> false
let uu___is_UninstantiatedVarInTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UninstantiatedVarInTactic  -> true
    | uu____388 -> false
let uu___is_ForbiddenReferenceToCurrentModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ForbiddenReferenceToCurrentModule  -> true
    | uu____392 -> false
let uu___is_DuplicateTopLevelNames: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DuplicateTopLevelNames  -> true
    | uu____396 -> false
let uu___is_NameSpaceNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NameSpaceNotFound  -> true | uu____400 -> false
let uu___is_IncludeModuleNotPrepared: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IncludeModuleNotPrepared  -> true
    | uu____404 -> false
let uu___is_ModuleNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ModuleNotFound  -> true | uu____408 -> false
let uu___is_DocOverwrite: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | DocOverwrite  -> true | uu____412 -> false
let uu___is_AdmitWithoutDefinition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AdmitWithoutDefinition  -> true
    | uu____416 -> false
let uu___is_DuplicateModuleOrInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DuplicateModuleOrInterface  -> true
    | uu____420 -> false
let uu___is_MonadAlreadyDefined: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | MonadAlreadyDefined  -> true | uu____424 -> false
let uu___is_IdentifierNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IdentifierNotFound  -> true | uu____428 -> false
let uu___is_AbstractTypeDeclarationInInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AbstractTypeDeclarationInInterface  -> true
    | uu____432 -> false
let uu___is_WrongDefinitionOrder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | WrongDefinitionOrder  -> true | uu____436 -> false
let uu___is_BothValAndLetInInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | BothValAndLetInInterface  -> true
    | uu____440 -> false
let uu___is_AssumeValInInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | AssumeValInInterface  -> true | uu____444 -> false
let uu___is_InterfaceNotImplementedByModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InterfaceNotImplementedByModule  -> true
    | uu____448 -> false
let uu___is_InterfaceAlreadyProcessed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InterfaceAlreadyProcessed  -> true
    | uu____452 -> false
let uu___is_DeprecatedOpaqueQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DeprecatedOpaqueQualifier  -> true
    | uu____456 -> false
let uu___is_ReflectOnlySupportedOnEffects: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ReflectOnlySupportedOnEffects  -> true
    | uu____460 -> false
let uu___is_DefaultQualifierNotAllowedOnEffects: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DefaultQualifierNotAllowedOnEffects  -> true
    | uu____464 -> false
let uu___is_UnsupportedQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnsupportedQualifier  -> true | uu____468 -> false
let uu___is_NegativeUniverseConstNotSupported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NegativeUniverseConstNotSupported  -> true
    | uu____472 -> false
let uu___is_UniverseMightContainSumOfTwoUnivVars: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UniverseMightContainSumOfTwoUnivVars  -> true
    | uu____476 -> false
let uu___is_FieldsNotBelongToSameRecordType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | FieldsNotBelongToSameRecordType  -> true
    | uu____480 -> false
let uu___is_LetMutableForVariablesOnly: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LetMutableForVariablesOnly  -> true
    | uu____484 -> false
let uu___is_TypeWithinPatternsAllowedOnVariablesOnly: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | TypeWithinPatternsAllowedOnVariablesOnly  -> true
    | uu____488 -> false
let uu___is_UnexpectedPattern: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedPattern  -> true | uu____492 -> false
let uu___is_UnexpectedNumericLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedNumericLiteral  -> true
    | uu____496 -> false
let uu___is_UnknownAttribute: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnknownAttribute  -> true | uu____500 -> false
let uu___is_UnepxectedOrUnboundOperator: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnepxectedOrUnboundOperator  -> true
    | uu____504 -> false
let uu___is_AssignToImmutableValues: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AssignToImmutableValues  -> true
    | uu____508 -> false
let uu___is_EffectNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | EffectNotFound  -> true | uu____512 -> false
let uu___is_DataContructorNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DataContructorNotFound  -> true
    | uu____516 -> false
let uu___is_ConstructorNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ConstructorNotFound  -> true | uu____520 -> false
let uu___is_UnsupportedDisjuctivePatterns: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnsupportedDisjuctivePatterns  -> true
    | uu____524 -> false
let uu___is_ComputationTypeNotAllowed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ComputationTypeNotAllowed  -> true
    | uu____528 -> false
let uu___is_UnexpectedEmptyRecord: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedEmptyRecord  -> true
    | uu____532 -> false
let uu___is_MissingFieldInRecord: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | MissingFieldInRecord  -> true | uu____536 -> false
let uu___is_InvalidLemmaArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | InvalidLemmaArgument  -> true | uu____540 -> false
let uu___is_NotEnoughArgsToEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NotEnoughArgsToEffect  -> true
    | uu____544 -> false
let uu___is_UnexpectedLetBinding: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedLetBinding  -> true | uu____548 -> false
let uu___is_UnexpectedTermInUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedTermInUniverse  -> true
    | uu____552 -> false
let uu___is_UnexpectedUniverseVariable: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedUniverseVariable  -> true
    | uu____556 -> false
let uu___is_UseDefaultEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UseDefaultEffect  -> true | uu____560 -> false
let uu___is_AddImplicitAssumeNewQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AddImplicitAssumeNewQualifier  -> true
    | uu____564 -> false
let uu___is_MissingNameInBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | MissingNameInBinder  -> true | uu____568 -> false
let uu___is_UnexpectedBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedBinder  -> true | uu____572 -> false
let uu___is_MalformedActionDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MalformedActionDeclaration  -> true
    | uu____576 -> false
let uu___is_ArgumentLengthMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ArgumentLengthMismatch  -> true
    | uu____580 -> false
let uu___is_WrongTerm: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | WrongTerm  -> true | uu____584 -> false
let uu___is_TermOutsideOfDefLanguage: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | TermOutsideOfDefLanguage  -> true
    | uu____588 -> false
let uu___is_LetBoundMonadicMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LetBoundMonadicMismatch  -> true
    | uu____592 -> false
let uu___is_TypeMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeMismatch  -> true | uu____596 -> false
let uu___is_EffectfulAndPureComputationMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | EffectfulAndPureComputationMismatch  -> true
    | uu____600 -> false
let uu___is_NotFunctionType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NotFunctionType  -> true | uu____604 -> false
let uu___is_BinderAndArgsLengthMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | BinderAndArgsLengthMismatch  -> true
    | uu____608 -> false
let uu___is_WhenClauseNotSupported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | WhenClauseNotSupported  -> true
    | uu____612 -> false
let uu___is_NameNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NameNotFound  -> true | uu____616 -> false
let uu___is_VariableNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | VariableNotFound  -> true | uu____620 -> false
let uu___is_EffectsCannotBeComposed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | EffectsCannotBeComposed  -> true
    | uu____624 -> false
let uu___is_DivergentComputationCannotBeIncludedInTotal:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DivergentComputationCannotBeIncludedInTotal  -> true
    | uu____628 -> false
let uu___is_ConstructorArgLengthMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ConstructorArgLengthMismatch  -> true
    | uu____632 -> false
let uu___is_NotEnoughArgumentsForEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NotEnoughArgumentsForEffect  -> true
    | uu____636 -> false
let uu___is_UnexpectedSignatureForMonad: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedSignatureForMonad  -> true
    | uu____640 -> false
let uu___is_ExpectTermGotFunction: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExpectTermGotFunction  -> true
    | uu____644 -> false
let uu___is_UnexpectedImplicitArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedImplicitArgument  -> true
    | uu____648 -> false
let uu___is_UnexpectedExpressionType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedExpressionType  -> true
    | uu____652 -> false
let uu___is_UnexpectedFunctionParameterType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedFunctionParameterType  -> true
    | uu____656 -> false
let uu___is_TypeError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeError  -> true | uu____660 -> false
let uu___is_PossibleInfiniteTyp: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | PossibleInfiniteTyp  -> true | uu____664 -> false
let uu___is_UnificationNotWellFormed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnificationNotWellFormed  -> true
    | uu____668 -> false
let uu___is_IncompatibleKinds: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IncompatibleKinds  -> true | uu____672 -> false
let uu___is_ConstsructorBuildWrongType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ConstsructorBuildWrongType  -> true
    | uu____676 -> false
let uu___is_ConstructorFailedCheck: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ConstructorFailedCheck  -> true
    | uu____680 -> false
let uu___is_DuplicateTypeAnnotationAndValDecl: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DuplicateTypeAnnotationAndValDecl  -> true
    | uu____684 -> false
let uu___is_InferredTypeCauseVarEscape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InferredTypeCauseVarEscape  -> true
    | uu____688 -> false
let uu___is_FunctionTypeExpected: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | FunctionTypeExpected  -> true | uu____692 -> false
let uu___is_PolyTypeExpected: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | PolyTypeExpected  -> true | uu____696 -> false
let uu___is_NonLinearPatternVars: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NonLinearPatternVars  -> true | uu____700 -> false
let uu___is_DisjuctivePatternVarsMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | DisjuctivePatternVarsMismatch  -> true
    | uu____704 -> false
let uu___is_ComputedTypeNotMatchAnnotation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ComputedTypeNotMatchAnnotation  -> true
    | uu____708 -> false
let uu___is_UnExpectedPreCondition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnExpectedPreCondition  -> true
    | uu____712 -> false
let uu___is_ExpectedPureExpression: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExpectedPureExpression  -> true
    | uu____716 -> false
let uu___is_ExpectedGhostExpression: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExpectedGhostExpression  -> true
    | uu____720 -> false
let uu___is_TypeCheckerFailToProve: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | TypeCheckerFailToProve  -> true
    | uu____724 -> false
let uu___is_TopLevelEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | TopLevelEffect  -> true | uu____728 -> false
let uu___is_CardinalityConstraintViolated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CardinalityConstraintViolated  -> true
    | uu____732 -> false
let uu___is_MetaAlienNotATmUnknow: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MetaAlienNotATmUnknow  -> true
    | uu____736 -> false
let uu___is_NotApplicationOrFv: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | NotApplicationOrFv  -> true | uu____740 -> false
let uu___is_InductiveTypeNotSatisfyPositivityCondition:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InductiveTypeNotSatisfyPositivityCondition  -> true
    | uu____744 -> false
let uu___is_PatternMissingBoundVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | PatternMissingBoundVar  -> true
    | uu____748 -> false
let uu___is_UncontrainedUnificationVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UncontrainedUnificationVar  -> true
    | uu____752 -> false
let uu___is_IrrelevantQualifierOnArgumentToReify: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IrrelevantQualifierOnArgumentToReify  -> true
    | uu____756 -> false
let uu___is_IrrelevantQualifierOnArgumentToReflect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IrrelevantQualifierOnArgumentToReflect  -> true
    | uu____760 -> false
let uu___is_RedundantExplicitCurrying: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | RedundantExplicitCurrying  -> true
    | uu____764 -> false
let uu___is_ActionMustHaveFunctionType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ActionMustHaveFunctionType  -> true
    | uu____768 -> false
let uu___is_InvalidRedefinitionOfLexT: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidRedefinitionOfLexT  -> true
    | uu____772 -> false
let uu___is_FailToProcessPragma: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | FailToProcessPragma  -> true | uu____776 -> false
let uu___is_EffectCannotBeReified: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | EffectCannotBeReified  -> true
    | uu____780 -> false
let uu___is_TooManyUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | TooManyUniverse  -> true | uu____784 -> false
let uu___is_InconsistentQualifierAnnotation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InconsistentQualifierAnnotation  -> true
    | uu____788 -> false
let uu___is_AlreadyDefinedTopLevelDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | AlreadyDefinedTopLevelDeclaration  -> true
    | uu____792 -> false
let uu___is_IncoherentInlineUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IncoherentInlineUniverse  -> true
    | uu____796 -> false
let uu___is_WrongResultTypeAfterConstrutor: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | WrongResultTypeAfterConstrutor  -> true
    | uu____800 -> false
let uu___is_NonInductiveInMutuallyDefinedType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonInductiveInMutuallyDefinedType  -> true
    | uu____804 -> false
let uu___is_UnexpectedComputationTypeForLetRec: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedComputationTypeForLetRec  -> true
    | uu____808 -> false
let uu___is_InsufficientPatternArguments: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InsufficientPatternArguments  -> true
    | uu____812 -> false
let uu___is_NonTrivialPreConditionInPrims: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonTrivialPreConditionInPrims  -> true
    | uu____816 -> false
let uu___is_EffectConstructorNotFullyApplied: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | EffectConstructorNotFullyApplied  -> true
    | uu____820 -> false
let uu___is_UnexpectedGeneralizedUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedGeneralizedUniverse  -> true
    | uu____824 -> false
let uu___is_MissingImplicitArguments: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingImplicitArguments  -> true
    | uu____828 -> false
let uu___is_IncompatibleNumberOfTypes: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IncompatibleNumberOfTypes  -> true
    | uu____832 -> false
let uu___is_QulifierListNotPermitted: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QulifierListNotPermitted  -> true
    | uu____836 -> false
let uu___is_UnexpectedDataConstructor: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedDataConstructor  -> true
    | uu____840 -> false
let uu___is_BadSignatureShape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | BadSignatureShape  -> true | uu____844 -> false
let uu___is_ComputationNotTotal: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ComputationNotTotal  -> true | uu____848 -> false
let uu___is_WrongBodyTypeForReturnWP: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | WrongBodyTypeForReturnWP  -> true
    | uu____852 -> false
let uu___is_UnexpectedReturnShape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedReturnShape  -> true
    | uu____856 -> false
let uu___is_UnexpectedBindShape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedBindShape  -> true | uu____860 -> false
let uu___is_ImpossibleToGenerateDMEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossibleToGenerateDMEffect  -> true
    | uu____864 -> false
let uu___is_ImpossiblePrePostArrow: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ImpossiblePrePostArrow  -> true
    | uu____868 -> false
let uu___is_ImpossiblePrePostAbs: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ImpossiblePrePostAbs  -> true | uu____872 -> false
let uu___is_ExpectNormalizedEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExpectNormalizedEffect  -> true
    | uu____876 -> false
let uu___is_IncompatibleUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IncompatibleUniverse  -> true | uu____880 -> false
let uu___is_FailToSolveUniverseInEquality: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | FailToSolveUniverseInEquality  -> true
    | uu____884 -> false
let uu___is_ErrorInSolveDeferredConstraints: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ErrorInSolveDeferredConstraints  -> true
    | uu____888 -> false
let uu___is_ExpectTrivialPreCondition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExpectTrivialPreCondition  -> true
    | uu____892 -> false
let uu___is_FailToResolveImplicitArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | FailToResolveImplicitArgument  -> true
    | uu____896 -> false
let uu___is_UnexpectedGTotComputation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedGTotComputation  -> true
    | uu____900 -> false
let uu___is_UnexpectedInstance: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedInstance  -> true | uu____904 -> false
let uu___is_IncompatibleSetOfUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | IncompatibleSetOfUniverse  -> true
    | uu____908 -> false
let uu___is_TooManyPatternArguments: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | TooManyPatternArguments  -> true
    | uu____912 -> false
let uu___is_UnexpectedUniversePolymorphicReturn: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedUniversePolymorphicReturn  -> true
    | uu____916 -> false
let uu___is_MismatchUniversePolymorphic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MismatchUniversePolymorphic  -> true
    | uu____920 -> false
let uu___is_EscapedBoundVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | EscapedBoundVar  -> true | uu____924 -> false
let uu___is_ExpectedArrowAnnotatedType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ExpectedArrowAnnotatedType  -> true
    | uu____928 -> false
let uu___is_SynthByTacticError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | SynthByTacticError  -> true | uu____932 -> false
let uu___is_MissingDataConstructor: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingDataConstructor  -> true
    | uu____936 -> false
let uu___is_BadlyInstantiatedSynthByTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | BadlyInstantiatedSynthByTactic  -> true
    | uu____940 -> false
let uu___is_UnexpectedNumberOfUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedNumberOfUniverse  -> true
    | uu____944 -> false
let uu___is_UnsupportedConstant: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnsupportedConstant  -> true | uu____948 -> false
let uu___is_InconsistentImplicitArgumentAnnotation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InconsistentImplicitArgumentAnnotation  -> true
    | uu____952 -> false
let uu___is_ToManyArgumentToFunction: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ToManyArgumentToFunction  -> true
    | uu____956 -> false
let uu___is_InconsistentImplicitQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InconsistentImplicitQualifier  -> true
    | uu____960 -> false
let uu___is_LetRecArgumentMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LetRecArgumentMismatch  -> true
    | uu____964 -> false
let uu___is_RecursiveFunctionLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | RecursiveFunctionLiteral  -> true
    | uu____968 -> false
let uu___is_UnexpectedGTotForLetRec: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedGTotForLetRec  -> true
    | uu____972 -> false
let uu___is_UnexpectedImplictArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedImplictArgument  -> true
    | uu____976 -> false
let uu___is_UnexpectedTermType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedTermType  -> true | uu____980 -> false
let uu___is_UniversePolymorphicInnerLetBound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UniversePolymorphicInnerLetBound  -> true
    | uu____984 -> false
let uu___is_UnresolvedPatternVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnresolvedPatternVar  -> true | uu____988 -> false
let uu___is_HintFailedToReplayProof: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | HintFailedToReplayProof  -> true
    | uu____992 -> false
let uu___is_HitReplayFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | HitReplayFailed  -> true | uu____996 -> false
let uu___is_ProofObligationFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | ProofObligationFailed  -> true
    | uu____1000 -> false
let uu___is_UnknowAssertionFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnknowAssertionFailure  -> true
    | uu____1004 -> false
let uu___is_Z3SolverError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3SolverError  -> true | uu____1008 -> false
let uu___is_UninstantiatedUnificationVarInTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UninstantiatedUnificationVarInTactic  -> true
    | uu____1012 -> false
let uu___is_AssertionFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | AssertionFailure  -> true | uu____1016 -> false
let uu___is_MissingInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | MissingInterface  -> true | uu____1020 -> false
let uu___is_MissingImplementation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingImplementation  -> true
    | uu____1024 -> false
let uu___is_TooManyOrTooFewFileMatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | TooManyOrTooFewFileMatch  -> true
    | uu____1028 -> false
let uu___is_UnexpectedGuard: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | UnexpectedGuard  -> true | uu____1032 -> false
let uu___is_ErrorsReported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | ErrorsReported  -> true | uu____1036 -> false
let uu___is_TcOneFragmentFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | TcOneFragmentFailed  -> true | uu____1040 -> false
let uu___is_MissingExposeInterfacesOption: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MissingExposeInterfacesOption  -> true
    | uu____1044 -> false
let uu___is_NonLinearPatternNotPermitted: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | NonLinearPatternNotPermitted  -> true
    | uu____1048 -> false
let uu___is_SMTPatTDeprecated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | SMTPatTDeprecated  -> true | uu____1052 -> false
let uu___is_IllAppliedConstant: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IllAppliedConstant  -> true | uu____1056 -> false
let uu___is_MismatchedPatternType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | MismatchedPatternType  -> true
    | uu____1060 -> false
let uu___is_FreeVariables: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | FreeVariables _0 -> true | uu____1065 -> false
let __proj__FreeVariables__item___0: raw_error -> Prims.string =
  fun projectee  -> match projectee with | FreeVariables _0 -> _0
let uu___is_UnexpectedInductivetype: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedInductivetype  -> true
    | uu____1076 -> false
let uu___is_IllFormedGoal: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | IllFormedGoal  -> true | uu____1080 -> false
let uu___is_CachedFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | CachedFile  -> true | uu____1084 -> false
let uu___is_FileNotWritten: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | FileNotWritten  -> true | uu____1088 -> false
let uu___is_InvalidUTF8Encoding: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | InvalidUTF8Encoding  -> true | uu____1092 -> false
let uu___is_FailToCompileNativeTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | FailToCompileNativeTactic  -> true
    | uu____1096 -> false
exception Err of (raw_error,Prims.string) FStar_Pervasives_Native.tuple2
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____1107 -> true | uu____1112 -> false
let __proj__Err__item__uu___:
  Prims.exn -> (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Err uu____1127 -> uu____1127
exception Error of (raw_error,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____1144 -> true | uu____1151 -> false
let __proj__Error__item__uu___:
  Prims.exn ->
    (raw_error,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Error uu____1170 -> uu____1170
exception Warning of (raw_error,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____1189 -> true | uu____1196 -> false
let __proj__Warning__item__uu___:
  Prims.exn ->
    (raw_error,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Warning uu____1215 -> uu____1215
exception Stop
let uu___is_Stop: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Stop  -> true | uu____1225 -> false
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____1229 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError[@@deriving show]
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____1233 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EInfo  -> true | uu____1237 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____1241 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____1245 -> false
type issue =
  {
  issue_message: Prims.string;
  issue_level: issue_level;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
let __proj__Mkissue__item__issue_message: issue -> Prims.string =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_message
let __proj__Mkissue__item__issue_level: issue -> issue_level =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_level
let __proj__Mkissue__item__issue_range:
  issue -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;_} -> __fname__issue_range
type error_handler =
  {
  eh_add_one: issue -> Prims.unit;
  eh_count_errors: Prims.unit -> Prims.int;
  eh_report: Prims.unit -> issue Prims.list;
  eh_clear: Prims.unit -> Prims.unit;}[@@deriving show]
let __proj__Mkerror_handler__item__eh_add_one:
  error_handler -> issue -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_add_one
let __proj__Mkerror_handler__item__eh_count_errors:
  error_handler -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_count_errors
let __proj__Mkerror_handler__item__eh_report:
  error_handler -> Prims.unit -> issue Prims.list =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_report
let __proj__Mkerror_handler__item__eh_clear:
  error_handler -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { eh_add_one = __fname__eh_add_one;
        eh_count_errors = __fname__eh_count_errors;
        eh_report = __fname__eh_report; eh_clear = __fname__eh_clear;_} ->
        __fname__eh_clear
let format_issue: issue -> Prims.string =
  fun issue  ->
    let level_header =
      match issue.issue_level with
      | EInfo  -> "(Info) "
      | EWarning  -> "(Warning) "
      | EError  -> "(Error) "
      | ENotImplemented  -> "Feature not yet implemented: " in
    let uu____1414 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____1424 =
            let uu____1425 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____1425 in
          let uu____1426 =
            let uu____1427 =
              let uu____1428 = FStar_Range.use_range r in
              let uu____1429 = FStar_Range.def_range r in
              uu____1428 = uu____1429 in
            if uu____1427
            then ""
            else
              (let uu____1431 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____1431) in
          (uu____1424, uu____1426) in
    match uu____1414 with
    | (range_str,see_also_str) ->
        FStar_Util.format4 "%s%s%s%s\n" range_str level_header
          issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let uu____1437 = format_issue issue in FStar_Util.print_error uu____1437
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Prims.parse_int "0"
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____1452) -> - (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some uu____1457,FStar_Pervasives_Native.None
         ) -> Prims.parse_int "1"
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____1479 =
          let uu____1482 = FStar_ST.op_Bang errs in e :: uu____1482 in
        FStar_ST.op_Colon_Equals errs uu____1479
    | uu____1613 -> print_issue e in
  let count_errors uu____1617 =
    let uu____1618 = FStar_ST.op_Bang errs in FStar_List.length uu____1618 in
  let report uu____1690 =
    let sorted1 =
      let uu____1694 = FStar_ST.op_Bang errs in
      FStar_List.sortWith compare_issues uu____1694 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____1765 = FStar_ST.op_Colon_Equals errs [] in
  {
    eh_add_one = add_one;
    eh_count_errors = count_errors;
    eh_report = report;
    eh_clear = clear1
  }
let current_handler: error_handler FStar_ST.ref =
  FStar_Util.mk_ref default_handler
let mk_issue:
  issue_level ->
    FStar_Range.range FStar_Pervasives_Native.option -> Prims.string -> issue
  =
  fun level  ->
    fun range  ->
      fun msg  ->
        { issue_message = msg; issue_level = level; issue_range = range }
let get_err_count: Prims.unit -> Prims.int =
  fun uu____1858  ->
    let uu____1859 =
      let uu____1862 = FStar_ST.op_Bang current_handler in
      uu____1862.eh_count_errors in
    uu____1859 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____1914  ->
         let uu____1915 =
           let uu____1918 = FStar_ST.op_Bang current_handler in
           uu____1918.eh_add_one in
         uu____1915 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____1974  ->
         let uu____1975 =
           let uu____1978 = FStar_ST.op_Bang current_handler in
           uu____1978.eh_add_one in
         FStar_List.iter uu____1975 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____2029  ->
    let uu____2030 =
      let uu____2035 = FStar_ST.op_Bang current_handler in
      uu____2035.eh_report in
    uu____2030 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____2084  ->
    let uu____2085 =
      let uu____2088 = FStar_ST.op_Bang current_handler in
      uu____2088.eh_clear in
    uu____2085 ()
let set_handler: error_handler -> Prims.unit =
  fun handler  ->
    let issues = report_all () in
    clear ();
    FStar_ST.op_Colon_Equals current_handler handler;
    add_many issues
type error_message_prefix =
  {
  set_prefix: Prims.string -> Prims.unit;
  append_prefix: Prims.string -> Prims.string;
  clear_prefix: Prims.unit -> Prims.unit;}[@@deriving show]
let __proj__Mkerror_message_prefix__item__set_prefix:
  error_message_prefix -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__set_prefix
let __proj__Mkerror_message_prefix__item__append_prefix:
  error_message_prefix -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__append_prefix
let __proj__Mkerror_message_prefix__item__clear_prefix:
  error_message_prefix -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { set_prefix = __fname__set_prefix;
        append_prefix = __fname__append_prefix;
        clear_prefix = __fname__clear_prefix;_} -> __fname__clear_prefix
let message_prefix: error_message_prefix =
  let pfx = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_prefix s =
    FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some s) in
  let clear_prefix uu____2339 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None in
  let append_prefix s =
    let uu____2408 = FStar_ST.op_Bang pfx in
    match uu____2408 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let errno_of_error: raw_error -> Prims.int =
  fun uu___38_2478  ->
    match uu___38_2478 with
    | OutOfRange uu____2479 -> Prims.parse_int "1"
    | OpPlusInUniverse  -> Prims.parse_int "2"
    | InvalidUniverseVar  -> Prims.parse_int "3"
    | Z3InvocationError  -> Prims.parse_int "4"
    | TypeError  -> Prims.parse_int "5"
    | TypeCheckerFailToProve  -> Prims.parse_int "6"
    | InductiveTypeNotSatisfyPositivityCondition  -> Prims.parse_int "7"
    | UncontrainedUnificationVar  -> Prims.parse_int "8"
    | UnexpectedGTotComputation  -> Prims.parse_int "9"
    | UnexpectedInstance  -> Prims.parse_int "10"
    | ProofObligationFailed  -> Prims.parse_int "11"
    | UnknowAssertionFailure  -> Prims.parse_int "12"
    | UninstantiatedUnificationVarInTactic  -> Prims.parse_int "13"
    | AssertionFailure  -> Prims.parse_int "14"
    | MissingInterface  -> Prims.parse_int "15"
    | MissingImplementation  -> Prims.parse_int "16"
    | TooManyOrTooFewFileMatch  -> Prims.parse_int "17"
    | DeprecatedEqualityOnBinder  -> Prims.parse_int "18"
    | Filtered  -> Prims.parse_int "19"
    | ModuleFileNameMismatch  -> Prims.parse_int "20"
    | ModuleOrFileNotFoundWarning  -> Prims.parse_int "21"
    | UnboundModuleReference  -> Prims.parse_int "22"
    | UnprotectedTerm  -> Prims.parse_int "23"
    | NotEmbedded uu____2480 -> Prims.parse_int "24"
    | FunctionLiteralPrecisionLoss  -> Prims.parse_int "25"
    | NonListLiteralSMTPattern  -> Prims.parse_int "26"
    | SMTPatternMissingBoundVar  -> Prims.parse_int "27"
    | UnexpectedConstructorType  -> Prims.parse_int "28"
    | Z3InvocationWarning  -> Prims.parse_int "29"
    | UnexpectedZ3Output  -> Prims.parse_int "30"
    | InaccessibleArgument  -> Prims.parse_int "31"
    | DocOverwrite  -> Prims.parse_int "32"
    | AdmitWithoutDefinition  -> Prims.parse_int "33"
    | DeprecatedOpaqueQualifier  -> Prims.parse_int "34"
    | UseDefaultEffect  -> Prims.parse_int "35"
    | AddImplicitAssumeNewQualifier  -> Prims.parse_int "36"
    | TopLevelEffect  -> Prims.parse_int "37"
    | MetaAlienNotATmUnknow  -> Prims.parse_int "38"
    | PatternMissingBoundVar  -> Prims.parse_int "39"
    | IrrelevantQualifierOnArgumentToReify  -> Prims.parse_int "40"
    | IrrelevantQualifierOnArgumentToReflect  -> Prims.parse_int "41"
    | RedundantExplicitCurrying  -> Prims.parse_int "42"
    | HintFailedToReplayProof  -> Prims.parse_int "43"
    | HitReplayFailed  -> Prims.parse_int "44"
    | SMTPatTDeprecated  -> Prims.parse_int "45"
    | CachedFile  -> Prims.parse_int "46"
    | FileNotWritten  -> Prims.parse_int "47"
    | IllFormedGoal  -> Prims.parse_int "48"
    | uu____2481 -> Prims.parse_int "0"
type flag =
  | CError
  | CWarning
  | CSilent[@@deriving show]
let uu___is_CError: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CError  -> true | uu____2485 -> false
let uu___is_CWarning: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____2489 -> false
let uu___is_CSilent: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____2493 -> false
let next_errno: Prims.int = Prims.parse_int "49"
let flags: flag Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let update_flags:
  (flag,(Prims.int,Prims.int) FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun l  ->
    let compare1 uu____2551 uu____2552 =
      match (uu____2551, uu____2552) with
      | ((uu____2585,(a,uu____2587)),(uu____2588,(b,uu____2590))) ->
          if a > b
          then Prims.parse_int "1"
          else if a < b then - (Prims.parse_int "1") else Prims.parse_int "0" in
    let sorted1 = FStar_List.sortWith compare1 l in
    let rec set_flag i l1 =
      match l1 with
      | [] ->
          let uu____2671 = FStar_ST.op_Bang flags in
          FStar_List.nth uu____2671 i
      | (f,(l2,h))::tl1 ->
          if (i >= l2) && (i <= h)
          then f
          else
            if i < l2
            then
              (let uu____2751 = FStar_ST.op_Bang flags in
               FStar_List.nth uu____2751 i)
            else set_flag i tl1 in
    let rec aux f i l1 =
      match l1 with
      | [] -> f
      | hd1::tl1 ->
          let uu____2831 =
            let uu____2834 =
              let uu____2837 = set_flag i sorted1 in [uu____2837] in
            FStar_List.append f uu____2834 in
          aux uu____2831 (i + (Prims.parse_int "1")) tl1 in
    let rec init_flags l1 i =
      if i > (Prims.parse_int "0")
      then
        init_flags (FStar_List.append l1 [CError])
          (i - (Prims.parse_int "1"))
      else l1 in
    let rec check_range l1 =
      match l1 with
      | [] -> ()
      | (uu____2886,(l2,h))::tl1 ->
          if (l2 < (Prims.parse_int "0")) || (h > next_errno)
          then
            let uu____2912 =
              let uu____2913 = FStar_Util.string_of_int l2 in
              let uu____2914 = FStar_Util.string_of_int h in
              FStar_Util.format2 "No error for warn_error %s..%s" uu____2913
                uu____2914 in
            failwith uu____2912
          else () in
    check_range l;
    (let uu____2918 =
       let uu____2919 = FStar_ST.op_Bang flags in uu____2919 = [] in
     if uu____2918
     then
       let uu____2974 = init_flags [] next_errno in
       FStar_ST.op_Colon_Equals flags uu____2974
     else ());
    (let uu____3028 =
       let uu____3031 = FStar_ST.op_Bang flags in
       aux [] (Prims.parse_int "0") uu____3031 in
     FStar_ST.op_Colon_Equals flags uu____3028)
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____3140 = FStar_Options.debug_any () in
      if uu____3140
      then add_one (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg)
      else ()
let maybe_fatal_error:
  FStar_Range.range ->
    (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun r  ->
    fun uu____3151  ->
      match uu____3151 with
      | (e,msg) ->
          let errno = errno_of_error e in
          let uu____3159 =
            let uu____3160 = FStar_ST.op_Bang flags in
            FStar_List.nth uu____3160 errno in
          (match uu____3159 with
           | CError  ->
               add_one (mk_issue EError (FStar_Pervasives_Native.Some r) msg)
           | CWarning  ->
               add_one
                 (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg)
           | CSilent  -> ())
let add_errors:
  (raw_error,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
    Prims.list -> Prims.unit
  =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____3233  ->
         FStar_List.iter
           (fun uu____3245  ->
              match uu____3245 with
              | (e,msg,r) ->
                  let uu____3255 =
                    let uu____3260 = message_prefix.append_prefix msg in
                    (e, uu____3260) in
                  maybe_fatal_error r uu____3255) errs)
let issue_of_exn: Prims.exn -> issue FStar_Pervasives_Native.option =
  fun uu___39_3265  ->
    match uu___39_3265 with
    | Error (e,msg,r) ->
        let uu____3271 =
          let uu____3272 = message_prefix.append_prefix msg in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____3272 in
        FStar_Pervasives_Native.Some uu____3271
    | FStar_Util.NYI msg ->
        let uu____3274 =
          let uu____3275 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____3275 in
        FStar_Pervasives_Native.Some uu____3274
    | Err (e,msg) ->
        let uu____3278 =
          let uu____3279 = message_prefix.append_prefix msg in
          mk_issue EError FStar_Pervasives_Native.None uu____3279 in
        FStar_Pervasives_Native.Some uu____3278
    | uu____3280 -> FStar_Pervasives_Native.None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    if exn = Stop
    then ()
    else
      (let uu____3285 = issue_of_exn exn in
       match uu____3285 with
       | FStar_Pervasives_Native.Some issue -> add_one issue
       | FStar_Pervasives_Native.None  -> FStar_Exn.raise exn)
let handleable: Prims.exn -> Prims.bool =
  fun uu___40_3291  ->
    match uu___40_3291 with
    | Error uu____3292 -> true
    | FStar_Util.NYI uu____3299 -> true
    | Stop  -> true
    | Err uu____3300 -> true
    | uu____3305 -> false
let stop_if_err: Prims.unit -> Prims.unit =
  fun uu____3308  ->
    let uu____3309 =
      let uu____3310 = get_err_count () in uu____3310 > (Prims.parse_int "0") in
    if uu____3309 then FStar_Exn.raise Stop else ()
let raise_error:
  'Auu____3315 .
    (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 ->
      FStar_Range.range -> 'Auu____3315
  =
  fun uu____3326  ->
    fun r  ->
      match uu____3326 with | (e,msg) -> FStar_Exn.raise (Error (e, msg, r))
let raise_err:
  'Auu____3336 .
    (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 -> 'Auu____3336
  =
  fun uu____3344  ->
    match uu____3344 with | (e,msg) -> FStar_Exn.raise (Err (e, msg))