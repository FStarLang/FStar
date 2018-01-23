open Prims
type raw_error =
  | Error_DependencyAnalysisFailed
  | Error_IDETooManyPops
  | Error_IDEUnrecognized
  | Error_InductiveTypeNotSatisfyPositivityCondition
  | Error_InvalidUniverseVar
  | Error_MissingFileName
  | Error_ModuleFileNameMismatch
  | Error_OpPlusInUniverse
  | Error_OutOfRange
  | Error_ProofObligationFailed
  | Error_TooManyFiles
  | Error_TypeCheckerFailToProve
  | Error_TypeError
  | Error_UncontrainedUnificationVar
  | Error_UnexpectedGTotComputation
  | Error_UnexpectedInstance
  | Error_UnknownFatal_AssertionFailure
  | Error_Z3InvocationError
  | Error_IDEAssertionFailure
  | Error_Z3SolverError
  | Fatal_AbstractTypeDeclarationInInterface
  | Fatal_ActionMustHaveFunctionType
  | Fatal_AlreadyDefinedTopLevelDeclaration
  | Fatal_ArgumentLengthMismatch
  | Fatal_AssertionFailure
  | Fatal_AssignToImmutableValues
  | Fatal_AssumeValInInterface
  | Fatal_BadlyInstantiatedSynthByTactic
  | Fatal_BadSignatureShape
  | Fatal_BinderAndArgsLengthMismatch
  | Fatal_BothValAndLetInInterface
  | Fatal_CardinalityConstraintViolated
  | Fatal_ComputationNotTotal
  | Fatal_ComputationTypeNotAllowed
  | Fatal_ComputedTypeNotMatchAnnotation
  | Fatal_ConstructorArgLengthMismatch
  | Fatal_ConstructorFailedCheck
  | Fatal_ConstructorNotFound
  | Fatal_ConstsructorBuildWrongType
  | Fatal_CycleInRecTypeAbbreviation
  | Fatal_DataContructorNotFound
  | Fatal_DefaultQualifierNotAllowedOnEffects
  | Fatal_DefinitionNotFound
  | Fatal_DisjuctivePatternVarsMismatch
  | Fatal_DivergentComputationCannotBeIncludedInTotal
  | Fatal_DuplicateInImplementation
  | Fatal_DuplicateModuleOrInterface
  | Fatal_DuplicateTopLevelNames
  | Fatal_DuplicateTypeAnnotationAndValDecl
  | Fatal_EffectCannotBeReified
  | Fatal_EffectConstructorNotFullyApplied
  | Fatal_EffectfulAndPureComputationMismatch
  | Fatal_EffectNotFound
  | Fatal_EffectsCannotBeComposed
  | Fatal_ErrorInSolveDeferredConstraints
  | Fatal_ErrorsReported
  | Fatal_EscapedBoundVar
  | Fatal_ExpectedArrowAnnotatedType
  | Fatal_ExpectedGhostExpression
  | Fatal_ExpectedPureExpression
  | Fatal_ExpectNormalizedEffect
  | Fatal_ExpectTermGotFunction
  | Fatal_ExpectTrivialPreCondition
  | Fatal_FailToCompileNativeTactic
  | Fatal_FailToProcessPragma
  | Fatal_FailToResolveImplicitArgument
  | Fatal_FailToSolveUniverseInEquality
  | Fatal_FieldsNotBelongToSameRecordType
  | Fatal_ForbiddenReferenceToCurrentModule
  | Fatal_FreeVariables
  | Fatal_FunctionTypeExpected
  | Fatal_IdentifierNotFound
  | Fatal_IllAppliedConstant
  | Fatal_IllegalCharInByteArray
  | Fatal_IllegalCharInOperatorName
  | Fatal_IllTyped
  | Fatal_ImpossibleAbbrevLidBundle
  | Fatal_ImpossibleAbbrevRenameBundle
  | Fatal_ImpossibleInductiveWithAbbrev
  | Fatal_ImpossiblePrePostAbs
  | Fatal_ImpossiblePrePostArrow
  | Fatal_ImpossibleToGenerateDMEffect
  | Fatal_ImpossibleTypeAbbrevBundle
  | Fatal_ImpossibleTypeAbbrevSigeltBundle
  | Fatal_IncludeModuleNotPrepared
  | Fatal_IncoherentInlineUniverse
  | Fatal_IncompatibleKinds
  | Fatal_IncompatibleNumberOfTypes
  | Fatal_IncompatibleSetOfUniverse
  | Fatal_IncompatibleUniverse
  | Fatal_InconsistentImplicitArgumentAnnotation
  | Fatal_InconsistentImplicitQualifier
  | Fatal_InconsistentQualifierAnnotation
  | Fatal_InferredTypeCauseVarEscape
  | Fatal_InlineRenamedAsUnfold
  | Fatal_InsufficientPatternArguments
  | Fatal_InterfaceAlreadyProcessed
  | Fatal_InterfaceNotImplementedByModule
  | Fatal_InterfaceWithTypeImplementation
  | Fatal_InvalidFloatingPointNumber
  | Fatal_InvalidFSDocKeyword
  | Fatal_InvalidIdentifier
  | Fatal_InvalidLemmaArgument
  | Fatal_InvalidNumericLiteral
  | Fatal_InvalidRedefinitionOfLexT
  | Fatal_InvalidUnicodeInStringLiteral
  | Fatal_InvalidUTF8Encoding
  | Fatal_InvalidWarnErrorSetting
  | Fatal_LetBoundMonadicMismatch
  | Fatal_LetMutableForVariablesOnly
  | Fatal_LetOpenModuleOnly
  | Fatal_LetRecArgumentMismatch
  | Fatal_MalformedActionDeclaration
  | Fatal_MismatchedPatternType
  | Fatal_MismatchUniversePolymorphic
  | Fatal_MissingDataConstructor
  | Fatal_MissingExposeInterfacesOption
  | Fatal_MissingFieldInRecord
  | Fatal_MissingImplementation
  | Fatal_MissingImplicitArguments
  | Fatal_MissingInterface
  | Fatal_MissingNameInBinder
  | Fatal_MissingPrimsModule
  | Fatal_MissingQuantifierBinder
  | Fatal_ModuleExpected
  | Fatal_ModuleFileNotFound
  | Fatal_ModuleFirstStatement
  | Fatal_ModuleNotFound
  | Fatal_ModuleOrFileNotFound
  | Fatal_MonadAlreadyDefined
  | Fatal_MoreThanOneDeclaration
  | Fatal_MultipleLetBinding
  | Fatal_NameNotFound
  | Fatal_NameSpaceNotFound
  | Fatal_NegativeUniverseConstFatal_NotSupported
  | Fatal_NoFileProvided
  | Fatal_NonInductiveInMutuallyDefinedType
  | Fatal_NonLinearPatternNotPermitted
  | Fatal_NonLinearPatternVars
  | Fatal_NonSingletonTopLevel
  | Fatal_NonSingletonTopLevelModule
  | Fatal_NonTopRecFunctionNotFullyEncoded
  | Fatal_NonTrivialPreConditionInPrims
  | Fatal_NonVariableInductiveTypeParameter
  | Fatal_NotApplicationOrFv
  | Fatal_NotEnoughArgsToEffect
  | Fatal_NotEnoughArgumentsForEffect
  | Fatal_NotFunctionType
  | Fatal_NotSupported
  | Fatal_NotTopLevelModule
  | Fatal_NotValidFStarFile
  | Fatal_NotValidIncludeDirectory
  | Fatal_OneModulePerFile
  | Fatal_OpenGoalsInSynthesis
  | Fatal_OptionsNotCompatible
  | Fatal_OutOfOrder
  | Fatal_ParseErrors
  | Fatal_ParseItError
  | Fatal_PolyTypeExpected
  | Fatal_PossibleInfiniteTyp
  | Fatal_PreModuleMismatch
  | Fatal_QulifierListNotPermitted
  | Fatal_RecursiveFunctionLiteral
  | Fatal_ReflectOnlySupportedOnEffects
  | Fatal_ReservedPrefix
  | Fatal_SMTOutputParseError
  | Fatal_SMTSolverError
  | Fatal_SyntaxError
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
  | Fatal_UnexpectedBinder
  | Fatal_UnexpectedBindShape
  | Fatal_UnexpectedChar
  | Fatal_UnexpectedComputationTypeForLetRec
  | Fatal_UnexpectedConstructorType
  | Fatal_UnexpectedDataConstructor
  | Fatal_UnexpectedEffect
  | Fatal_UnexpectedEmptyRecord
  | Fatal_UnexpectedExpressionType
  | Fatal_UnexpectedFunctionParameterType
  | Fatal_UnexpectedGeneralizedUniverse
  | Fatal_UnexpectedGTotForLetRec
  | Fatal_UnexpectedGuard
  | Fatal_UnexpectedIdentifier
  | Fatal_UnexpectedImplicitArgument
  | Fatal_UnexpectedImplictArgument
  | Fatal_UnexpectedInductivetype
  | Fatal_UnexpectedLetBinding
  | Fatal_UnexpectedModuleDeclaration
  | Fatal_UnexpectedNumberOfUniverse
  | Fatal_UnexpectedNumericLiteral
  | Fatal_UnexpectedOperatorSymbol
  | Fatal_UnexpectedPattern
  | Fatal_UnexpectedPosition
  | Fatal_UnExpectedPreCondition
  | Fatal_UnexpectedReturnShape
  | Fatal_UnexpectedSignatureForMonad
  | Fatal_UnexpectedTerm
  | Fatal_UnexpectedTermInUniverse
  | Fatal_UnexpectedTermType
  | Fatal_UnexpectedUniversePolymorphicReturn
  | Fatal_UnexpectedUniverseVariable
  | Fatal_UnfoldableDeprecated
  | Fatal_UnificationNotWellFormed
  | Fatal_Uninstantiated
  | Fatal_UninstantiatedUnificationVarInTactic
  | Fatal_UninstantiatedVarInTactic
  | Fatal_UniverseMightContainSumOfTwoUnivVars
  | Fatal_UniversePolymorphicInnerLetBound
  | Fatal_UnknownAttribute
  | Fatal_UnknownToolForDep
  | Fatal_UnrecognizedExtension
  | Fatal_UnresolvedPatternVar
  | Fatal_UnsupportedConstant
  | Fatal_UnsupportedDisjuctivePatterns
  | Fatal_UnsupportedQualifier
  | Fatal_UserTacticFailure
  | Fatal_ValueRestriction
  | Fatal_VariableNotFound
  | Fatal_WrongBodyTypeForReturnWP
  | Fatal_WrongDataAppHeadFormat
  | Fatal_WrongDefinitionOrder
  | Fatal_WrongResultTypeAfterConstrutor
  | Fatal_WrongTerm
  | Fatal_WhenClauseNotSupported
  | Fatal_CallNotImplemented
  | Warning_AddImplicitAssumeNewQualifier
  | Warning_AdmitWithoutDefinition
  | Warning_CachedFile
  | Warning_DefinitionNotTranslated
  | Warning_DependencyFound
  | Warning_DeprecatedEqualityOnBinder
  | Warning_DeprecatedOpaqueQualifier
  | Warning_DocOverwrite
  | Warning_FileNotWritten
  | Warning_Filtered
  | Warning_FunctionLiteralPrecisionLoss
  | Warning_FunctionNotExtacted
  | Warning_HintFailedToReplayProof
  | Warning_HitReplayFailed
  | Warning_IDEIgnoreCodeGen
  | Warning_IllFormedGoal
  | Warning_InaccessibleArgument
  | Warning_IncoherentImplicitQualifier
  | Warning_IrrelevantQualifierOnArgumentToReflect
  | Warning_IrrelevantQualifierOnArgumentToReify
  | Warning_MalformedWarnErrorList
  | Warning_MetaAlienNotATmUnknown
  | Warning_MultipleAscriptions
  | Warning_NondependentUserDefinedDataType
  | Warning_NonListLiteralSMTPattern
  | Warning_NormalizationFailure
  | Warning_NotDependentArrow
  | Warning_NotEmbedded
  | Warning_PatternMissingBoundVar
  | Warning_RecursiveDependency
  | Warning_RedundantExplicitCurrying
  | Warning_SMTPatTDeprecated
  | Warning_SMTPatternMissingBoundVar
  | Warning_TopLevelEffect
  | Warning_UnboundModuleReference
  | Warning_UnexpectedFile
  | Warning_UnexpectedFsTypApp
  | Warning_UnexpectedZ3Output
  | Warning_UnprotectedTerm
  | Warning_UnrecognizedAttribute
  | Warning_UpperBoundCandidateAlreadyVisited
  | Warning_UseDefaultEffect
  | Warning_WrongErrorLocation
  | Warning_Z3InvocationWarning
  | Warning_CallNotImplementedAsWarning
  | Warning_MissingInterfaceOrImplementation
  | Warning_ConstructorBuildsUnexpectedType
  | Warning_ModuleOrFileNotFoundWarning
  | Error_NoLetMutable
  | Error_BadImplicit[@@deriving show]
let uu___is_Error_DependencyAnalysisFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_DependencyAnalysisFailed  -> true
    | uu____4 -> false
let uu___is_Error_IDETooManyPops: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_IDETooManyPops  -> true | uu____8 -> false
let uu___is_Error_IDEUnrecognized: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_IDEUnrecognized  -> true | uu____12 -> false
let uu___is_Error_InductiveTypeNotSatisfyPositivityCondition:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_InductiveTypeNotSatisfyPositivityCondition  -> true
    | uu____16 -> false
let uu___is_Error_InvalidUniverseVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_InvalidUniverseVar  -> true
    | uu____20 -> false
let uu___is_Error_MissingFileName: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_MissingFileName  -> true | uu____24 -> false
let uu___is_Error_ModuleFileNameMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_ModuleFileNameMismatch  -> true
    | uu____28 -> false
let uu___is_Error_OpPlusInUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_OpPlusInUniverse  -> true
    | uu____32 -> false
let uu___is_Error_OutOfRange: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_OutOfRange  -> true | uu____36 -> false
let uu___is_Error_ProofObligationFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_ProofObligationFailed  -> true
    | uu____40 -> false
let uu___is_Error_TooManyFiles: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_TooManyFiles  -> true | uu____44 -> false
let uu___is_Error_TypeCheckerFailToProve: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_TypeCheckerFailToProve  -> true
    | uu____48 -> false
let uu___is_Error_TypeError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_TypeError  -> true | uu____52 -> false
let uu___is_Error_UncontrainedUnificationVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_UncontrainedUnificationVar  -> true
    | uu____56 -> false
let uu___is_Error_UnexpectedGTotComputation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedGTotComputation  -> true
    | uu____60 -> false
let uu___is_Error_UnexpectedInstance: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedInstance  -> true
    | uu____64 -> false
let uu___is_Error_UnknownFatal_AssertionFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_UnknownFatal_AssertionFailure  -> true
    | uu____68 -> false
let uu___is_Error_Z3InvocationError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_Z3InvocationError  -> true
    | uu____72 -> false
let uu___is_Error_IDEAssertionFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Error_IDEAssertionFailure  -> true
    | uu____76 -> false
let uu___is_Error_Z3SolverError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_Z3SolverError  -> true | uu____80 -> false
let uu___is_Fatal_AbstractTypeDeclarationInInterface: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_AbstractTypeDeclarationInInterface  -> true
    | uu____84 -> false
let uu___is_Fatal_ActionMustHaveFunctionType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ActionMustHaveFunctionType  -> true
    | uu____88 -> false
let uu___is_Fatal_AlreadyDefinedTopLevelDeclaration: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_AlreadyDefinedTopLevelDeclaration  -> true
    | uu____92 -> false
let uu___is_Fatal_ArgumentLengthMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ArgumentLengthMismatch  -> true
    | uu____96 -> false
let uu___is_Fatal_AssertionFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_AssertionFailure  -> true
    | uu____100 -> false
let uu___is_Fatal_AssignToImmutableValues: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_AssignToImmutableValues  -> true
    | uu____104 -> false
let uu___is_Fatal_AssumeValInInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_AssumeValInInterface  -> true
    | uu____108 -> false
let uu___is_Fatal_BadlyInstantiatedSynthByTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_BadlyInstantiatedSynthByTactic  -> true
    | uu____112 -> false
let uu___is_Fatal_BadSignatureShape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_BadSignatureShape  -> true
    | uu____116 -> false
let uu___is_Fatal_BinderAndArgsLengthMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_BinderAndArgsLengthMismatch  -> true
    | uu____120 -> false
let uu___is_Fatal_BothValAndLetInInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_BothValAndLetInInterface  -> true
    | uu____124 -> false
let uu___is_Fatal_CardinalityConstraintViolated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_CardinalityConstraintViolated  -> true
    | uu____128 -> false
let uu___is_Fatal_ComputationNotTotal: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ComputationNotTotal  -> true
    | uu____132 -> false
let uu___is_Fatal_ComputationTypeNotAllowed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ComputationTypeNotAllowed  -> true
    | uu____136 -> false
let uu___is_Fatal_ComputedTypeNotMatchAnnotation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ComputedTypeNotMatchAnnotation  -> true
    | uu____140 -> false
let uu___is_Fatal_ConstructorArgLengthMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorArgLengthMismatch  -> true
    | uu____144 -> false
let uu___is_Fatal_ConstructorFailedCheck: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorFailedCheck  -> true
    | uu____148 -> false
let uu___is_Fatal_ConstructorNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorNotFound  -> true
    | uu____152 -> false
let uu___is_Fatal_ConstsructorBuildWrongType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ConstsructorBuildWrongType  -> true
    | uu____156 -> false
let uu___is_Fatal_CycleInRecTypeAbbreviation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_CycleInRecTypeAbbreviation  -> true
    | uu____160 -> false
let uu___is_Fatal_DataContructorNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DataContructorNotFound  -> true
    | uu____164 -> false
let uu___is_Fatal_DefaultQualifierNotAllowedOnEffects:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DefaultQualifierNotAllowedOnEffects  -> true
    | uu____168 -> false
let uu___is_Fatal_DefinitionNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DefinitionNotFound  -> true
    | uu____172 -> false
let uu___is_Fatal_DisjuctivePatternVarsMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DisjuctivePatternVarsMismatch  -> true
    | uu____176 -> false
let uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DivergentComputationCannotBeIncludedInTotal  -> true
    | uu____180 -> false
let uu___is_Fatal_DuplicateInImplementation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateInImplementation  -> true
    | uu____184 -> false
let uu___is_Fatal_DuplicateModuleOrInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateModuleOrInterface  -> true
    | uu____188 -> false
let uu___is_Fatal_DuplicateTopLevelNames: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateTopLevelNames  -> true
    | uu____192 -> false
let uu___is_Fatal_DuplicateTypeAnnotationAndValDecl: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateTypeAnnotationAndValDecl  -> true
    | uu____196 -> false
let uu___is_Fatal_EffectCannotBeReified: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_EffectCannotBeReified  -> true
    | uu____200 -> false
let uu___is_Fatal_EffectConstructorNotFullyApplied: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_EffectConstructorNotFullyApplied  -> true
    | uu____204 -> false
let uu___is_Fatal_EffectfulAndPureComputationMismatch:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_EffectfulAndPureComputationMismatch  -> true
    | uu____208 -> false
let uu___is_Fatal_EffectNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_EffectNotFound  -> true | uu____212 -> false
let uu___is_Fatal_EffectsCannotBeComposed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_EffectsCannotBeComposed  -> true
    | uu____216 -> false
let uu___is_Fatal_ErrorInSolveDeferredConstraints: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ErrorInSolveDeferredConstraints  -> true
    | uu____220 -> false
let uu___is_Fatal_ErrorsReported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_ErrorsReported  -> true | uu____224 -> false
let uu___is_Fatal_EscapedBoundVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_EscapedBoundVar  -> true
    | uu____228 -> false
let uu___is_Fatal_ExpectedArrowAnnotatedType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedArrowAnnotatedType  -> true
    | uu____232 -> false
let uu___is_Fatal_ExpectedGhostExpression: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedGhostExpression  -> true
    | uu____236 -> false
let uu___is_Fatal_ExpectedPureExpression: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedPureExpression  -> true
    | uu____240 -> false
let uu___is_Fatal_ExpectNormalizedEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectNormalizedEffect  -> true
    | uu____244 -> false
let uu___is_Fatal_ExpectTermGotFunction: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectTermGotFunction  -> true
    | uu____248 -> false
let uu___is_Fatal_ExpectTrivialPreCondition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectTrivialPreCondition  -> true
    | uu____252 -> false
let uu___is_Fatal_FailToCompileNativeTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_FailToCompileNativeTactic  -> true
    | uu____256 -> false
let uu___is_Fatal_FailToProcessPragma: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_FailToProcessPragma  -> true
    | uu____260 -> false
let uu___is_Fatal_FailToResolveImplicitArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_FailToResolveImplicitArgument  -> true
    | uu____264 -> false
let uu___is_Fatal_FailToSolveUniverseInEquality: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_FailToSolveUniverseInEquality  -> true
    | uu____268 -> false
let uu___is_Fatal_FieldsNotBelongToSameRecordType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_FieldsNotBelongToSameRecordType  -> true
    | uu____272 -> false
let uu___is_Fatal_ForbiddenReferenceToCurrentModule: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_ForbiddenReferenceToCurrentModule  -> true
    | uu____276 -> false
let uu___is_Fatal_FreeVariables: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_FreeVariables  -> true | uu____280 -> false
let uu___is_Fatal_FunctionTypeExpected: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_FunctionTypeExpected  -> true
    | uu____284 -> false
let uu___is_Fatal_IdentifierNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IdentifierNotFound  -> true
    | uu____288 -> false
let uu___is_Fatal_IllAppliedConstant: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IllAppliedConstant  -> true
    | uu____292 -> false
let uu___is_Fatal_IllegalCharInByteArray: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IllegalCharInByteArray  -> true
    | uu____296 -> false
let uu___is_Fatal_IllegalCharInOperatorName: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IllegalCharInOperatorName  -> true
    | uu____300 -> false
let uu___is_Fatal_IllTyped: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_IllTyped  -> true | uu____304 -> false
let uu___is_Fatal_ImpossibleAbbrevLidBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleAbbrevLidBundle  -> true
    | uu____308 -> false
let uu___is_Fatal_ImpossibleAbbrevRenameBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleAbbrevRenameBundle  -> true
    | uu____312 -> false
let uu___is_Fatal_ImpossibleInductiveWithAbbrev: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleInductiveWithAbbrev  -> true
    | uu____316 -> false
let uu___is_Fatal_ImpossiblePrePostAbs: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossiblePrePostAbs  -> true
    | uu____320 -> false
let uu___is_Fatal_ImpossiblePrePostArrow: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossiblePrePostArrow  -> true
    | uu____324 -> false
let uu___is_Fatal_ImpossibleToGenerateDMEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleToGenerateDMEffect  -> true
    | uu____328 -> false
let uu___is_Fatal_ImpossibleTypeAbbrevBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevBundle  -> true
    | uu____332 -> false
let uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevSigeltBundle  -> true
    | uu____336 -> false
let uu___is_Fatal_IncludeModuleNotPrepared: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IncludeModuleNotPrepared  -> true
    | uu____340 -> false
let uu___is_Fatal_IncoherentInlineUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IncoherentInlineUniverse  -> true
    | uu____344 -> false
let uu___is_Fatal_IncompatibleKinds: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleKinds  -> true
    | uu____348 -> false
let uu___is_Fatal_IncompatibleNumberOfTypes: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleNumberOfTypes  -> true
    | uu____352 -> false
let uu___is_Fatal_IncompatibleSetOfUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleSetOfUniverse  -> true
    | uu____356 -> false
let uu___is_Fatal_IncompatibleUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleUniverse  -> true
    | uu____360 -> false
let uu___is_Fatal_InconsistentImplicitArgumentAnnotation:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentImplicitArgumentAnnotation  -> true
    | uu____364 -> false
let uu___is_Fatal_InconsistentImplicitQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentImplicitQualifier  -> true
    | uu____368 -> false
let uu___is_Fatal_InconsistentQualifierAnnotation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentQualifierAnnotation  -> true
    | uu____372 -> false
let uu___is_Fatal_InferredTypeCauseVarEscape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InferredTypeCauseVarEscape  -> true
    | uu____376 -> false
let uu___is_Fatal_InlineRenamedAsUnfold: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InlineRenamedAsUnfold  -> true
    | uu____380 -> false
let uu___is_Fatal_InsufficientPatternArguments: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InsufficientPatternArguments  -> true
    | uu____384 -> false
let uu___is_Fatal_InterfaceAlreadyProcessed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceAlreadyProcessed  -> true
    | uu____388 -> false
let uu___is_Fatal_InterfaceNotImplementedByModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceNotImplementedByModule  -> true
    | uu____392 -> false
let uu___is_Fatal_InterfaceWithTypeImplementation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceWithTypeImplementation  -> true
    | uu____396 -> false
let uu___is_Fatal_InvalidFloatingPointNumber: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidFloatingPointNumber  -> true
    | uu____400 -> false
let uu___is_Fatal_InvalidFSDocKeyword: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidFSDocKeyword  -> true
    | uu____404 -> false
let uu___is_Fatal_InvalidIdentifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidIdentifier  -> true
    | uu____408 -> false
let uu___is_Fatal_InvalidLemmaArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidLemmaArgument  -> true
    | uu____412 -> false
let uu___is_Fatal_InvalidNumericLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidNumericLiteral  -> true
    | uu____416 -> false
let uu___is_Fatal_InvalidRedefinitionOfLexT: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidRedefinitionOfLexT  -> true
    | uu____420 -> false
let uu___is_Fatal_InvalidUnicodeInStringLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidUnicodeInStringLiteral  -> true
    | uu____424 -> false
let uu___is_Fatal_InvalidUTF8Encoding: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidUTF8Encoding  -> true
    | uu____428 -> false
let uu___is_Fatal_InvalidWarnErrorSetting: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidWarnErrorSetting  -> true
    | uu____432 -> false
let uu___is_Fatal_LetBoundMonadicMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_LetBoundMonadicMismatch  -> true
    | uu____436 -> false
let uu___is_Fatal_LetMutableForVariablesOnly: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_LetMutableForVariablesOnly  -> true
    | uu____440 -> false
let uu___is_Fatal_LetOpenModuleOnly: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_LetOpenModuleOnly  -> true
    | uu____444 -> false
let uu___is_Fatal_LetRecArgumentMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_LetRecArgumentMismatch  -> true
    | uu____448 -> false
let uu___is_Fatal_MalformedActionDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MalformedActionDeclaration  -> true
    | uu____452 -> false
let uu___is_Fatal_MismatchedPatternType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MismatchedPatternType  -> true
    | uu____456 -> false
let uu___is_Fatal_MismatchUniversePolymorphic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MismatchUniversePolymorphic  -> true
    | uu____460 -> false
let uu___is_Fatal_MissingDataConstructor: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingDataConstructor  -> true
    | uu____464 -> false
let uu___is_Fatal_MissingExposeInterfacesOption: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingExposeInterfacesOption  -> true
    | uu____468 -> false
let uu___is_Fatal_MissingFieldInRecord: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingFieldInRecord  -> true
    | uu____472 -> false
let uu___is_Fatal_MissingImplementation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingImplementation  -> true
    | uu____476 -> false
let uu___is_Fatal_MissingImplicitArguments: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingImplicitArguments  -> true
    | uu____480 -> false
let uu___is_Fatal_MissingInterface: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingInterface  -> true
    | uu____484 -> false
let uu___is_Fatal_MissingNameInBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingNameInBinder  -> true
    | uu____488 -> false
let uu___is_Fatal_MissingPrimsModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingPrimsModule  -> true
    | uu____492 -> false
let uu___is_Fatal_MissingQuantifierBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MissingQuantifierBinder  -> true
    | uu____496 -> false
let uu___is_Fatal_ModuleExpected: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_ModuleExpected  -> true | uu____500 -> false
let uu___is_Fatal_ModuleFileNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleFileNotFound  -> true
    | uu____504 -> false
let uu___is_Fatal_ModuleFirstStatement: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleFirstStatement  -> true
    | uu____508 -> false
let uu___is_Fatal_ModuleNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_ModuleNotFound  -> true | uu____512 -> false
let uu___is_Fatal_ModuleOrFileNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleOrFileNotFound  -> true
    | uu____516 -> false
let uu___is_Fatal_MonadAlreadyDefined: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MonadAlreadyDefined  -> true
    | uu____520 -> false
let uu___is_Fatal_MoreThanOneDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MoreThanOneDeclaration  -> true
    | uu____524 -> false
let uu___is_Fatal_MultipleLetBinding: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_MultipleLetBinding  -> true
    | uu____528 -> false
let uu___is_Fatal_NameNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_NameNotFound  -> true | uu____532 -> false
let uu___is_Fatal_NameSpaceNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NameSpaceNotFound  -> true
    | uu____536 -> false
let uu___is_Fatal_NegativeUniverseConstFatal_NotSupported:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NegativeUniverseConstFatal_NotSupported  -> true
    | uu____540 -> false
let uu___is_Fatal_NoFileProvided: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_NoFileProvided  -> true | uu____544 -> false
let uu___is_Fatal_NonInductiveInMutuallyDefinedType: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_NonInductiveInMutuallyDefinedType  -> true
    | uu____548 -> false
let uu___is_Fatal_NonLinearPatternNotPermitted: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NonLinearPatternNotPermitted  -> true
    | uu____552 -> false
let uu___is_Fatal_NonLinearPatternVars: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NonLinearPatternVars  -> true
    | uu____556 -> false
let uu___is_Fatal_NonSingletonTopLevel: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NonSingletonTopLevel  -> true
    | uu____560 -> false
let uu___is_Fatal_NonSingletonTopLevelModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NonSingletonTopLevelModule  -> true
    | uu____564 -> false
let uu___is_Fatal_NonTopRecFunctionNotFullyEncoded: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NonTopRecFunctionNotFullyEncoded  -> true
    | uu____568 -> false
let uu___is_Fatal_NonTrivialPreConditionInPrims: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NonTrivialPreConditionInPrims  -> true
    | uu____572 -> false
let uu___is_Fatal_NonVariableInductiveTypeParameter: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_NonVariableInductiveTypeParameter  -> true
    | uu____576 -> false
let uu___is_Fatal_NotApplicationOrFv: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotApplicationOrFv  -> true
    | uu____580 -> false
let uu___is_Fatal_NotEnoughArgsToEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotEnoughArgsToEffect  -> true
    | uu____584 -> false
let uu___is_Fatal_NotEnoughArgumentsForEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotEnoughArgumentsForEffect  -> true
    | uu____588 -> false
let uu___is_Fatal_NotFunctionType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotFunctionType  -> true
    | uu____592 -> false
let uu___is_Fatal_NotSupported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_NotSupported  -> true | uu____596 -> false
let uu___is_Fatal_NotTopLevelModule: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotTopLevelModule  -> true
    | uu____600 -> false
let uu___is_Fatal_NotValidFStarFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotValidFStarFile  -> true
    | uu____604 -> false
let uu___is_Fatal_NotValidIncludeDirectory: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_NotValidIncludeDirectory  -> true
    | uu____608 -> false
let uu___is_Fatal_OneModulePerFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_OneModulePerFile  -> true
    | uu____612 -> false
let uu___is_Fatal_OpenGoalsInSynthesis: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_OpenGoalsInSynthesis  -> true
    | uu____616 -> false
let uu___is_Fatal_OptionsNotCompatible: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_OptionsNotCompatible  -> true
    | uu____620 -> false
let uu___is_Fatal_OutOfOrder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_OutOfOrder  -> true | uu____624 -> false
let uu___is_Fatal_ParseErrors: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_ParseErrors  -> true | uu____628 -> false
let uu___is_Fatal_ParseItError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_ParseItError  -> true | uu____632 -> false
let uu___is_Fatal_PolyTypeExpected: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_PolyTypeExpected  -> true
    | uu____636 -> false
let uu___is_Fatal_PossibleInfiniteTyp: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_PossibleInfiniteTyp  -> true
    | uu____640 -> false
let uu___is_Fatal_PreModuleMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_PreModuleMismatch  -> true
    | uu____644 -> false
let uu___is_Fatal_QulifierListNotPermitted: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_QulifierListNotPermitted  -> true
    | uu____648 -> false
let uu___is_Fatal_RecursiveFunctionLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_RecursiveFunctionLiteral  -> true
    | uu____652 -> false
let uu___is_Fatal_ReflectOnlySupportedOnEffects: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ReflectOnlySupportedOnEffects  -> true
    | uu____656 -> false
let uu___is_Fatal_ReservedPrefix: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_ReservedPrefix  -> true | uu____660 -> false
let uu___is_Fatal_SMTOutputParseError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_SMTOutputParseError  -> true
    | uu____664 -> false
let uu___is_Fatal_SMTSolverError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_SMTSolverError  -> true | uu____668 -> false
let uu___is_Fatal_SyntaxError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_SyntaxError  -> true | uu____672 -> false
let uu___is_Fatal_SynthByTacticError: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_SynthByTacticError  -> true
    | uu____676 -> false
let uu___is_Fatal_TacticGotStuck: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_TacticGotStuck  -> true | uu____680 -> false
let uu___is_Fatal_TcOneFragmentFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_TcOneFragmentFailed  -> true
    | uu____684 -> false
let uu___is_Fatal_TermOutsideOfDefLanguage: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_TermOutsideOfDefLanguage  -> true
    | uu____688 -> false
let uu___is_Fatal_ToManyArgumentToFunction: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ToManyArgumentToFunction  -> true
    | uu____692 -> false
let uu___is_Fatal_TooManyOrTooFewFileMatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyOrTooFewFileMatch  -> true
    | uu____696 -> false
let uu___is_Fatal_TooManyPatternArguments: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyPatternArguments  -> true
    | uu____700 -> false
let uu___is_Fatal_TooManyUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyUniverse  -> true
    | uu____704 -> false
let uu___is_Fatal_TypeMismatch: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_TypeMismatch  -> true | uu____708 -> false
let uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_TypeWithinPatternsAllowedOnVariablesOnly  -> true
    | uu____712 -> false
let uu___is_Fatal_UnableToReadFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnableToReadFile  -> true
    | uu____716 -> false
let uu___is_Fatal_UnepxectedOrUnboundOperator: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnepxectedOrUnboundOperator  -> true
    | uu____720 -> false
let uu___is_Fatal_UnexpectedBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedBinder  -> true
    | uu____724 -> false
let uu___is_Fatal_UnexpectedBindShape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedBindShape  -> true
    | uu____728 -> false
let uu___is_Fatal_UnexpectedChar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_UnexpectedChar  -> true | uu____732 -> false
let uu___is_Fatal_UnexpectedComputationTypeForLetRec: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedComputationTypeForLetRec  -> true
    | uu____736 -> false
let uu___is_Fatal_UnexpectedConstructorType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedConstructorType  -> true
    | uu____740 -> false
let uu___is_Fatal_UnexpectedDataConstructor: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedDataConstructor  -> true
    | uu____744 -> false
let uu___is_Fatal_UnexpectedEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedEffect  -> true
    | uu____748 -> false
let uu___is_Fatal_UnexpectedEmptyRecord: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedEmptyRecord  -> true
    | uu____752 -> false
let uu___is_Fatal_UnexpectedExpressionType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedExpressionType  -> true
    | uu____756 -> false
let uu___is_Fatal_UnexpectedFunctionParameterType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedFunctionParameterType  -> true
    | uu____760 -> false
let uu___is_Fatal_UnexpectedGeneralizedUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGeneralizedUniverse  -> true
    | uu____764 -> false
let uu___is_Fatal_UnexpectedGTotForLetRec: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGTotForLetRec  -> true
    | uu____768 -> false
let uu___is_Fatal_UnexpectedGuard: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGuard  -> true
    | uu____772 -> false
let uu___is_Fatal_UnexpectedIdentifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedIdentifier  -> true
    | uu____776 -> false
let uu___is_Fatal_UnexpectedImplicitArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedImplicitArgument  -> true
    | uu____780 -> false
let uu___is_Fatal_UnexpectedImplictArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedImplictArgument  -> true
    | uu____784 -> false
let uu___is_Fatal_UnexpectedInductivetype: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedInductivetype  -> true
    | uu____788 -> false
let uu___is_Fatal_UnexpectedLetBinding: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedLetBinding  -> true
    | uu____792 -> false
let uu___is_Fatal_UnexpectedModuleDeclaration: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedModuleDeclaration  -> true
    | uu____796 -> false
let uu___is_Fatal_UnexpectedNumberOfUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedNumberOfUniverse  -> true
    | uu____800 -> false
let uu___is_Fatal_UnexpectedNumericLiteral: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedNumericLiteral  -> true
    | uu____804 -> false
let uu___is_Fatal_UnexpectedOperatorSymbol: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedOperatorSymbol  -> true
    | uu____808 -> false
let uu___is_Fatal_UnexpectedPattern: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedPattern  -> true
    | uu____812 -> false
let uu___is_Fatal_UnexpectedPosition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedPosition  -> true
    | uu____816 -> false
let uu___is_Fatal_UnExpectedPreCondition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnExpectedPreCondition  -> true
    | uu____820 -> false
let uu___is_Fatal_UnexpectedReturnShape: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedReturnShape  -> true
    | uu____824 -> false
let uu___is_Fatal_UnexpectedSignatureForMonad: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedSignatureForMonad  -> true
    | uu____828 -> false
let uu___is_Fatal_UnexpectedTerm: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_UnexpectedTerm  -> true | uu____832 -> false
let uu___is_Fatal_UnexpectedTermInUniverse: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermInUniverse  -> true
    | uu____836 -> false
let uu___is_Fatal_UnexpectedTermType: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermType  -> true
    | uu____840 -> false
let uu___is_Fatal_UnexpectedUniversePolymorphicReturn:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedUniversePolymorphicReturn  -> true
    | uu____844 -> false
let uu___is_Fatal_UnexpectedUniverseVariable: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedUniverseVariable  -> true
    | uu____848 -> false
let uu___is_Fatal_UnfoldableDeprecated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnfoldableDeprecated  -> true
    | uu____852 -> false
let uu___is_Fatal_UnificationNotWellFormed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnificationNotWellFormed  -> true
    | uu____856 -> false
let uu___is_Fatal_Uninstantiated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_Uninstantiated  -> true | uu____860 -> false
let uu___is_Fatal_UninstantiatedUnificationVarInTactic:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UninstantiatedUnificationVarInTactic  -> true
    | uu____864 -> false
let uu___is_Fatal_UninstantiatedVarInTactic: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UninstantiatedVarInTactic  -> true
    | uu____868 -> false
let uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UniverseMightContainSumOfTwoUnivVars  -> true
    | uu____872 -> false
let uu___is_Fatal_UniversePolymorphicInnerLetBound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UniversePolymorphicInnerLetBound  -> true
    | uu____876 -> false
let uu___is_Fatal_UnknownAttribute: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnknownAttribute  -> true
    | uu____880 -> false
let uu___is_Fatal_UnknownToolForDep: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnknownToolForDep  -> true
    | uu____884 -> false
let uu___is_Fatal_UnrecognizedExtension: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnrecognizedExtension  -> true
    | uu____888 -> false
let uu___is_Fatal_UnresolvedPatternVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnresolvedPatternVar  -> true
    | uu____892 -> false
let uu___is_Fatal_UnsupportedConstant: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedConstant  -> true
    | uu____896 -> false
let uu___is_Fatal_UnsupportedDisjuctivePatterns: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedDisjuctivePatterns  -> true
    | uu____900 -> false
let uu___is_Fatal_UnsupportedQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedQualifier  -> true
    | uu____904 -> false
let uu___is_Fatal_UserTacticFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_UserTacticFailure  -> true
    | uu____908 -> false
let uu___is_Fatal_ValueRestriction: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_ValueRestriction  -> true
    | uu____912 -> false
let uu___is_Fatal_VariableNotFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_VariableNotFound  -> true
    | uu____916 -> false
let uu___is_Fatal_WrongBodyTypeForReturnWP: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_WrongBodyTypeForReturnWP  -> true
    | uu____920 -> false
let uu___is_Fatal_WrongDataAppHeadFormat: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_WrongDataAppHeadFormat  -> true
    | uu____924 -> false
let uu___is_Fatal_WrongDefinitionOrder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_WrongDefinitionOrder  -> true
    | uu____928 -> false
let uu___is_Fatal_WrongResultTypeAfterConstrutor: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_WrongResultTypeAfterConstrutor  -> true
    | uu____932 -> false
let uu___is_Fatal_WrongTerm: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Fatal_WrongTerm  -> true | uu____936 -> false
let uu___is_Fatal_WhenClauseNotSupported: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_WhenClauseNotSupported  -> true
    | uu____940 -> false
let uu___is_Fatal_CallNotImplemented: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Fatal_CallNotImplemented  -> true
    | uu____944 -> false
let uu___is_Warning_AddImplicitAssumeNewQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_AddImplicitAssumeNewQualifier  -> true
    | uu____948 -> false
let uu___is_Warning_AdmitWithoutDefinition: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_AdmitWithoutDefinition  -> true
    | uu____952 -> false
let uu___is_Warning_CachedFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning_CachedFile  -> true | uu____956 -> false
let uu___is_Warning_DefinitionNotTranslated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_DefinitionNotTranslated  -> true
    | uu____960 -> false
let uu___is_Warning_DependencyFound: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_DependencyFound  -> true
    | uu____964 -> false
let uu___is_Warning_DeprecatedEqualityOnBinder: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedEqualityOnBinder  -> true
    | uu____968 -> false
let uu___is_Warning_DeprecatedOpaqueQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedOpaqueQualifier  -> true
    | uu____972 -> false
let uu___is_Warning_DocOverwrite: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning_DocOverwrite  -> true | uu____976 -> false
let uu___is_Warning_FileNotWritten: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_FileNotWritten  -> true
    | uu____980 -> false
let uu___is_Warning_Filtered: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning_Filtered  -> true | uu____984 -> false
let uu___is_Warning_FunctionLiteralPrecisionLoss: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_FunctionLiteralPrecisionLoss  -> true
    | uu____988 -> false
let uu___is_Warning_FunctionNotExtacted: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_FunctionNotExtacted  -> true
    | uu____992 -> false
let uu___is_Warning_HintFailedToReplayProof: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_HintFailedToReplayProof  -> true
    | uu____996 -> false
let uu___is_Warning_HitReplayFailed: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_HitReplayFailed  -> true
    | uu____1000 -> false
let uu___is_Warning_IDEIgnoreCodeGen: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_IDEIgnoreCodeGen  -> true
    | uu____1004 -> false
let uu___is_Warning_IllFormedGoal: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_IllFormedGoal  -> true
    | uu____1008 -> false
let uu___is_Warning_InaccessibleArgument: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_InaccessibleArgument  -> true
    | uu____1012 -> false
let uu___is_Warning_IncoherentImplicitQualifier: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_IncoherentImplicitQualifier  -> true
    | uu____1016 -> false
let uu___is_Warning_IrrelevantQualifierOnArgumentToReflect:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReflect  -> true
    | uu____1020 -> false
let uu___is_Warning_IrrelevantQualifierOnArgumentToReify:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReify  -> true
    | uu____1024 -> false
let uu___is_Warning_MalformedWarnErrorList: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_MalformedWarnErrorList  -> true
    | uu____1028 -> false
let uu___is_Warning_MetaAlienNotATmUnknown: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_MetaAlienNotATmUnknown  -> true
    | uu____1032 -> false
let uu___is_Warning_MultipleAscriptions: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_MultipleAscriptions  -> true
    | uu____1036 -> false
let uu___is_Warning_NondependentUserDefinedDataType: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Warning_NondependentUserDefinedDataType  -> true
    | uu____1040 -> false
let uu___is_Warning_NonListLiteralSMTPattern: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_NonListLiteralSMTPattern  -> true
    | uu____1044 -> false
let uu___is_Warning_NormalizationFailure: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_NormalizationFailure  -> true
    | uu____1048 -> false
let uu___is_Warning_NotDependentArrow: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_NotDependentArrow  -> true
    | uu____1052 -> false
let uu___is_Warning_NotEmbedded: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning_NotEmbedded  -> true | uu____1056 -> false
let uu___is_Warning_PatternMissingBoundVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_PatternMissingBoundVar  -> true
    | uu____1060 -> false
let uu___is_Warning_RecursiveDependency: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_RecursiveDependency  -> true
    | uu____1064 -> false
let uu___is_Warning_RedundantExplicitCurrying: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_RedundantExplicitCurrying  -> true
    | uu____1068 -> false
let uu___is_Warning_SMTPatTDeprecated: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_SMTPatTDeprecated  -> true
    | uu____1072 -> false
let uu___is_Warning_SMTPatternMissingBoundVar: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_SMTPatternMissingBoundVar  -> true
    | uu____1076 -> false
let uu___is_Warning_TopLevelEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_TopLevelEffect  -> true
    | uu____1080 -> false
let uu___is_Warning_UnboundModuleReference: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UnboundModuleReference  -> true
    | uu____1084 -> false
let uu___is_Warning_UnexpectedFile: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedFile  -> true
    | uu____1088 -> false
let uu___is_Warning_UnexpectedFsTypApp: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedFsTypApp  -> true
    | uu____1092 -> false
let uu___is_Warning_UnexpectedZ3Output: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedZ3Output  -> true
    | uu____1096 -> false
let uu___is_Warning_UnprotectedTerm: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UnprotectedTerm  -> true
    | uu____1100 -> false
let uu___is_Warning_UnrecognizedAttribute: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UnrecognizedAttribute  -> true
    | uu____1104 -> false
let uu___is_Warning_UpperBoundCandidateAlreadyVisited:
  raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UpperBoundCandidateAlreadyVisited  -> true
    | uu____1108 -> false
let uu___is_Warning_UseDefaultEffect: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_UseDefaultEffect  -> true
    | uu____1112 -> false
let uu___is_Warning_WrongErrorLocation: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_WrongErrorLocation  -> true
    | uu____1116 -> false
let uu___is_Warning_Z3InvocationWarning: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_Z3InvocationWarning  -> true
    | uu____1120 -> false
let uu___is_Warning_CallNotImplementedAsWarning: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_CallNotImplementedAsWarning  -> true
    | uu____1124 -> false
let uu___is_Warning_MissingInterfaceOrImplementation: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Warning_MissingInterfaceOrImplementation  -> true
    | uu____1128 -> false
let uu___is_Warning_ConstructorBuildsUnexpectedType: raw_error -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | Warning_ConstructorBuildsUnexpectedType  -> true
    | uu____1132 -> false
let uu___is_Warning_ModuleOrFileNotFoundWarning: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Warning_ModuleOrFileNotFoundWarning  -> true
    | uu____1136 -> false
let uu___is_Error_NoLetMutable: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_NoLetMutable  -> true | uu____1140 -> false
let uu___is_Error_BadImplicit: raw_error -> Prims.bool =
  fun projectee  ->
    match projectee with | Error_BadImplicit  -> true | uu____1144 -> false
type flag =
  | CError
  | CFatal
  | CWarning
  | CSilent[@@deriving show]
let uu___is_CError: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CError  -> true | uu____1148 -> false
let uu___is_CFatal: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____1152 -> false
let uu___is_CWarning: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____1156 -> false
let uu___is_CSilent: flag -> Prims.bool =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____1160 -> false
let default_flags: (raw_error,flag) FStar_Pervasives_Native.tuple2 Prims.list
  =
  [(Error_DependencyAnalysisFailed, CError);
  (Error_IDETooManyPops, CError);
  (Error_IDEUnrecognized, CError);
  (Error_InductiveTypeNotSatisfyPositivityCondition, CError);
  (Error_InvalidUniverseVar, CError);
  (Error_MissingFileName, CError);
  (Error_ModuleFileNameMismatch, CError);
  (Error_OpPlusInUniverse, CError);
  (Error_OutOfRange, CError);
  (Error_ProofObligationFailed, CError);
  (Error_TooManyFiles, CError);
  (Error_TypeCheckerFailToProve, CError);
  (Error_TypeError, CError);
  (Error_UncontrainedUnificationVar, CError);
  (Error_UnexpectedGTotComputation, CError);
  (Error_UnexpectedInstance, CError);
  (Error_UnknownFatal_AssertionFailure, CError);
  (Error_Z3InvocationError, CError);
  (Error_IDEAssertionFailure, CError);
  (Error_Z3SolverError, CError);
  (Fatal_AbstractTypeDeclarationInInterface, CFatal);
  (Fatal_ActionMustHaveFunctionType, CFatal);
  (Fatal_AlreadyDefinedTopLevelDeclaration, CFatal);
  (Fatal_ArgumentLengthMismatch, CFatal);
  (Fatal_AssertionFailure, CFatal);
  (Fatal_AssignToImmutableValues, CFatal);
  (Fatal_AssumeValInInterface, CFatal);
  (Fatal_BadlyInstantiatedSynthByTactic, CFatal);
  (Fatal_BadSignatureShape, CFatal);
  (Fatal_BinderAndArgsLengthMismatch, CFatal);
  (Fatal_BothValAndLetInInterface, CFatal);
  (Fatal_CardinalityConstraintViolated, CFatal);
  (Fatal_ComputationNotTotal, CFatal);
  (Fatal_ComputationTypeNotAllowed, CFatal);
  (Fatal_ComputedTypeNotMatchAnnotation, CFatal);
  (Fatal_ConstructorArgLengthMismatch, CFatal);
  (Fatal_ConstructorFailedCheck, CFatal);
  (Fatal_ConstructorNotFound, CFatal);
  (Fatal_ConstsructorBuildWrongType, CFatal);
  (Fatal_CycleInRecTypeAbbreviation, CFatal);
  (Fatal_DataContructorNotFound, CFatal);
  (Fatal_DefaultQualifierNotAllowedOnEffects, CFatal);
  (Fatal_DefinitionNotFound, CFatal);
  (Fatal_DisjuctivePatternVarsMismatch, CFatal);
  (Fatal_DivergentComputationCannotBeIncludedInTotal, CFatal);
  (Fatal_DuplicateInImplementation, CFatal);
  (Fatal_DuplicateModuleOrInterface, CFatal);
  (Fatal_DuplicateTopLevelNames, CFatal);
  (Fatal_DuplicateTypeAnnotationAndValDecl, CFatal);
  (Fatal_EffectCannotBeReified, CFatal);
  (Fatal_EffectConstructorNotFullyApplied, CFatal);
  (Fatal_EffectfulAndPureComputationMismatch, CFatal);
  (Fatal_EffectNotFound, CFatal);
  (Fatal_EffectsCannotBeComposed, CFatal);
  (Fatal_ErrorInSolveDeferredConstraints, CFatal);
  (Fatal_ErrorsReported, CFatal);
  (Fatal_EscapedBoundVar, CFatal);
  (Fatal_ExpectedArrowAnnotatedType, CFatal);
  (Fatal_ExpectedGhostExpression, CFatal);
  (Fatal_ExpectedPureExpression, CFatal);
  (Fatal_ExpectNormalizedEffect, CFatal);
  (Fatal_ExpectTermGotFunction, CFatal);
  (Fatal_ExpectTrivialPreCondition, CFatal);
  (Fatal_FailToCompileNativeTactic, CFatal);
  (Fatal_FailToProcessPragma, CFatal);
  (Fatal_FailToResolveImplicitArgument, CFatal);
  (Fatal_FailToSolveUniverseInEquality, CFatal);
  (Fatal_FieldsNotBelongToSameRecordType, CFatal);
  (Fatal_ForbiddenReferenceToCurrentModule, CFatal);
  (Fatal_FreeVariables, CFatal);
  (Fatal_FunctionTypeExpected, CFatal);
  (Fatal_IdentifierNotFound, CFatal);
  (Fatal_IllAppliedConstant, CFatal);
  (Fatal_IllegalCharInByteArray, CFatal);
  (Fatal_IllegalCharInOperatorName, CFatal);
  (Fatal_IllTyped, CFatal);
  (Fatal_ImpossibleAbbrevLidBundle, CFatal);
  (Fatal_ImpossibleAbbrevRenameBundle, CFatal);
  (Fatal_ImpossibleInductiveWithAbbrev, CFatal);
  (Fatal_ImpossiblePrePostAbs, CFatal);
  (Fatal_ImpossiblePrePostArrow, CFatal);
  (Fatal_ImpossibleToGenerateDMEffect, CFatal);
  (Fatal_ImpossibleTypeAbbrevBundle, CFatal);
  (Fatal_ImpossibleTypeAbbrevSigeltBundle, CFatal);
  (Fatal_IncludeModuleNotPrepared, CFatal);
  (Fatal_IncoherentInlineUniverse, CFatal);
  (Fatal_IncompatibleKinds, CFatal);
  (Fatal_IncompatibleNumberOfTypes, CFatal);
  (Fatal_IncompatibleSetOfUniverse, CFatal);
  (Fatal_IncompatibleUniverse, CFatal);
  (Fatal_InconsistentImplicitArgumentAnnotation, CFatal);
  (Fatal_InconsistentImplicitQualifier, CFatal);
  (Fatal_InconsistentQualifierAnnotation, CFatal);
  (Fatal_InferredTypeCauseVarEscape, CFatal);
  (Fatal_InlineRenamedAsUnfold, CFatal);
  (Fatal_InsufficientPatternArguments, CFatal);
  (Fatal_InterfaceAlreadyProcessed, CFatal);
  (Fatal_InterfaceNotImplementedByModule, CFatal);
  (Fatal_InterfaceWithTypeImplementation, CFatal);
  (Fatal_InvalidFloatingPointNumber, CFatal);
  (Fatal_InvalidFSDocKeyword, CFatal);
  (Fatal_InvalidIdentifier, CFatal);
  (Fatal_InvalidLemmaArgument, CFatal);
  (Fatal_InvalidNumericLiteral, CFatal);
  (Fatal_InvalidRedefinitionOfLexT, CFatal);
  (Fatal_InvalidUnicodeInStringLiteral, CFatal);
  (Fatal_InvalidUTF8Encoding, CFatal);
  (Fatal_InvalidWarnErrorSetting, CFatal);
  (Fatal_LetBoundMonadicMismatch, CFatal);
  (Fatal_LetMutableForVariablesOnly, CFatal);
  (Fatal_LetOpenModuleOnly, CFatal);
  (Fatal_LetRecArgumentMismatch, CFatal);
  (Fatal_MalformedActionDeclaration, CFatal);
  (Fatal_MismatchedPatternType, CFatal);
  (Fatal_MismatchUniversePolymorphic, CFatal);
  (Fatal_MissingDataConstructor, CFatal);
  (Fatal_MissingExposeInterfacesOption, CFatal);
  (Fatal_MissingFieldInRecord, CFatal);
  (Fatal_MissingImplementation, CFatal);
  (Fatal_MissingImplicitArguments, CFatal);
  (Fatal_MissingInterface, CFatal);
  (Fatal_MissingNameInBinder, CFatal);
  (Fatal_MissingPrimsModule, CFatal);
  (Fatal_MissingQuantifierBinder, CFatal);
  (Fatal_ModuleExpected, CFatal);
  (Fatal_ModuleFileNotFound, CFatal);
  (Fatal_ModuleFirstStatement, CFatal);
  (Fatal_ModuleNotFound, CFatal);
  (Fatal_ModuleOrFileNotFound, CFatal);
  (Fatal_MonadAlreadyDefined, CFatal);
  (Fatal_MoreThanOneDeclaration, CFatal);
  (Fatal_MultipleLetBinding, CFatal);
  (Fatal_NameNotFound, CFatal);
  (Fatal_NameSpaceNotFound, CFatal);
  (Fatal_NegativeUniverseConstFatal_NotSupported, CFatal);
  (Fatal_NoFileProvided, CFatal);
  (Fatal_NonInductiveInMutuallyDefinedType, CFatal);
  (Fatal_NonLinearPatternNotPermitted, CFatal);
  (Fatal_NonLinearPatternVars, CFatal);
  (Fatal_NonSingletonTopLevel, CFatal);
  (Fatal_NonSingletonTopLevelModule, CFatal);
  (Fatal_NonTopRecFunctionNotFullyEncoded, CFatal);
  (Fatal_NonTrivialPreConditionInPrims, CFatal);
  (Fatal_NonVariableInductiveTypeParameter, CFatal);
  (Fatal_NotApplicationOrFv, CFatal);
  (Fatal_NotEnoughArgsToEffect, CFatal);
  (Fatal_NotEnoughArgumentsForEffect, CFatal);
  (Fatal_NotFunctionType, CFatal);
  (Fatal_NotSupported, CFatal);
  (Fatal_NotTopLevelModule, CFatal);
  (Fatal_NotValidFStarFile, CFatal);
  (Fatal_NotValidIncludeDirectory, CFatal);
  (Fatal_OneModulePerFile, CFatal);
  (Fatal_OpenGoalsInSynthesis, CFatal);
  (Fatal_OptionsNotCompatible, CFatal);
  (Fatal_OutOfOrder, CFatal);
  (Fatal_ParseErrors, CFatal);
  (Fatal_ParseItError, CFatal);
  (Fatal_PolyTypeExpected, CFatal);
  (Fatal_PossibleInfiniteTyp, CFatal);
  (Fatal_PreModuleMismatch, CFatal);
  (Fatal_QulifierListNotPermitted, CFatal);
  (Fatal_RecursiveFunctionLiteral, CFatal);
  (Fatal_ReflectOnlySupportedOnEffects, CFatal);
  (Fatal_ReservedPrefix, CFatal);
  (Fatal_SMTOutputParseError, CFatal);
  (Fatal_SMTSolverError, CFatal);
  (Fatal_SyntaxError, CFatal);
  (Fatal_SynthByTacticError, CFatal);
  (Fatal_TacticGotStuck, CFatal);
  (Fatal_TcOneFragmentFailed, CFatal);
  (Fatal_TermOutsideOfDefLanguage, CFatal);
  (Fatal_ToManyArgumentToFunction, CFatal);
  (Fatal_TooManyOrTooFewFileMatch, CFatal);
  (Fatal_TooManyPatternArguments, CFatal);
  (Fatal_TooManyUniverse, CFatal);
  (Fatal_TypeMismatch, CFatal);
  (Fatal_TypeWithinPatternsAllowedOnVariablesOnly, CFatal);
  (Fatal_UnableToReadFile, CFatal);
  (Fatal_UnepxectedOrUnboundOperator, CFatal);
  (Fatal_UnexpectedBinder, CFatal);
  (Fatal_UnexpectedBindShape, CFatal);
  (Fatal_UnexpectedChar, CFatal);
  (Fatal_UnexpectedComputationTypeForLetRec, CFatal);
  (Fatal_UnexpectedConstructorType, CFatal);
  (Fatal_UnexpectedDataConstructor, CFatal);
  (Fatal_UnexpectedEffect, CFatal);
  (Fatal_UnexpectedEmptyRecord, CFatal);
  (Fatal_UnexpectedExpressionType, CFatal);
  (Fatal_UnexpectedFunctionParameterType, CFatal);
  (Fatal_UnexpectedGeneralizedUniverse, CFatal);
  (Fatal_UnexpectedGTotForLetRec, CFatal);
  (Fatal_UnexpectedGuard, CFatal);
  (Fatal_UnexpectedIdentifier, CFatal);
  (Fatal_UnexpectedImplicitArgument, CFatal);
  (Fatal_UnexpectedImplictArgument, CFatal);
  (Fatal_UnexpectedInductivetype, CFatal);
  (Fatal_UnexpectedLetBinding, CFatal);
  (Fatal_UnexpectedModuleDeclaration, CFatal);
  (Fatal_UnexpectedNumberOfUniverse, CFatal);
  (Fatal_UnexpectedNumericLiteral, CFatal);
  (Fatal_UnexpectedOperatorSymbol, CFatal);
  (Fatal_UnexpectedPattern, CFatal);
  (Fatal_UnexpectedPosition, CFatal);
  (Fatal_UnExpectedPreCondition, CFatal);
  (Fatal_UnexpectedReturnShape, CFatal);
  (Fatal_UnexpectedSignatureForMonad, CFatal);
  (Fatal_UnexpectedTerm, CFatal);
  (Fatal_UnexpectedTermInUniverse, CFatal);
  (Fatal_UnexpectedTermType, CFatal);
  (Fatal_UnexpectedUniversePolymorphicReturn, CFatal);
  (Fatal_UnexpectedUniverseVariable, CFatal);
  (Fatal_UnfoldableDeprecated, CFatal);
  (Fatal_UnificationNotWellFormed, CFatal);
  (Fatal_Uninstantiated, CFatal);
  (Fatal_UninstantiatedUnificationVarInTactic, CFatal);
  (Fatal_UninstantiatedVarInTactic, CFatal);
  (Fatal_UniverseMightContainSumOfTwoUnivVars, CFatal);
  (Fatal_UniversePolymorphicInnerLetBound, CFatal);
  (Fatal_UnknownAttribute, CFatal);
  (Fatal_UnknownToolForDep, CFatal);
  (Fatal_UnrecognizedExtension, CFatal);
  (Fatal_UnresolvedPatternVar, CFatal);
  (Fatal_UnsupportedConstant, CFatal);
  (Fatal_UnsupportedDisjuctivePatterns, CFatal);
  (Fatal_UnsupportedQualifier, CFatal);
  (Fatal_UserTacticFailure, CFatal);
  (Fatal_ValueRestriction, CFatal);
  (Fatal_VariableNotFound, CFatal);
  (Fatal_WrongBodyTypeForReturnWP, CFatal);
  (Fatal_WrongDataAppHeadFormat, CFatal);
  (Fatal_WrongDefinitionOrder, CFatal);
  (Fatal_WrongResultTypeAfterConstrutor, CFatal);
  (Fatal_WrongTerm, CFatal);
  (Fatal_WhenClauseNotSupported, CFatal);
  (Fatal_CallNotImplemented, CFatal);
  (Warning_CallNotImplementedAsWarning, CWarning);
  (Warning_AddImplicitAssumeNewQualifier, CWarning);
  (Warning_AdmitWithoutDefinition, CWarning);
  (Warning_CachedFile, CWarning);
  (Warning_DefinitionNotTranslated, CWarning);
  (Warning_DependencyFound, CWarning);
  (Warning_DeprecatedEqualityOnBinder, CWarning);
  (Warning_DeprecatedOpaqueQualifier, CWarning);
  (Warning_DocOverwrite, CWarning);
  (Warning_FileNotWritten, CWarning);
  (Warning_Filtered, CWarning);
  (Warning_FunctionLiteralPrecisionLoss, CWarning);
  (Warning_FunctionNotExtacted, CWarning);
  (Warning_HintFailedToReplayProof, CWarning);
  (Warning_HitReplayFailed, CWarning);
  (Warning_IDEIgnoreCodeGen, CWarning);
  (Warning_IllFormedGoal, CWarning);
  (Warning_InaccessibleArgument, CWarning);
  (Warning_IncoherentImplicitQualifier, CWarning);
  (Warning_IrrelevantQualifierOnArgumentToReflect, CWarning);
  (Warning_IrrelevantQualifierOnArgumentToReify, CWarning);
  (Warning_MalformedWarnErrorList, CWarning);
  (Warning_MetaAlienNotATmUnknown, CWarning);
  (Warning_MultipleAscriptions, CWarning);
  (Warning_NondependentUserDefinedDataType, CWarning);
  (Warning_NonListLiteralSMTPattern, CWarning);
  (Warning_NormalizationFailure, CWarning);
  (Warning_NotDependentArrow, CWarning);
  (Warning_NotEmbedded, CWarning);
  (Warning_PatternMissingBoundVar, CWarning);
  (Warning_RecursiveDependency, CWarning);
  (Warning_RedundantExplicitCurrying, CWarning);
  (Warning_SMTPatTDeprecated, CWarning);
  (Warning_SMTPatternMissingBoundVar, CWarning);
  (Warning_TopLevelEffect, CWarning);
  (Warning_UnboundModuleReference, CWarning);
  (Warning_UnexpectedFile, CWarning);
  (Warning_UnexpectedFsTypApp, CWarning);
  (Warning_UnexpectedZ3Output, CWarning);
  (Warning_UnprotectedTerm, CWarning);
  (Warning_UnrecognizedAttribute, CWarning);
  (Warning_UpperBoundCandidateAlreadyVisited, CWarning);
  (Warning_UseDefaultEffect, CWarning);
  (Warning_WrongErrorLocation, CWarning);
  (Warning_Z3InvocationWarning, CWarning);
  (Warning_MissingInterfaceOrImplementation, CWarning);
  (Warning_ConstructorBuildsUnexpectedType, CWarning);
  (Warning_ModuleOrFileNotFoundWarning, CWarning);
  (Error_BadImplicit, CError)]
exception Err of (raw_error,Prims.string) FStar_Pervasives_Native.tuple2
let uu___is_Err: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Err uu____2321 -> true | uu____2326 -> false
let __proj__Err__item__uu___:
  Prims.exn -> (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Err uu____2341 -> uu____2341
exception Error of (raw_error,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
let uu___is_Error: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Error uu____2358 -> true | uu____2365 -> false
let __proj__Error__item__uu___:
  Prims.exn ->
    (raw_error,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Error uu____2384 -> uu____2384
exception Warning of (raw_error,Prims.string,FStar_Range.range)
  FStar_Pervasives_Native.tuple3
let uu___is_Warning: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Warning uu____2403 -> true | uu____2410 -> false
let __proj__Warning__item__uu___:
  Prims.exn ->
    (raw_error,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Warning uu____2429 -> uu____2429
exception Stop
let uu___is_Stop: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Stop  -> true | uu____2439 -> false
exception Empty_frag
let uu___is_Empty_frag: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____2443 -> false
type issue_level =
  | ENotImplemented
  | EInfo
  | EWarning
  | EError[@@deriving show]
let uu___is_ENotImplemented: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____2447 -> false
let uu___is_EInfo: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EInfo  -> true | uu____2451 -> false
let uu___is_EWarning: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____2455 -> false
let uu___is_EError: issue_level -> Prims.bool =
  fun projectee  ->
    match projectee with | EError  -> true | uu____2459 -> false
type issue =
  {
  issue_message: Prims.string;
  issue_level: issue_level;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option;
  issue_number: Prims.int FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkissue__item__issue_message: issue -> Prims.string =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;
        issue_number = __fname__issue_number;_} -> __fname__issue_message
let __proj__Mkissue__item__issue_level: issue -> issue_level =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;
        issue_number = __fname__issue_number;_} -> __fname__issue_level
let __proj__Mkissue__item__issue_range:
  issue -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;
        issue_number = __fname__issue_number;_} -> __fname__issue_range
let __proj__Mkissue__item__issue_number:
  issue -> Prims.int FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { issue_message = __fname__issue_message;
        issue_level = __fname__issue_level;
        issue_range = __fname__issue_range;
        issue_number = __fname__issue_number;_} -> __fname__issue_number
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
      | EInfo  -> "Info"
      | EWarning  -> "Warning"
      | EError  -> "Error"
      | ENotImplemented  -> "Feature not yet implemented: " in
    let uu____2658 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____2668 =
            let uu____2669 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____2669 in
          let uu____2670 =
            let uu____2671 =
              let uu____2672 = FStar_Range.use_range r in
              let uu____2673 = FStar_Range.def_range r in
              uu____2672 = uu____2673 in
            if uu____2671
            then ""
            else
              (let uu____2675 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____2675) in
          (uu____2668, uu____2670) in
    match uu____2658 with
    | (range_str,see_also_str) ->
        let issue_number =
          match issue.issue_number with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some n1 ->
              let uu____2680 = FStar_Util.string_of_int n1 in
              FStar_Util.format1 " %s" uu____2680 in
        FStar_Util.format5 "%s(%s%s) %s%s\n" range_str level_header
          issue_number issue.issue_message see_also_str
let print_issue: issue -> Prims.unit =
  fun issue  ->
    let printer =
      match issue.issue_level with
      | EInfo  -> FStar_Util.print_string
      | EWarning  -> FStar_Util.print_warning
      | EError  -> FStar_Util.print_error
      | ENotImplemented  -> FStar_Util.print_error in
    let uu____2689 = format_issue issue in printer uu____2689
let compare_issues: issue -> issue -> Prims.int =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Prims.parse_int "0"
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____2704) -> - (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some uu____2709,FStar_Pervasives_Native.None
         ) -> Prims.parse_int "1"
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let default_handler: error_handler =
  let errs = FStar_Util.mk_ref [] in
  let add_one e =
    match e.issue_level with
    | EError  ->
        let uu____2731 =
          let uu____2734 = FStar_ST.op_Bang errs in e :: uu____2734 in
        FStar_ST.op_Colon_Equals errs uu____2731
    | uu____2827 -> print_issue e in
  let count_errors uu____2831 =
    let uu____2832 = FStar_ST.op_Bang errs in FStar_List.length uu____2832 in
  let report uu____2885 =
    let sorted1 =
      let uu____2889 = FStar_ST.op_Bang errs in
      FStar_List.sortWith compare_issues uu____2889 in
    FStar_List.iter print_issue sorted1; sorted1 in
  let clear1 uu____2941 = FStar_ST.op_Colon_Equals errs [] in
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
    FStar_Range.range FStar_Pervasives_Native.option ->
      Prims.string -> Prims.int FStar_Pervasives_Native.option -> issue
  =
  fun level  ->
    fun range  ->
      fun msg  ->
        fun n1  ->
          {
            issue_message = msg;
            issue_level = level;
            issue_range = range;
            issue_number = n1
          }
let get_err_count: Prims.unit -> Prims.int =
  fun uu____3026  ->
    let uu____3027 =
      let uu____3030 = FStar_ST.op_Bang current_handler in
      uu____3030.eh_count_errors in
    uu____3027 ()
let add_one: issue -> Prims.unit =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____3055  ->
         let uu____3056 =
           let uu____3059 = FStar_ST.op_Bang current_handler in
           uu____3059.eh_add_one in
         uu____3056 issue)
let add_many: issue Prims.list -> Prims.unit =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____3088  ->
         let uu____3089 =
           let uu____3092 = FStar_ST.op_Bang current_handler in
           uu____3092.eh_add_one in
         FStar_List.iter uu____3089 issues)
let report_all: Prims.unit -> issue Prims.list =
  fun uu____3116  ->
    let uu____3117 =
      let uu____3122 = FStar_ST.op_Bang current_handler in
      uu____3122.eh_report in
    uu____3117 ()
let clear: Prims.unit -> Prims.unit =
  fun uu____3144  ->
    let uu____3145 =
      let uu____3148 = FStar_ST.op_Bang current_handler in
      uu____3148.eh_clear in
    uu____3145 ()
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
  let clear_prefix uu____3326 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None in
  let append_prefix s =
    let uu____3376 = FStar_ST.op_Bang pfx in
    match uu____3376 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p -> Prims.strcat p (Prims.strcat ": " s) in
  { set_prefix; append_prefix; clear_prefix }
let findIndex:
  'Auu____3429 'Auu____3430 .
    ('Auu____3430,'Auu____3429) FStar_Pervasives_Native.tuple2 Prims.list ->
      'Auu____3430 -> Prims.int
  =
  fun l  ->
    fun v1  ->
      FStar_All.pipe_right l
        (FStar_List.index
           (fun uu___26_3464  ->
              match uu___26_3464 with
              | (e,uu____3470) when e = v1 -> true
              | uu____3471 -> false))
let errno_of_error: raw_error -> Prims.int =
  fun e  -> findIndex default_flags e
let flags: flag Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_warn_error_flags: Prims.unit =
  let rec aux r l =
    match l with | [] -> r | (e,f)::tl1 -> aux (FStar_List.append r [f]) tl1 in
  let uu____3540 = aux [] default_flags in
  FStar_ST.op_Colon_Equals flags uu____3540
let diag: FStar_Range.range -> Prims.string -> Prims.unit =
  fun r  ->
    fun msg  ->
      let uu____3572 = FStar_Options.debug_any () in
      if uu____3572
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None)
      else ()
let log_issue:
  FStar_Range.range ->
    (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 -> Prims.unit
  =
  fun r  ->
    fun uu____3583  ->
      match uu____3583 with
      | (e,msg) ->
          let errno = errno_of_error e in
          let uu____3591 =
            let uu____3592 = FStar_ST.op_Bang flags in
            FStar_List.nth uu____3592 errno in
          (match uu____3591 with
           | CError  ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | CWarning  ->
               add_one
                 (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | CSilent  -> ()
           | CFatal  ->
               let i =
                 mk_issue EError (FStar_Pervasives_Native.Some r) msg
                   (FStar_Pervasives_Native.Some errno) in
               let uu____3619 = FStar_Options.ide () in
               if uu____3619
               then add_one i
               else
                 (let uu____3621 =
                    let uu____3622 = format_issue i in
                    Prims.strcat
                      "don't use log_issue to report fatal error, should use raise_error: "
                      uu____3622 in
                  failwith uu____3621))
let add_errors:
  (raw_error,Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple3
    Prims.list -> Prims.unit
  =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____3643  ->
         FStar_List.iter
           (fun uu____3655  ->
              match uu____3655 with
              | (e,msg,r) ->
                  let uu____3665 =
                    let uu____3670 = message_prefix.append_prefix msg in
                    (e, uu____3670) in
                  log_issue r uu____3665) errs)
let issue_of_exn: Prims.exn -> issue FStar_Pervasives_Native.option =
  fun uu___27_3675  ->
    match uu___27_3675 with
    | Error (e,msg,r) ->
        let errno = errno_of_error e in
        let uu____3682 =
          let uu____3683 = message_prefix.append_prefix msg in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____3683
            (FStar_Pervasives_Native.Some errno) in
        FStar_Pervasives_Native.Some uu____3682
    | FStar_Util.NYI msg ->
        let uu____3685 =
          let uu____3686 = message_prefix.append_prefix msg in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____3686
            FStar_Pervasives_Native.None in
        FStar_Pervasives_Native.Some uu____3685
    | Err (e,msg) ->
        let errno = errno_of_error e in
        let uu____3690 =
          let uu____3691 = message_prefix.append_prefix msg in
          mk_issue EError FStar_Pervasives_Native.None uu____3691
            (FStar_Pervasives_Native.Some errno) in
        FStar_Pervasives_Native.Some uu____3690
    | uu____3692 -> FStar_Pervasives_Native.None
let err_exn: Prims.exn -> Prims.unit =
  fun exn  ->
    if exn = Stop
    then ()
    else
      (let uu____3697 = issue_of_exn exn in
       match uu____3697 with
       | FStar_Pervasives_Native.Some issue -> add_one issue
       | FStar_Pervasives_Native.None  -> FStar_Exn.raise exn)
let handleable: Prims.exn -> Prims.bool =
  fun uu___28_3703  ->
    match uu___28_3703 with
    | Error uu____3704 -> true
    | FStar_Util.NYI uu____3711 -> true
    | Stop  -> true
    | Err uu____3712 -> true
    | uu____3717 -> false
let stop_if_err: Prims.unit -> Prims.unit =
  fun uu____3720  ->
    let uu____3721 =
      let uu____3722 = get_err_count () in uu____3722 > (Prims.parse_int "0") in
    if uu____3721 then FStar_Exn.raise Stop else ()
let raise_error:
  'Auu____3727 .
    (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 ->
      FStar_Range.range -> 'Auu____3727
  =
  fun uu____3738  ->
    fun r  ->
      match uu____3738 with | (e,msg) -> FStar_Exn.raise (Error (e, msg, r))
let raise_err:
  'Auu____3748 .
    (raw_error,Prims.string) FStar_Pervasives_Native.tuple2 -> 'Auu____3748
  =
  fun uu____3756  ->
    match uu____3756 with | (e,msg) -> FStar_Exn.raise (Err (e, msg))
let update_flags:
  (flag,Prims.string) FStar_Pervasives_Native.tuple2 Prims.list -> Prims.unit
  =
  fun l  ->
    let compare1 uu____3799 uu____3800 =
      match (uu____3799, uu____3800) with
      | ((uu____3833,(a,uu____3835)),(uu____3836,(b,uu____3838))) ->
          if a > b
          then Prims.parse_int "1"
          else if a < b then - (Prims.parse_int "1") else Prims.parse_int "0" in
    let set_one_flag f d =
      match (f, d) with
      | (CWarning ,CError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot turn an error into warning")
      | (CSilent ,CError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting, "cannot silence an error")
      | (uu____3872,CFatal ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot reset the error level of a fatal error")
      | uu____3873 -> f in
    let rec set_flag i l1 =
      let d =
        let uu____3906 = FStar_ST.op_Bang flags in
        FStar_List.nth uu____3906 i in
      match l1 with
      | [] -> d
      | (f,(l2,h))::tl1 ->
          if (i >= l2) && (i <= h)
          then set_one_flag f d
          else if i < l2 then d else set_flag i tl1 in
    let rec aux f i l1 sorted1 =
      match l1 with
      | [] -> f
      | hd1::tl1 ->
          let uu____4017 =
            let uu____4020 =
              let uu____4023 = set_flag i sorted1 in [uu____4023] in
            FStar_List.append f uu____4020 in
          aux uu____4017 (i + (Prims.parse_int "1")) tl1 sorted1 in
    let rec compute_range result l1 =
      match l1 with
      | [] -> result
      | (f,s)::tl1 ->
          let r = FStar_Util.split s ".." in
          let uu____4103 =
            match r with
            | r1::r2::[] ->
                let uu____4114 = FStar_Util.int_of_string r1 in
                let uu____4115 = FStar_Util.int_of_string r2 in
                (uu____4114, uu____4115)
            | uu____4116 ->
                let uu____4119 =
                  let uu____4124 =
                    FStar_Util.format1 "Malformed warn-error range %s" s in
                  (Fatal_InvalidWarnErrorSetting, uu____4124) in
                raise_err uu____4119 in
          (match uu____4103 with
           | (l2,h) ->
               (if
                  (l2 < (Prims.parse_int "0")) ||
                    (h >= (FStar_List.length default_flags))
                then
                  (let uu____4146 =
                     let uu____4151 =
                       let uu____4152 = FStar_Util.string_of_int l2 in
                       let uu____4153 = FStar_Util.string_of_int h in
                       FStar_Util.format2 "No error for warn_error %s..%s"
                         uu____4152 uu____4153 in
                     (Fatal_InvalidWarnErrorSetting, uu____4151) in
                   raise_err uu____4146)
                else ();
                compute_range (FStar_List.append result [(f, (l2, h))]) tl1)) in
    let range = compute_range [] l in
    let sorted1 = FStar_List.sortWith compare1 range in
    let uu____4221 =
      let uu____4224 = FStar_ST.op_Bang flags in
      aux [] (Prims.parse_int "0") uu____4224 sorted1 in
    FStar_ST.op_Colon_Equals flags uu____4221