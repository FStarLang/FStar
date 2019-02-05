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
  | Fatal_FailToExtractNativeTactic 
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
  | Fatal_UnexpectedTermVQuote 
  | Fatal_UnexpectedUniversePolymorphicReturn 
  | Fatal_UnexpectedUniverseVariable 
  | Fatal_UnfoldableDeprecated 
  | Fatal_UnificationNotWellFormed 
  | Fatal_Uninstantiated 
  | Error_UninstantiatedUnificationVarInTactic 
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
  | Unused01 
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
  | Error_BadImplicit 
  | Warning_DeprecatedDefinition 
  | Fatal_SMTEncodingArityMismatch 
  | Warning_Defensive 
  | Warning_CantInspect 
  | Warning_NilGivenExplicitArgs 
  | Warning_ConsAppliedExplicitArgs 
  | Warning_UnembedBinderKnot 
  | Fatal_TacticProofRelevantGoal 
  | Warning_TacAdmit 
  | Fatal_IncoherentPatterns 
  | Error_NoSMTButNeeded 
  | Fatal_UnexpectedAntiquotation 
  | Fatal_SplicedUndef 
  | Fatal_SpliceUnembedFail 
  | Warning_ExtractionUnexpectedEffect 
  | Error_DidNotFail 
  | Warning_UnappliedFail 
  | Warning_QuantifierWithoutPattern 
  | Error_EmptyFailErrs 
  | Warning_logicqualifier 
  | Fatal_CyclicDependence 
  | Error_InductiveAnnotNotAType 
  | Fatal_FriendInterface 
  | Error_CannotRedefineConst 
  | Error_BadClassDecl 
  | Error_BadInductiveParam 
  | Error_FieldShadow 
  | Error_UnexpectedDM4FType 
  | Fatal_EffectAbbreviationResultTypeMismatch 
  | Error_AlreadyCachedAssertionFailure 
  | Error_MustEraseMissing 
  | Warning_EffectfulArgumentToErasedFunction 
  | Fatal_EmptySurfaceLet 
let (uu___is_Error_DependencyAnalysisFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_DependencyAnalysisFailed  -> true
    | uu____9 -> false
  
let (uu___is_Error_IDETooManyPops : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_IDETooManyPops  -> true | uu____20 -> false
  
let (uu___is_Error_IDEUnrecognized : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_IDEUnrecognized  -> true | uu____31 -> false
  
let (uu___is_Error_InductiveTypeNotSatisfyPositivityCondition :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_InductiveTypeNotSatisfyPositivityCondition  -> true
    | uu____42 -> false
  
let (uu___is_Error_InvalidUniverseVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_InvalidUniverseVar  -> true
    | uu____53 -> false
  
let (uu___is_Error_MissingFileName : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_MissingFileName  -> true | uu____64 -> false
  
let (uu___is_Error_ModuleFileNameMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_ModuleFileNameMismatch  -> true
    | uu____75 -> false
  
let (uu___is_Error_OpPlusInUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_OpPlusInUniverse  -> true
    | uu____86 -> false
  
let (uu___is_Error_OutOfRange : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_OutOfRange  -> true | uu____97 -> false
  
let (uu___is_Error_ProofObligationFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_ProofObligationFailed  -> true
    | uu____108 -> false
  
let (uu___is_Error_TooManyFiles : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_TooManyFiles  -> true | uu____119 -> false
  
let (uu___is_Error_TypeCheckerFailToProve : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_TypeCheckerFailToProve  -> true
    | uu____130 -> false
  
let (uu___is_Error_TypeError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_TypeError  -> true | uu____141 -> false
  
let (uu___is_Error_UncontrainedUnificationVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UncontrainedUnificationVar  -> true
    | uu____152 -> false
  
let (uu___is_Error_UnexpectedGTotComputation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedGTotComputation  -> true
    | uu____163 -> false
  
let (uu___is_Error_UnexpectedInstance : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedInstance  -> true
    | uu____174 -> false
  
let (uu___is_Error_UnknownFatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnknownFatal_AssertionFailure  -> true
    | uu____185 -> false
  
let (uu___is_Error_Z3InvocationError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_Z3InvocationError  -> true
    | uu____196 -> false
  
let (uu___is_Error_IDEAssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_IDEAssertionFailure  -> true
    | uu____207 -> false
  
let (uu___is_Error_Z3SolverError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_Z3SolverError  -> true | uu____218 -> false
  
let (uu___is_Fatal_AbstractTypeDeclarationInInterface :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AbstractTypeDeclarationInInterface  -> true
    | uu____229 -> false
  
let (uu___is_Fatal_ActionMustHaveFunctionType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ActionMustHaveFunctionType  -> true
    | uu____240 -> false
  
let (uu___is_Fatal_AlreadyDefinedTopLevelDeclaration :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AlreadyDefinedTopLevelDeclaration  -> true
    | uu____251 -> false
  
let (uu___is_Fatal_ArgumentLengthMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ArgumentLengthMismatch  -> true
    | uu____262 -> false
  
let (uu___is_Fatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AssertionFailure  -> true
    | uu____273 -> false
  
let (uu___is_Fatal_AssignToImmutableValues : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AssignToImmutableValues  -> true
    | uu____284 -> false
  
let (uu___is_Fatal_AssumeValInInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AssumeValInInterface  -> true
    | uu____295 -> false
  
let (uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_BadlyInstantiatedSynthByTactic  -> true
    | uu____306 -> false
  
let (uu___is_Fatal_BadSignatureShape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_BadSignatureShape  -> true
    | uu____317 -> false
  
let (uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_BinderAndArgsLengthMismatch  -> true
    | uu____328 -> false
  
let (uu___is_Fatal_BothValAndLetInInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_BothValAndLetInInterface  -> true
    | uu____339 -> false
  
let (uu___is_Fatal_CardinalityConstraintViolated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_CardinalityConstraintViolated  -> true
    | uu____350 -> false
  
let (uu___is_Fatal_ComputationNotTotal : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ComputationNotTotal  -> true
    | uu____361 -> false
  
let (uu___is_Fatal_ComputationTypeNotAllowed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ComputationTypeNotAllowed  -> true
    | uu____372 -> false
  
let (uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_ComputedTypeNotMatchAnnotation  -> true
    | uu____383 -> false
  
let (uu___is_Fatal_ConstructorArgLengthMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorArgLengthMismatch  -> true
    | uu____394 -> false
  
let (uu___is_Fatal_ConstructorFailedCheck : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorFailedCheck  -> true
    | uu____405 -> false
  
let (uu___is_Fatal_ConstructorNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorNotFound  -> true
    | uu____416 -> false
  
let (uu___is_Fatal_ConstsructorBuildWrongType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstsructorBuildWrongType  -> true
    | uu____427 -> false
  
let (uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_CycleInRecTypeAbbreviation  -> true
    | uu____438 -> false
  
let (uu___is_Fatal_DataContructorNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DataContructorNotFound  -> true
    | uu____449 -> false
  
let (uu___is_Fatal_DefaultQualifierNotAllowedOnEffects :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DefaultQualifierNotAllowedOnEffects  -> true
    | uu____460 -> false
  
let (uu___is_Fatal_DefinitionNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DefinitionNotFound  -> true
    | uu____471 -> false
  
let (uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DisjuctivePatternVarsMismatch  -> true
    | uu____482 -> false
  
let (uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DivergentComputationCannotBeIncludedInTotal  -> true
    | uu____493 -> false
  
let (uu___is_Fatal_DuplicateInImplementation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateInImplementation  -> true
    | uu____504 -> false
  
let (uu___is_Fatal_DuplicateModuleOrInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateModuleOrInterface  -> true
    | uu____515 -> false
  
let (uu___is_Fatal_DuplicateTopLevelNames : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateTopLevelNames  -> true
    | uu____526 -> false
  
let (uu___is_Fatal_DuplicateTypeAnnotationAndValDecl :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateTypeAnnotationAndValDecl  -> true
    | uu____537 -> false
  
let (uu___is_Fatal_EffectCannotBeReified : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectCannotBeReified  -> true
    | uu____548 -> false
  
let (uu___is_Fatal_EffectConstructorNotFullyApplied :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectConstructorNotFullyApplied  -> true
    | uu____559 -> false
  
let (uu___is_Fatal_EffectfulAndPureComputationMismatch :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectfulAndPureComputationMismatch  -> true
    | uu____570 -> false
  
let (uu___is_Fatal_EffectNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_EffectNotFound  -> true | uu____581 -> false
  
let (uu___is_Fatal_EffectsCannotBeComposed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectsCannotBeComposed  -> true
    | uu____592 -> false
  
let (uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_ErrorInSolveDeferredConstraints  -> true
    | uu____603 -> false
  
let (uu___is_Fatal_ErrorsReported : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_ErrorsReported  -> true | uu____614 -> false
  
let (uu___is_Fatal_EscapedBoundVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EscapedBoundVar  -> true
    | uu____625 -> false
  
let (uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedArrowAnnotatedType  -> true
    | uu____636 -> false
  
let (uu___is_Fatal_ExpectedGhostExpression : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedGhostExpression  -> true
    | uu____647 -> false
  
let (uu___is_Fatal_ExpectedPureExpression : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedPureExpression  -> true
    | uu____658 -> false
  
let (uu___is_Fatal_ExpectNormalizedEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectNormalizedEffect  -> true
    | uu____669 -> false
  
let (uu___is_Fatal_ExpectTermGotFunction : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectTermGotFunction  -> true
    | uu____680 -> false
  
let (uu___is_Fatal_ExpectTrivialPreCondition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectTrivialPreCondition  -> true
    | uu____691 -> false
  
let (uu___is_Fatal_FailToCompileNativeTactic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToCompileNativeTactic  -> true
    | uu____702 -> false
  
let (uu___is_Fatal_FailToExtractNativeTactic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToExtractNativeTactic  -> true
    | uu____713 -> false
  
let (uu___is_Fatal_FailToProcessPragma : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToProcessPragma  -> true
    | uu____724 -> false
  
let (uu___is_Fatal_FailToResolveImplicitArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToResolveImplicitArgument  -> true
    | uu____735 -> false
  
let (uu___is_Fatal_FailToSolveUniverseInEquality : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToSolveUniverseInEquality  -> true
    | uu____746 -> false
  
let (uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_FieldsNotBelongToSameRecordType  -> true
    | uu____757 -> false
  
let (uu___is_Fatal_ForbiddenReferenceToCurrentModule :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ForbiddenReferenceToCurrentModule  -> true
    | uu____768 -> false
  
let (uu___is_Fatal_FreeVariables : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_FreeVariables  -> true | uu____779 -> false
  
let (uu___is_Fatal_FunctionTypeExpected : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FunctionTypeExpected  -> true
    | uu____790 -> false
  
let (uu___is_Fatal_IdentifierNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IdentifierNotFound  -> true
    | uu____801 -> false
  
let (uu___is_Fatal_IllAppliedConstant : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IllAppliedConstant  -> true
    | uu____812 -> false
  
let (uu___is_Fatal_IllegalCharInByteArray : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IllegalCharInByteArray  -> true
    | uu____823 -> false
  
let (uu___is_Fatal_IllegalCharInOperatorName : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IllegalCharInOperatorName  -> true
    | uu____834 -> false
  
let (uu___is_Fatal_IllTyped : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_IllTyped  -> true | uu____845 -> false
  
let (uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleAbbrevLidBundle  -> true
    | uu____856 -> false
  
let (uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleAbbrevRenameBundle  -> true
    | uu____867 -> false
  
let (uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleInductiveWithAbbrev  -> true
    | uu____878 -> false
  
let (uu___is_Fatal_ImpossiblePrePostAbs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossiblePrePostAbs  -> true
    | uu____889 -> false
  
let (uu___is_Fatal_ImpossiblePrePostArrow : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossiblePrePostArrow  -> true
    | uu____900 -> false
  
let (uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleToGenerateDMEffect  -> true
    | uu____911 -> false
  
let (uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevBundle  -> true
    | uu____922 -> false
  
let (uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevSigeltBundle  -> true
    | uu____933 -> false
  
let (uu___is_Fatal_IncludeModuleNotPrepared : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncludeModuleNotPrepared  -> true
    | uu____944 -> false
  
let (uu___is_Fatal_IncoherentInlineUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncoherentInlineUniverse  -> true
    | uu____955 -> false
  
let (uu___is_Fatal_IncompatibleKinds : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleKinds  -> true
    | uu____966 -> false
  
let (uu___is_Fatal_IncompatibleNumberOfTypes : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleNumberOfTypes  -> true
    | uu____977 -> false
  
let (uu___is_Fatal_IncompatibleSetOfUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleSetOfUniverse  -> true
    | uu____988 -> false
  
let (uu___is_Fatal_IncompatibleUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleUniverse  -> true
    | uu____999 -> false
  
let (uu___is_Fatal_InconsistentImplicitArgumentAnnotation :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentImplicitArgumentAnnotation  -> true
    | uu____1010 -> false
  
let (uu___is_Fatal_InconsistentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentImplicitQualifier  -> true
    | uu____1021 -> false
  
let (uu___is_Fatal_InconsistentQualifierAnnotation : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentQualifierAnnotation  -> true
    | uu____1032 -> false
  
let (uu___is_Fatal_InferredTypeCauseVarEscape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InferredTypeCauseVarEscape  -> true
    | uu____1043 -> false
  
let (uu___is_Fatal_InlineRenamedAsUnfold : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InlineRenamedAsUnfold  -> true
    | uu____1054 -> false
  
let (uu___is_Fatal_InsufficientPatternArguments : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InsufficientPatternArguments  -> true
    | uu____1065 -> false
  
let (uu___is_Fatal_InterfaceAlreadyProcessed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceAlreadyProcessed  -> true
    | uu____1076 -> false
  
let (uu___is_Fatal_InterfaceNotImplementedByModule : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceNotImplementedByModule  -> true
    | uu____1087 -> false
  
let (uu___is_Fatal_InterfaceWithTypeImplementation : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceWithTypeImplementation  -> true
    | uu____1098 -> false
  
let (uu___is_Fatal_InvalidFloatingPointNumber : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidFloatingPointNumber  -> true
    | uu____1109 -> false
  
let (uu___is_Fatal_InvalidFSDocKeyword : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidFSDocKeyword  -> true
    | uu____1120 -> false
  
let (uu___is_Fatal_InvalidIdentifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidIdentifier  -> true
    | uu____1131 -> false
  
let (uu___is_Fatal_InvalidLemmaArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidLemmaArgument  -> true
    | uu____1142 -> false
  
let (uu___is_Fatal_InvalidNumericLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidNumericLiteral  -> true
    | uu____1153 -> false
  
let (uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidRedefinitionOfLexT  -> true
    | uu____1164 -> false
  
let (uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidUnicodeInStringLiteral  -> true
    | uu____1175 -> false
  
let (uu___is_Fatal_InvalidUTF8Encoding : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidUTF8Encoding  -> true
    | uu____1186 -> false
  
let (uu___is_Fatal_InvalidWarnErrorSetting : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidWarnErrorSetting  -> true
    | uu____1197 -> false
  
let (uu___is_Fatal_LetBoundMonadicMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetBoundMonadicMismatch  -> true
    | uu____1208 -> false
  
let (uu___is_Fatal_LetMutableForVariablesOnly : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetMutableForVariablesOnly  -> true
    | uu____1219 -> false
  
let (uu___is_Fatal_LetOpenModuleOnly : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetOpenModuleOnly  -> true
    | uu____1230 -> false
  
let (uu___is_Fatal_LetRecArgumentMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetRecArgumentMismatch  -> true
    | uu____1241 -> false
  
let (uu___is_Fatal_MalformedActionDeclaration : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MalformedActionDeclaration  -> true
    | uu____1252 -> false
  
let (uu___is_Fatal_MismatchedPatternType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MismatchedPatternType  -> true
    | uu____1263 -> false
  
let (uu___is_Fatal_MismatchUniversePolymorphic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MismatchUniversePolymorphic  -> true
    | uu____1274 -> false
  
let (uu___is_Fatal_MissingDataConstructor : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingDataConstructor  -> true
    | uu____1285 -> false
  
let (uu___is_Fatal_MissingExposeInterfacesOption : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingExposeInterfacesOption  -> true
    | uu____1296 -> false
  
let (uu___is_Fatal_MissingFieldInRecord : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingFieldInRecord  -> true
    | uu____1307 -> false
  
let (uu___is_Fatal_MissingImplementation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingImplementation  -> true
    | uu____1318 -> false
  
let (uu___is_Fatal_MissingImplicitArguments : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingImplicitArguments  -> true
    | uu____1329 -> false
  
let (uu___is_Fatal_MissingInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingInterface  -> true
    | uu____1340 -> false
  
let (uu___is_Fatal_MissingNameInBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingNameInBinder  -> true
    | uu____1351 -> false
  
let (uu___is_Fatal_MissingPrimsModule : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingPrimsModule  -> true
    | uu____1362 -> false
  
let (uu___is_Fatal_MissingQuantifierBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingQuantifierBinder  -> true
    | uu____1373 -> false
  
let (uu___is_Fatal_ModuleExpected : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleExpected  -> true
    | uu____1384 -> false
  
let (uu___is_Fatal_ModuleFileNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleFileNotFound  -> true
    | uu____1395 -> false
  
let (uu___is_Fatal_ModuleFirstStatement : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleFirstStatement  -> true
    | uu____1406 -> false
  
let (uu___is_Fatal_ModuleNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleNotFound  -> true
    | uu____1417 -> false
  
let (uu___is_Fatal_ModuleOrFileNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleOrFileNotFound  -> true
    | uu____1428 -> false
  
let (uu___is_Fatal_MonadAlreadyDefined : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MonadAlreadyDefined  -> true
    | uu____1439 -> false
  
let (uu___is_Fatal_MoreThanOneDeclaration : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MoreThanOneDeclaration  -> true
    | uu____1450 -> false
  
let (uu___is_Fatal_MultipleLetBinding : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MultipleLetBinding  -> true
    | uu____1461 -> false
  
let (uu___is_Fatal_NameNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_NameNotFound  -> true | uu____1472 -> false
  
let (uu___is_Fatal_NameSpaceNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NameSpaceNotFound  -> true
    | uu____1483 -> false
  
let (uu___is_Fatal_NegativeUniverseConstFatal_NotSupported :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NegativeUniverseConstFatal_NotSupported  -> true
    | uu____1494 -> false
  
let (uu___is_Fatal_NoFileProvided : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NoFileProvided  -> true
    | uu____1505 -> false
  
let (uu___is_Fatal_NonInductiveInMutuallyDefinedType :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonInductiveInMutuallyDefinedType  -> true
    | uu____1516 -> false
  
let (uu___is_Fatal_NonLinearPatternNotPermitted : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonLinearPatternNotPermitted  -> true
    | uu____1527 -> false
  
let (uu___is_Fatal_NonLinearPatternVars : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonLinearPatternVars  -> true
    | uu____1538 -> false
  
let (uu___is_Fatal_NonSingletonTopLevel : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonSingletonTopLevel  -> true
    | uu____1549 -> false
  
let (uu___is_Fatal_NonSingletonTopLevelModule : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonSingletonTopLevelModule  -> true
    | uu____1560 -> false
  
let (uu___is_Fatal_NonTopRecFunctionNotFullyEncoded :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonTopRecFunctionNotFullyEncoded  -> true
    | uu____1571 -> false
  
let (uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonTrivialPreConditionInPrims  -> true
    | uu____1582 -> false
  
let (uu___is_Fatal_NonVariableInductiveTypeParameter :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonVariableInductiveTypeParameter  -> true
    | uu____1593 -> false
  
let (uu___is_Fatal_NotApplicationOrFv : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotApplicationOrFv  -> true
    | uu____1604 -> false
  
let (uu___is_Fatal_NotEnoughArgsToEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotEnoughArgsToEffect  -> true
    | uu____1615 -> false
  
let (uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotEnoughArgumentsForEffect  -> true
    | uu____1626 -> false
  
let (uu___is_Fatal_NotFunctionType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotFunctionType  -> true
    | uu____1637 -> false
  
let (uu___is_Fatal_NotSupported : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_NotSupported  -> true | uu____1648 -> false
  
let (uu___is_Fatal_NotTopLevelModule : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotTopLevelModule  -> true
    | uu____1659 -> false
  
let (uu___is_Fatal_NotValidFStarFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotValidFStarFile  -> true
    | uu____1670 -> false
  
let (uu___is_Fatal_NotValidIncludeDirectory : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotValidIncludeDirectory  -> true
    | uu____1681 -> false
  
let (uu___is_Fatal_OneModulePerFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_OneModulePerFile  -> true
    | uu____1692 -> false
  
let (uu___is_Fatal_OpenGoalsInSynthesis : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_OpenGoalsInSynthesis  -> true
    | uu____1703 -> false
  
let (uu___is_Fatal_OptionsNotCompatible : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_OptionsNotCompatible  -> true
    | uu____1714 -> false
  
let (uu___is_Fatal_OutOfOrder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_OutOfOrder  -> true | uu____1725 -> false
  
let (uu___is_Fatal_ParseErrors : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_ParseErrors  -> true | uu____1736 -> false
  
let (uu___is_Fatal_ParseItError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_ParseItError  -> true | uu____1747 -> false
  
let (uu___is_Fatal_PolyTypeExpected : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_PolyTypeExpected  -> true
    | uu____1758 -> false
  
let (uu___is_Fatal_PossibleInfiniteTyp : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_PossibleInfiniteTyp  -> true
    | uu____1769 -> false
  
let (uu___is_Fatal_PreModuleMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_PreModuleMismatch  -> true
    | uu____1780 -> false
  
let (uu___is_Fatal_QulifierListNotPermitted : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_QulifierListNotPermitted  -> true
    | uu____1791 -> false
  
let (uu___is_Fatal_RecursiveFunctionLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_RecursiveFunctionLiteral  -> true
    | uu____1802 -> false
  
let (uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ReflectOnlySupportedOnEffects  -> true
    | uu____1813 -> false
  
let (uu___is_Fatal_ReservedPrefix : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ReservedPrefix  -> true
    | uu____1824 -> false
  
let (uu___is_Fatal_SMTOutputParseError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SMTOutputParseError  -> true
    | uu____1835 -> false
  
let (uu___is_Fatal_SMTSolverError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SMTSolverError  -> true
    | uu____1846 -> false
  
let (uu___is_Fatal_SyntaxError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_SyntaxError  -> true | uu____1857 -> false
  
let (uu___is_Fatal_SynthByTacticError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SynthByTacticError  -> true
    | uu____1868 -> false
  
let (uu___is_Fatal_TacticGotStuck : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TacticGotStuck  -> true
    | uu____1879 -> false
  
let (uu___is_Fatal_TcOneFragmentFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TcOneFragmentFailed  -> true
    | uu____1890 -> false
  
let (uu___is_Fatal_TermOutsideOfDefLanguage : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TermOutsideOfDefLanguage  -> true
    | uu____1901 -> false
  
let (uu___is_Fatal_ToManyArgumentToFunction : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ToManyArgumentToFunction  -> true
    | uu____1912 -> false
  
let (uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyOrTooFewFileMatch  -> true
    | uu____1923 -> false
  
let (uu___is_Fatal_TooManyPatternArguments : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyPatternArguments  -> true
    | uu____1934 -> false
  
let (uu___is_Fatal_TooManyUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyUniverse  -> true
    | uu____1945 -> false
  
let (uu___is_Fatal_TypeMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_TypeMismatch  -> true | uu____1956 -> false
  
let (uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TypeWithinPatternsAllowedOnVariablesOnly  -> true
    | uu____1967 -> false
  
let (uu___is_Fatal_UnableToReadFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnableToReadFile  -> true
    | uu____1978 -> false
  
let (uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnepxectedOrUnboundOperator  -> true
    | uu____1989 -> false
  
let (uu___is_Fatal_UnexpectedBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedBinder  -> true
    | uu____2000 -> false
  
let (uu___is_Fatal_UnexpectedBindShape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedBindShape  -> true
    | uu____2011 -> false
  
let (uu___is_Fatal_UnexpectedChar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedChar  -> true
    | uu____2022 -> false
  
let (uu___is_Fatal_UnexpectedComputationTypeForLetRec :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedComputationTypeForLetRec  -> true
    | uu____2033 -> false
  
let (uu___is_Fatal_UnexpectedConstructorType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedConstructorType  -> true
    | uu____2044 -> false
  
let (uu___is_Fatal_UnexpectedDataConstructor : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedDataConstructor  -> true
    | uu____2055 -> false
  
let (uu___is_Fatal_UnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedEffect  -> true
    | uu____2066 -> false
  
let (uu___is_Fatal_UnexpectedEmptyRecord : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedEmptyRecord  -> true
    | uu____2077 -> false
  
let (uu___is_Fatal_UnexpectedExpressionType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedExpressionType  -> true
    | uu____2088 -> false
  
let (uu___is_Fatal_UnexpectedFunctionParameterType : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedFunctionParameterType  -> true
    | uu____2099 -> false
  
let (uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGeneralizedUniverse  -> true
    | uu____2110 -> false
  
let (uu___is_Fatal_UnexpectedGTotForLetRec : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGTotForLetRec  -> true
    | uu____2121 -> false
  
let (uu___is_Fatal_UnexpectedGuard : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGuard  -> true
    | uu____2132 -> false
  
let (uu___is_Fatal_UnexpectedIdentifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedIdentifier  -> true
    | uu____2143 -> false
  
let (uu___is_Fatal_UnexpectedImplicitArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedImplicitArgument  -> true
    | uu____2154 -> false
  
let (uu___is_Fatal_UnexpectedImplictArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedImplictArgument  -> true
    | uu____2165 -> false
  
let (uu___is_Fatal_UnexpectedInductivetype : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedInductivetype  -> true
    | uu____2176 -> false
  
let (uu___is_Fatal_UnexpectedLetBinding : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedLetBinding  -> true
    | uu____2187 -> false
  
let (uu___is_Fatal_UnexpectedModuleDeclaration : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedModuleDeclaration  -> true
    | uu____2198 -> false
  
let (uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedNumberOfUniverse  -> true
    | uu____2209 -> false
  
let (uu___is_Fatal_UnexpectedNumericLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedNumericLiteral  -> true
    | uu____2220 -> false
  
let (uu___is_Fatal_UnexpectedOperatorSymbol : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedOperatorSymbol  -> true
    | uu____2231 -> false
  
let (uu___is_Fatal_UnexpectedPattern : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedPattern  -> true
    | uu____2242 -> false
  
let (uu___is_Fatal_UnexpectedPosition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedPosition  -> true
    | uu____2253 -> false
  
let (uu___is_Fatal_UnExpectedPreCondition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnExpectedPreCondition  -> true
    | uu____2264 -> false
  
let (uu___is_Fatal_UnexpectedReturnShape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedReturnShape  -> true
    | uu____2275 -> false
  
let (uu___is_Fatal_UnexpectedSignatureForMonad : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedSignatureForMonad  -> true
    | uu____2286 -> false
  
let (uu___is_Fatal_UnexpectedTerm : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTerm  -> true
    | uu____2297 -> false
  
let (uu___is_Fatal_UnexpectedTermInUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermInUniverse  -> true
    | uu____2308 -> false
  
let (uu___is_Fatal_UnexpectedTermType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermType  -> true
    | uu____2319 -> false
  
let (uu___is_Fatal_UnexpectedTermVQuote : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermVQuote  -> true
    | uu____2330 -> false
  
let (uu___is_Fatal_UnexpectedUniversePolymorphicReturn :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedUniversePolymorphicReturn  -> true
    | uu____2341 -> false
  
let (uu___is_Fatal_UnexpectedUniverseVariable : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedUniverseVariable  -> true
    | uu____2352 -> false
  
let (uu___is_Fatal_UnfoldableDeprecated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnfoldableDeprecated  -> true
    | uu____2363 -> false
  
let (uu___is_Fatal_UnificationNotWellFormed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnificationNotWellFormed  -> true
    | uu____2374 -> false
  
let (uu___is_Fatal_Uninstantiated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_Uninstantiated  -> true
    | uu____2385 -> false
  
let (uu___is_Error_UninstantiatedUnificationVarInTactic :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UninstantiatedUnificationVarInTactic  -> true
    | uu____2396 -> false
  
let (uu___is_Fatal_UninstantiatedVarInTactic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UninstantiatedVarInTactic  -> true
    | uu____2407 -> false
  
let (uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UniverseMightContainSumOfTwoUnivVars  -> true
    | uu____2418 -> false
  
let (uu___is_Fatal_UniversePolymorphicInnerLetBound :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UniversePolymorphicInnerLetBound  -> true
    | uu____2429 -> false
  
let (uu___is_Fatal_UnknownAttribute : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnknownAttribute  -> true
    | uu____2440 -> false
  
let (uu___is_Fatal_UnknownToolForDep : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnknownToolForDep  -> true
    | uu____2451 -> false
  
let (uu___is_Fatal_UnrecognizedExtension : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnrecognizedExtension  -> true
    | uu____2462 -> false
  
let (uu___is_Fatal_UnresolvedPatternVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnresolvedPatternVar  -> true
    | uu____2473 -> false
  
let (uu___is_Fatal_UnsupportedConstant : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedConstant  -> true
    | uu____2484 -> false
  
let (uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedDisjuctivePatterns  -> true
    | uu____2495 -> false
  
let (uu___is_Fatal_UnsupportedQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedQualifier  -> true
    | uu____2506 -> false
  
let (uu___is_Fatal_UserTacticFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UserTacticFailure  -> true
    | uu____2517 -> false
  
let (uu___is_Fatal_ValueRestriction : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ValueRestriction  -> true
    | uu____2528 -> false
  
let (uu___is_Fatal_VariableNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_VariableNotFound  -> true
    | uu____2539 -> false
  
let (uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WrongBodyTypeForReturnWP  -> true
    | uu____2550 -> false
  
let (uu___is_Fatal_WrongDataAppHeadFormat : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WrongDataAppHeadFormat  -> true
    | uu____2561 -> false
  
let (uu___is_Fatal_WrongDefinitionOrder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WrongDefinitionOrder  -> true
    | uu____2572 -> false
  
let (uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_WrongResultTypeAfterConstrutor  -> true
    | uu____2583 -> false
  
let (uu___is_Fatal_WrongTerm : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_WrongTerm  -> true | uu____2594 -> false
  
let (uu___is_Fatal_WhenClauseNotSupported : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WhenClauseNotSupported  -> true
    | uu____2605 -> false
  
let (uu___is_Unused01 : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unused01  -> true | uu____2616 -> false
  
let (uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Warning_AddImplicitAssumeNewQualifier  -> true
    | uu____2627 -> false
  
let (uu___is_Warning_AdmitWithoutDefinition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_AdmitWithoutDefinition  -> true
    | uu____2638 -> false
  
let (uu___is_Warning_CachedFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_CachedFile  -> true | uu____2649 -> false
  
let (uu___is_Warning_DefinitionNotTranslated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DefinitionNotTranslated  -> true
    | uu____2660 -> false
  
let (uu___is_Warning_DependencyFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DependencyFound  -> true
    | uu____2671 -> false
  
let (uu___is_Warning_DeprecatedEqualityOnBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedEqualityOnBinder  -> true
    | uu____2682 -> false
  
let (uu___is_Warning_DeprecatedOpaqueQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedOpaqueQualifier  -> true
    | uu____2693 -> false
  
let (uu___is_Warning_DocOverwrite : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DocOverwrite  -> true
    | uu____2704 -> false
  
let (uu___is_Warning_FileNotWritten : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_FileNotWritten  -> true
    | uu____2715 -> false
  
let (uu___is_Warning_Filtered : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_Filtered  -> true | uu____2726 -> false
  
let (uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Warning_FunctionLiteralPrecisionLoss  -> true
    | uu____2737 -> false
  
let (uu___is_Warning_FunctionNotExtacted : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_FunctionNotExtacted  -> true
    | uu____2748 -> false
  
let (uu___is_Warning_HintFailedToReplayProof : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_HintFailedToReplayProof  -> true
    | uu____2759 -> false
  
let (uu___is_Warning_HitReplayFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_HitReplayFailed  -> true
    | uu____2770 -> false
  
let (uu___is_Warning_IDEIgnoreCodeGen : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IDEIgnoreCodeGen  -> true
    | uu____2781 -> false
  
let (uu___is_Warning_IllFormedGoal : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IllFormedGoal  -> true
    | uu____2792 -> false
  
let (uu___is_Warning_InaccessibleArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_InaccessibleArgument  -> true
    | uu____2803 -> false
  
let (uu___is_Warning_IncoherentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IncoherentImplicitQualifier  -> true
    | uu____2814 -> false
  
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReflect :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReflect  -> true
    | uu____2825 -> false
  
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReify :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReify  -> true
    | uu____2836 -> false
  
let (uu___is_Warning_MalformedWarnErrorList : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MalformedWarnErrorList  -> true
    | uu____2847 -> false
  
let (uu___is_Warning_MetaAlienNotATmUnknown : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MetaAlienNotATmUnknown  -> true
    | uu____2858 -> false
  
let (uu___is_Warning_MultipleAscriptions : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MultipleAscriptions  -> true
    | uu____2869 -> false
  
let (uu___is_Warning_NondependentUserDefinedDataType :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NondependentUserDefinedDataType  -> true
    | uu____2880 -> false
  
let (uu___is_Warning_NonListLiteralSMTPattern : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NonListLiteralSMTPattern  -> true
    | uu____2891 -> false
  
let (uu___is_Warning_NormalizationFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NormalizationFailure  -> true
    | uu____2902 -> false
  
let (uu___is_Warning_NotDependentArrow : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NotDependentArrow  -> true
    | uu____2913 -> false
  
let (uu___is_Warning_NotEmbedded : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_NotEmbedded  -> true | uu____2924 -> false
  
let (uu___is_Warning_PatternMissingBoundVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_PatternMissingBoundVar  -> true
    | uu____2935 -> false
  
let (uu___is_Warning_RecursiveDependency : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_RecursiveDependency  -> true
    | uu____2946 -> false
  
let (uu___is_Warning_RedundantExplicitCurrying : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_RedundantExplicitCurrying  -> true
    | uu____2957 -> false
  
let (uu___is_Warning_SMTPatTDeprecated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_SMTPatTDeprecated  -> true
    | uu____2968 -> false
  
let (uu___is_Warning_SMTPatternMissingBoundVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_SMTPatternMissingBoundVar  -> true
    | uu____2979 -> false
  
let (uu___is_Warning_TopLevelEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_TopLevelEffect  -> true
    | uu____2990 -> false
  
let (uu___is_Warning_UnboundModuleReference : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnboundModuleReference  -> true
    | uu____3001 -> false
  
let (uu___is_Warning_UnexpectedFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedFile  -> true
    | uu____3012 -> false
  
let (uu___is_Warning_UnexpectedFsTypApp : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedFsTypApp  -> true
    | uu____3023 -> false
  
let (uu___is_Warning_UnexpectedZ3Output : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedZ3Output  -> true
    | uu____3034 -> false
  
let (uu___is_Warning_UnprotectedTerm : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnprotectedTerm  -> true
    | uu____3045 -> false
  
let (uu___is_Warning_UnrecognizedAttribute : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnrecognizedAttribute  -> true
    | uu____3056 -> false
  
let (uu___is_Warning_UpperBoundCandidateAlreadyVisited :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UpperBoundCandidateAlreadyVisited  -> true
    | uu____3067 -> false
  
let (uu___is_Warning_UseDefaultEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UseDefaultEffect  -> true
    | uu____3078 -> false
  
let (uu___is_Warning_WrongErrorLocation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_WrongErrorLocation  -> true
    | uu____3089 -> false
  
let (uu___is_Warning_Z3InvocationWarning : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_Z3InvocationWarning  -> true
    | uu____3100 -> false
  
let (uu___is_Warning_CallNotImplementedAsWarning : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_CallNotImplementedAsWarning  -> true
    | uu____3111 -> false
  
let (uu___is_Warning_MissingInterfaceOrImplementation :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MissingInterfaceOrImplementation  -> true
    | uu____3122 -> false
  
let (uu___is_Warning_ConstructorBuildsUnexpectedType :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ConstructorBuildsUnexpectedType  -> true
    | uu____3133 -> false
  
let (uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ModuleOrFileNotFoundWarning  -> true
    | uu____3144 -> false
  
let (uu___is_Error_NoLetMutable : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_NoLetMutable  -> true | uu____3155 -> false
  
let (uu___is_Error_BadImplicit : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_BadImplicit  -> true | uu____3166 -> false
  
let (uu___is_Warning_DeprecatedDefinition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedDefinition  -> true
    | uu____3177 -> false
  
let (uu___is_Fatal_SMTEncodingArityMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SMTEncodingArityMismatch  -> true
    | uu____3188 -> false
  
let (uu___is_Warning_Defensive : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_Defensive  -> true | uu____3199 -> false
  
let (uu___is_Warning_CantInspect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_CantInspect  -> true | uu____3210 -> false
  
let (uu___is_Warning_NilGivenExplicitArgs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NilGivenExplicitArgs  -> true
    | uu____3221 -> false
  
let (uu___is_Warning_ConsAppliedExplicitArgs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ConsAppliedExplicitArgs  -> true
    | uu____3232 -> false
  
let (uu___is_Warning_UnembedBinderKnot : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnembedBinderKnot  -> true
    | uu____3243 -> false
  
let (uu___is_Fatal_TacticProofRelevantGoal : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TacticProofRelevantGoal  -> true
    | uu____3254 -> false
  
let (uu___is_Warning_TacAdmit : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_TacAdmit  -> true | uu____3265 -> false
  
let (uu___is_Fatal_IncoherentPatterns : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncoherentPatterns  -> true
    | uu____3276 -> false
  
let (uu___is_Error_NoSMTButNeeded : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_NoSMTButNeeded  -> true
    | uu____3287 -> false
  
let (uu___is_Fatal_UnexpectedAntiquotation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedAntiquotation  -> true
    | uu____3298 -> false
  
let (uu___is_Fatal_SplicedUndef : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_SplicedUndef  -> true | uu____3309 -> false
  
let (uu___is_Fatal_SpliceUnembedFail : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SpliceUnembedFail  -> true
    | uu____3320 -> false
  
let (uu___is_Warning_ExtractionUnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ExtractionUnexpectedEffect  -> true
    | uu____3331 -> false
  
let (uu___is_Error_DidNotFail : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_DidNotFail  -> true | uu____3342 -> false
  
let (uu___is_Warning_UnappliedFail : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnappliedFail  -> true
    | uu____3353 -> false
  
let (uu___is_Warning_QuantifierWithoutPattern : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_QuantifierWithoutPattern  -> true
    | uu____3364 -> false
  
let (uu___is_Error_EmptyFailErrs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_EmptyFailErrs  -> true | uu____3375 -> false
  
let (uu___is_Warning_logicqualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_logicqualifier  -> true
    | uu____3386 -> false
  
let (uu___is_Fatal_CyclicDependence : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_CyclicDependence  -> true
    | uu____3397 -> false
  
let (uu___is_Error_InductiveAnnotNotAType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_InductiveAnnotNotAType  -> true
    | uu____3408 -> false
  
let (uu___is_Fatal_FriendInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FriendInterface  -> true
    | uu____3419 -> false
  
let (uu___is_Error_CannotRedefineConst : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_CannotRedefineConst  -> true
    | uu____3430 -> false
  
let (uu___is_Error_BadClassDecl : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_BadClassDecl  -> true | uu____3441 -> false
  
let (uu___is_Error_BadInductiveParam : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_BadInductiveParam  -> true
    | uu____3452 -> false
  
let (uu___is_Error_FieldShadow : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_FieldShadow  -> true | uu____3463 -> false
  
let (uu___is_Error_UnexpectedDM4FType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedDM4FType  -> true
    | uu____3474 -> false
  
let (uu___is_Fatal_EffectAbbreviationResultTypeMismatch :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectAbbreviationResultTypeMismatch  -> true
    | uu____3485 -> false
  
let (uu___is_Error_AlreadyCachedAssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_AlreadyCachedAssertionFailure  -> true
    | uu____3496 -> false
  
let (uu___is_Error_MustEraseMissing : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_MustEraseMissing  -> true
    | uu____3507 -> false
  
let (uu___is_Warning_EffectfulArgumentToErasedFunction :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_EffectfulArgumentToErasedFunction  -> true
    | uu____3518 -> false
  
let (uu___is_Fatal_EmptySurfaceLet : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EmptySurfaceLet  -> true
    | uu____3529 -> false
  
type flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CFatal  -> true | uu____3540 -> false
  
let (uu___is_CAlwaysError : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CAlwaysError  -> true | uu____3551 -> false
  
let (uu___is_CError : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CError  -> true | uu____3562 -> false
  
let (uu___is_CWarning : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CWarning  -> true | uu____3573 -> false
  
let (uu___is_CSilent : flag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CSilent  -> true | uu____3584 -> false
  
let (default_flags : (raw_error * flag) Prims.list) =
  [(Error_DependencyAnalysisFailed, CAlwaysError);
  (Error_IDETooManyPops, CAlwaysError);
  (Error_IDEUnrecognized, CAlwaysError);
  (Error_InductiveTypeNotSatisfyPositivityCondition, CAlwaysError);
  (Error_InvalidUniverseVar, CAlwaysError);
  (Error_MissingFileName, CAlwaysError);
  (Error_ModuleFileNameMismatch, CAlwaysError);
  (Error_OpPlusInUniverse, CAlwaysError);
  (Error_OutOfRange, CAlwaysError);
  (Error_ProofObligationFailed, CError);
  (Error_TooManyFiles, CAlwaysError);
  (Error_TypeCheckerFailToProve, CAlwaysError);
  (Error_TypeError, CAlwaysError);
  (Error_UncontrainedUnificationVar, CAlwaysError);
  (Error_UnexpectedGTotComputation, CAlwaysError);
  (Error_UnexpectedInstance, CAlwaysError);
  (Error_UnknownFatal_AssertionFailure, CError);
  (Error_Z3InvocationError, CAlwaysError);
  (Error_IDEAssertionFailure, CAlwaysError);
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
  (Fatal_FailToExtractNativeTactic, CFatal);
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
  (Fatal_UnexpectedTermVQuote, CFatal);
  (Fatal_UnexpectedUniversePolymorphicReturn, CFatal);
  (Fatal_UnexpectedUniverseVariable, CFatal);
  (Fatal_UnfoldableDeprecated, CFatal);
  (Fatal_UnificationNotWellFormed, CFatal);
  (Fatal_Uninstantiated, CFatal);
  (Error_UninstantiatedUnificationVarInTactic, CError);
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
  (Unused01, CFatal);
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
  (Warning_UnexpectedZ3Output, CError);
  (Warning_UnprotectedTerm, CWarning);
  (Warning_UnrecognizedAttribute, CWarning);
  (Warning_UpperBoundCandidateAlreadyVisited, CWarning);
  (Warning_UseDefaultEffect, CWarning);
  (Warning_WrongErrorLocation, CWarning);
  (Warning_Z3InvocationWarning, CWarning);
  (Warning_MissingInterfaceOrImplementation, CWarning);
  (Warning_ConstructorBuildsUnexpectedType, CWarning);
  (Warning_ModuleOrFileNotFoundWarning, CWarning);
  (Error_NoLetMutable, CAlwaysError);
  (Error_BadImplicit, CAlwaysError);
  (Warning_DeprecatedDefinition, CWarning);
  (Fatal_SMTEncodingArityMismatch, CFatal);
  (Warning_Defensive, CWarning);
  (Warning_CantInspect, CWarning);
  (Warning_NilGivenExplicitArgs, CWarning);
  (Warning_ConsAppliedExplicitArgs, CWarning);
  (Warning_UnembedBinderKnot, CWarning);
  (Fatal_TacticProofRelevantGoal, CFatal);
  (Warning_TacAdmit, CWarning);
  (Fatal_IncoherentPatterns, CFatal);
  (Error_NoSMTButNeeded, CAlwaysError);
  (Fatal_UnexpectedAntiquotation, CFatal);
  (Fatal_SplicedUndef, CFatal);
  (Fatal_SpliceUnembedFail, CFatal);
  (Warning_ExtractionUnexpectedEffect, CWarning);
  (Error_DidNotFail, CAlwaysError);
  (Warning_UnappliedFail, CWarning);
  (Warning_QuantifierWithoutPattern, CSilent);
  (Error_EmptyFailErrs, CAlwaysError);
  (Warning_logicqualifier, CWarning);
  (Fatal_CyclicDependence, CFatal);
  (Error_InductiveAnnotNotAType, CError);
  (Fatal_FriendInterface, CFatal);
  (Error_CannotRedefineConst, CError);
  (Error_BadClassDecl, CError);
  (Error_BadInductiveParam, CFatal);
  (Error_FieldShadow, CFatal);
  (Error_UnexpectedDM4FType, CFatal);
  (Fatal_EffectAbbreviationResultTypeMismatch, CFatal);
  (Error_AlreadyCachedAssertionFailure, CFatal);
  (Error_MustEraseMissing, CWarning);
  (Warning_EffectfulArgumentToErasedFunction, CWarning);
  (Fatal_EmptySurfaceLet, CFatal)] 
exception Err of (raw_error * Prims.string) 
let (uu___is_Err : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Err uu____4898 -> true | uu____4905 -> false
  
let (__proj__Err__item__uu___ : Prims.exn -> (raw_error * Prims.string)) =
  fun projectee  -> match projectee with | Err uu____4924 -> uu____4924 
exception Error of (raw_error * Prims.string * FStar_Range.range) 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error uu____4949 -> true | uu____4958 -> false
  
let (__proj__Error__item__uu___ :
  Prims.exn -> (raw_error * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Error uu____4981 -> uu____4981 
exception Warning of (raw_error * Prims.string * FStar_Range.range) 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning uu____5008 -> true | uu____5017 -> false
  
let (__proj__Warning__item__uu___ :
  Prims.exn -> (raw_error * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Warning uu____5040 -> uu____5040 
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stop  -> true | uu____5057 -> false
  
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____5068 -> false
  
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____5079 -> false
  
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | EInfo  -> true | uu____5090 -> false
  
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____5101 -> false
  
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | EError  -> true | uu____5112 -> false
  
type issue =
  {
  issue_message: Prims.string ;
  issue_level: issue_level ;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option ;
  issue_number: Prims.int FStar_Pervasives_Native.option }
let (__proj__Mkissue__item__issue_message : issue -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { issue_message; issue_level; issue_range; issue_number;_} ->
        issue_message
  
let (__proj__Mkissue__item__issue_level : issue -> issue_level) =
  fun projectee  ->
    match projectee with
    | { issue_message; issue_level; issue_range; issue_number;_} ->
        issue_level
  
let (__proj__Mkissue__item__issue_range :
  issue -> FStar_Range.range FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { issue_message; issue_level; issue_range; issue_number;_} ->
        issue_range
  
let (__proj__Mkissue__item__issue_number :
  issue -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { issue_message; issue_level; issue_range; issue_number;_} ->
        issue_number
  
type error_handler =
  {
  eh_add_one: issue -> unit ;
  eh_count_errors: unit -> Prims.int ;
  eh_report: unit -> issue Prims.list ;
  eh_clear: unit -> unit }
let (__proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> unit) =
  fun projectee  ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_add_one
  
let (__proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_count_errors
  
let (__proj__Mkerror_handler__item__eh_report :
  error_handler -> unit -> issue Prims.list) =
  fun projectee  ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_report
  
let (__proj__Mkerror_handler__item__eh_clear : error_handler -> unit -> unit)
  =
  fun projectee  ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_clear
  
let (format_issue : issue -> Prims.string) =
  fun issue  ->
    let level_header =
      match issue.issue_level with
      | EInfo  -> "Info"
      | EWarning  -> "Warning"
      | EError  -> "Error"
      | ENotImplemented  -> "Feature not yet implemented: "  in
    let uu____5407 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r when r = FStar_Range.dummyRange ->
          ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____5430 =
            let uu____5432 = FStar_Range.string_of_use_range r  in
            FStar_Util.format1 "%s: " uu____5432  in
          let uu____5435 =
            let uu____5437 =
              let uu____5439 = FStar_Range.use_range r  in
              let uu____5440 = FStar_Range.def_range r  in
              uu____5439 = uu____5440  in
            if uu____5437
            then ""
            else
              (let uu____5446 = FStar_Range.string_of_range r  in
               FStar_Util.format1 " (see also %s)" uu____5446)
             in
          (uu____5430, uu____5435)
       in
    match uu____5407 with
    | (range_str,see_also_str) ->
        let issue_number =
          match issue.issue_number with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some n1 ->
              let uu____5466 = FStar_Util.string_of_int n1  in
              FStar_Util.format1 " %s" uu____5466
           in
        FStar_Util.format5 "%s(%s%s) %s%s\n" range_str level_header
          issue_number issue.issue_message see_also_str
  
let (print_issue : issue -> unit) =
  fun issue  ->
    let printer =
      match issue.issue_level with
      | EInfo  -> FStar_Util.print_string
      | EWarning  -> FStar_Util.print_warning
      | EError  -> FStar_Util.print_error
      | ENotImplemented  -> FStar_Util.print_error  in
    let uu____5486 = format_issue issue  in printer uu____5486
  
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          (Prims.parse_int "0")
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____5510) -> ~- (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some uu____5516,FStar_Pervasives_Native.None
         ) -> (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
  
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print7  ->
    let errs = FStar_Util.mk_ref []  in
    let add_one e =
      match e.issue_level with
      | EError  ->
          let uu____5549 =
            let uu____5552 = FStar_ST.op_Bang errs  in e :: uu____5552  in
          FStar_ST.op_Colon_Equals errs uu____5549
      | uu____5645 -> print_issue e  in
    let count_errors uu____5651 =
      let uu____5652 = FStar_ST.op_Bang errs  in FStar_List.length uu____5652
       in
    let report uu____5707 =
      let sorted1 =
        let uu____5711 = FStar_ST.op_Bang errs  in
        FStar_List.sortWith compare_issues uu____5711  in
      if print7 then FStar_List.iter print_issue sorted1 else (); sorted1  in
    let clear1 uu____5768 = FStar_ST.op_Colon_Equals errs []  in
    {
      eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear1
    }
  
let (default_handler : error_handler) = mk_default_handler true 
let (current_handler : error_handler FStar_ST.ref) =
  FStar_Util.mk_ref default_handler 
let (mk_issue :
  issue_level ->
    FStar_Range.range FStar_Pervasives_Native.option ->
      Prims.string -> Prims.int FStar_Pervasives_Native.option -> issue)
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
  
let (get_err_count : unit -> Prims.int) =
  fun uu____5873  ->
    let uu____5874 =
      let uu____5880 = FStar_ST.op_Bang current_handler  in
      uu____5880.eh_count_errors  in
    uu____5874 ()
  
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h  ->
    fun issue  ->
      h.eh_add_one issue;
      if issue.issue_level <> EInfo
      then
        ((let uu____5914 =
            let uu____5916 = FStar_ST.op_Bang FStar_Options.abort_counter  in
            uu____5916 - (Prims.parse_int "1")  in
          FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____5914);
         (let uu____5961 =
            let uu____5963 = FStar_ST.op_Bang FStar_Options.abort_counter  in
            uu____5963 = (Prims.parse_int "0")  in
          if uu____5961 then failwith "Aborting due to --abort_on" else ()))
      else ()
  
let (add_one : issue -> unit) =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____6002  ->
         let uu____6003 = FStar_ST.op_Bang current_handler  in
         wrapped_eh_add_one uu____6003 issue)
  
let (add_many : issue Prims.list -> unit) =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____6035  ->
         let uu____6036 =
           let uu____6041 = FStar_ST.op_Bang current_handler  in
           wrapped_eh_add_one uu____6041  in
         FStar_List.iter uu____6036 issues)
  
let (report_all : unit -> issue Prims.list) =
  fun uu____6068  ->
    let uu____6069 =
      let uu____6076 = FStar_ST.op_Bang current_handler  in
      uu____6076.eh_report  in
    uu____6069 ()
  
let (clear : unit -> unit) =
  fun uu____6101  ->
    let uu____6102 =
      let uu____6107 = FStar_ST.op_Bang current_handler  in
      uu____6107.eh_clear  in
    uu____6102 ()
  
let (set_handler : error_handler -> unit) =
  fun handler  ->
    let issues = report_all ()  in
    clear ();
    FStar_ST.op_Colon_Equals current_handler handler;
    add_many issues
  
type error_message_prefix =
  {
  set_prefix: Prims.string -> unit ;
  append_prefix: Prims.string -> Prims.string ;
  clear_prefix: unit -> unit }
let (__proj__Mkerror_message_prefix__item__set_prefix :
  error_message_prefix -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { set_prefix; append_prefix; clear_prefix;_} -> set_prefix
  
let (__proj__Mkerror_message_prefix__item__append_prefix :
  error_message_prefix -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { set_prefix; append_prefix; clear_prefix;_} -> append_prefix
  
let (__proj__Mkerror_message_prefix__item__clear_prefix :
  error_message_prefix -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { set_prefix; append_prefix; clear_prefix;_} -> clear_prefix
  
let (message_prefix : error_message_prefix) =
  let pfx = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set_prefix s =
    FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some s)  in
  let clear_prefix uu____6352 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None  in
  let append_prefix s =
    let uu____6410 = FStar_ST.op_Bang pfx  in
    match uu____6410 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p -> Prims.strcat p (Prims.strcat ": " s)
     in
  { set_prefix; append_prefix; clear_prefix } 
let findIndex :
  'Auu____6476 'Auu____6477 .
    ('Auu____6476 * 'Auu____6477) Prims.list -> 'Auu____6476 -> Prims.int
  =
  fun l  ->
    fun v1  ->
      FStar_All.pipe_right l
        (FStar_List.index
           (fun uu___83_6515  ->
              match uu___83_6515 with
              | (e,uu____6522) when e = v1 -> true
              | uu____6524 -> false))
  
let (errno_of_error : raw_error -> Prims.int) =
  fun e  -> findIndex default_flags e 
let (flags : flag Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_warn_error_flags : unit) =
  let rec aux r l =
    match l with | [] -> r | (e,f)::tl1 -> aux (FStar_List.append r [f]) tl1
     in
  let uu____6604 = aux [] default_flags  in
  FStar_ST.op_Colon_Equals flags uu____6604 
let (diag : FStar_Range.range -> Prims.string -> unit) =
  fun r  ->
    fun msg  ->
      let uu____6643 = FStar_Options.debug_any ()  in
      if uu____6643
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None)
      else ()
  
let (defensive_errno : Prims.int) = errno_of_error Warning_Defensive 
let (lookup : flag Prims.list -> Prims.int -> flag) =
  fun flags1  ->
    fun errno  ->
      let uu____6668 =
        (errno = defensive_errno) && (FStar_Options.defensive_fail ())  in
      if uu____6668 then CAlwaysError else FStar_List.nth flags1 errno
  
let (log_issue : FStar_Range.range -> (raw_error * Prims.string) -> unit) =
  fun r  ->
    fun uu____6689  ->
      match uu____6689 with
      | (e,msg) ->
          let errno = errno_of_error e  in
          let uu____6701 =
            let uu____6702 = FStar_ST.op_Bang flags  in
            lookup uu____6702 errno  in
          (match uu____6701 with
           | CAlwaysError  ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
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
                   (FStar_Pervasives_Native.Some errno)
                  in
               let uu____6733 = FStar_Options.ide ()  in
               if uu____6733
               then add_one i
               else
                 (let uu____6738 =
                    let uu____6740 = format_issue i  in
                    Prims.strcat
                      "don't use log_issue to report fatal error, should use raise_error: "
                      uu____6740
                     in
                  failwith uu____6738))
  
let (add_errors :
  (raw_error * Prims.string * FStar_Range.range) Prims.list -> unit) =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____6768  ->
         FStar_List.iter
           (fun uu____6781  ->
              match uu____6781 with
              | (e,msg,r) ->
                  let uu____6794 =
                    let uu____6800 = message_prefix.append_prefix msg  in
                    (e, uu____6800)  in
                  log_issue r uu____6794) errs)
  
let (issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option) =
  fun uu___84_6810  ->
    match uu___84_6810 with
    | Error (e,msg,r) ->
        let errno = errno_of_error e  in
        let uu____6820 =
          let uu____6821 = message_prefix.append_prefix msg  in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____6821
            (FStar_Pervasives_Native.Some errno)
           in
        FStar_Pervasives_Native.Some uu____6820
    | FStar_Util.NYI msg ->
        let uu____6826 =
          let uu____6827 = message_prefix.append_prefix msg  in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____6827
            FStar_Pervasives_Native.None
           in
        FStar_Pervasives_Native.Some uu____6826
    | Err (e,msg) ->
        let errno = errno_of_error e  in
        let uu____6836 =
          let uu____6837 = message_prefix.append_prefix msg  in
          mk_issue EError FStar_Pervasives_Native.None uu____6837
            (FStar_Pervasives_Native.Some errno)
           in
        FStar_Pervasives_Native.Some uu____6836
    | uu____6840 -> FStar_Pervasives_Native.None
  
let (err_exn : Prims.exn -> unit) =
  fun exn  ->
    if exn = Stop
    then ()
    else
      (let uu____6850 = issue_of_exn exn  in
       match uu____6850 with
       | FStar_Pervasives_Native.Some issue -> add_one issue
       | FStar_Pervasives_Native.None  -> FStar_Exn.raise exn)
  
let (handleable : Prims.exn -> Prims.bool) =
  fun uu___85_6860  ->
    match uu___85_6860 with
    | Error uu____6862 -> true
    | FStar_Util.NYI uu____6871 -> true
    | Stop  -> true
    | Err uu____6875 -> true
    | uu____6882 -> false
  
let (stop_if_err : unit -> unit) =
  fun uu____6889  ->
    let uu____6890 =
      let uu____6892 = get_err_count ()  in
      uu____6892 > (Prims.parse_int "0")  in
    if uu____6890 then FStar_Exn.raise Stop else ()
  
let raise_error :
  'Auu____6905 .
    (raw_error * Prims.string) -> FStar_Range.range -> 'Auu____6905
  =
  fun uu____6919  ->
    fun r  ->
      match uu____6919 with | (e,msg) -> FStar_Exn.raise (Error (e, msg, r))
  
let raise_err : 'Auu____6936 . (raw_error * Prims.string) -> 'Auu____6936 =
  fun uu____6946  ->
    match uu____6946 with | (e,msg) -> FStar_Exn.raise (Err (e, msg))
  
let (update_flags : (flag * Prims.string) Prims.list -> unit) =
  fun l  ->
    let compare1 uu____7007 uu____7008 =
      match (uu____7007, uu____7008) with
      | ((uu____7050,(a,uu____7052)),(uu____7053,(b,uu____7055))) ->
          if a > b
          then (Prims.parse_int "1")
          else
            if a < b then ~- (Prims.parse_int "1") else (Prims.parse_int "0")
       in
    let set_one_flag f d =
      match (f, d) with
      | (CWarning ,CAlwaysError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot turn an error into warning")
      | (CError ,CAlwaysError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot turn an error into warning")
      | (CSilent ,CAlwaysError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting, "cannot silence an error")
      | (uu____7124,CFatal ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot reset the error level of a fatal error")
      | uu____7127 -> f  in
    let rec set_flag i l1 =
      let d =
        let uu____7170 = FStar_ST.op_Bang flags  in
        FStar_List.nth uu____7170 i  in
      match l1 with
      | [] -> d
      | (f,(l2,h))::tl1 ->
          if (i >= l2) && (i <= h)
          then set_one_flag f d
          else if i < l2 then d else set_flag i tl1
       in
    let rec aux f i l1 sorted1 =
      match l1 with
      | [] -> f
      | hd1::tl1 ->
          let uu____7311 =
            let uu____7314 =
              let uu____7317 = set_flag i sorted1  in [uu____7317]  in
            FStar_List.append f uu____7314  in
          aux uu____7311 (i + (Prims.parse_int "1")) tl1 sorted1
       in
    let rec compute_range result l1 =
      match l1 with
      | [] -> result
      | (f,s)::tl1 ->
          let r = FStar_Util.split s ".."  in
          let uu____7419 =
            match r with
            | r1::r2::[] ->
                let uu____7439 = FStar_Util.int_of_string r1  in
                let uu____7441 = FStar_Util.int_of_string r2  in
                (uu____7439, uu____7441)
            | uu____7445 ->
                let uu____7449 =
                  let uu____7455 =
                    FStar_Util.format1 "Malformed warn-error range %s" s  in
                  (Fatal_InvalidWarnErrorSetting, uu____7455)  in
                raise_err uu____7449
             in
          (match uu____7419 with
           | (l2,h) ->
               (if
                  (l2 < (Prims.parse_int "0")) ||
                    (h >= (FStar_List.length default_flags))
                then
                  (let uu____7490 =
                     let uu____7496 =
                       let uu____7498 = FStar_Util.string_of_int l2  in
                       let uu____7500 = FStar_Util.string_of_int h  in
                       FStar_Util.format2 "No error for warn_error %s..%s"
                         uu____7498 uu____7500
                        in
                     (Fatal_InvalidWarnErrorSetting, uu____7496)  in
                   raise_err uu____7490)
                else ();
                compute_range (FStar_List.append result [(f, (l2, h))]) tl1))
       in
    let range = compute_range [] l  in
    let sorted1 = FStar_List.sortWith compare1 range  in
    let uu____7590 =
      let uu____7593 = FStar_ST.op_Bang flags  in
      aux [] (Prims.parse_int "0") uu____7593 sorted1  in
    FStar_ST.op_Colon_Equals flags uu____7590
  
let catch_errors :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f  ->
    let newh = mk_default_handler false  in
    let old = FStar_ST.op_Bang current_handler  in
    FStar_ST.op_Colon_Equals current_handler newh;
    (let r =
       try
         (fun uu___87_7716  ->
            match () with
            | () -> let r = f ()  in FStar_Pervasives_Native.Some r) ()
       with
       | uu___86_7722 -> (err_exn uu___86_7722; FStar_Pervasives_Native.None)
        in
     let errs = newh.eh_report ()  in
     FStar_ST.op_Colon_Equals current_handler old; (errs, r))
  