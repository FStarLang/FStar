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
  | Warning_SMTPatternIllFormed 
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
    | uu____36209 -> false
  
let (uu___is_Error_IDETooManyPops : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_IDETooManyPops  -> true
    | uu____36220 -> false
  
let (uu___is_Error_IDEUnrecognized : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_IDEUnrecognized  -> true
    | uu____36231 -> false
  
let (uu___is_Error_InductiveTypeNotSatisfyPositivityCondition :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_InductiveTypeNotSatisfyPositivityCondition  -> true
    | uu____36242 -> false
  
let (uu___is_Error_InvalidUniverseVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_InvalidUniverseVar  -> true
    | uu____36253 -> false
  
let (uu___is_Error_MissingFileName : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_MissingFileName  -> true
    | uu____36264 -> false
  
let (uu___is_Error_ModuleFileNameMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_ModuleFileNameMismatch  -> true
    | uu____36275 -> false
  
let (uu___is_Error_OpPlusInUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_OpPlusInUniverse  -> true
    | uu____36286 -> false
  
let (uu___is_Error_OutOfRange : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_OutOfRange  -> true | uu____36297 -> false
  
let (uu___is_Error_ProofObligationFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_ProofObligationFailed  -> true
    | uu____36308 -> false
  
let (uu___is_Error_TooManyFiles : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_TooManyFiles  -> true | uu____36319 -> false
  
let (uu___is_Error_TypeCheckerFailToProve : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_TypeCheckerFailToProve  -> true
    | uu____36330 -> false
  
let (uu___is_Error_TypeError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_TypeError  -> true | uu____36341 -> false
  
let (uu___is_Error_UncontrainedUnificationVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UncontrainedUnificationVar  -> true
    | uu____36352 -> false
  
let (uu___is_Error_UnexpectedGTotComputation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedGTotComputation  -> true
    | uu____36363 -> false
  
let (uu___is_Error_UnexpectedInstance : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedInstance  -> true
    | uu____36374 -> false
  
let (uu___is_Error_UnknownFatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnknownFatal_AssertionFailure  -> true
    | uu____36385 -> false
  
let (uu___is_Error_Z3InvocationError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_Z3InvocationError  -> true
    | uu____36396 -> false
  
let (uu___is_Error_IDEAssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_IDEAssertionFailure  -> true
    | uu____36407 -> false
  
let (uu___is_Error_Z3SolverError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_Z3SolverError  -> true
    | uu____36418 -> false
  
let (uu___is_Fatal_AbstractTypeDeclarationInInterface :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AbstractTypeDeclarationInInterface  -> true
    | uu____36429 -> false
  
let (uu___is_Fatal_ActionMustHaveFunctionType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ActionMustHaveFunctionType  -> true
    | uu____36440 -> false
  
let (uu___is_Fatal_AlreadyDefinedTopLevelDeclaration :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AlreadyDefinedTopLevelDeclaration  -> true
    | uu____36451 -> false
  
let (uu___is_Fatal_ArgumentLengthMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ArgumentLengthMismatch  -> true
    | uu____36462 -> false
  
let (uu___is_Fatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AssertionFailure  -> true
    | uu____36473 -> false
  
let (uu___is_Fatal_AssignToImmutableValues : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AssignToImmutableValues  -> true
    | uu____36484 -> false
  
let (uu___is_Fatal_AssumeValInInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_AssumeValInInterface  -> true
    | uu____36495 -> false
  
let (uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_BadlyInstantiatedSynthByTactic  -> true
    | uu____36506 -> false
  
let (uu___is_Fatal_BadSignatureShape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_BadSignatureShape  -> true
    | uu____36517 -> false
  
let (uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_BinderAndArgsLengthMismatch  -> true
    | uu____36528 -> false
  
let (uu___is_Fatal_BothValAndLetInInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_BothValAndLetInInterface  -> true
    | uu____36539 -> false
  
let (uu___is_Fatal_CardinalityConstraintViolated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_CardinalityConstraintViolated  -> true
    | uu____36550 -> false
  
let (uu___is_Fatal_ComputationNotTotal : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ComputationNotTotal  -> true
    | uu____36561 -> false
  
let (uu___is_Fatal_ComputationTypeNotAllowed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ComputationTypeNotAllowed  -> true
    | uu____36572 -> false
  
let (uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_ComputedTypeNotMatchAnnotation  -> true
    | uu____36583 -> false
  
let (uu___is_Fatal_ConstructorArgLengthMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorArgLengthMismatch  -> true
    | uu____36594 -> false
  
let (uu___is_Fatal_ConstructorFailedCheck : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorFailedCheck  -> true
    | uu____36605 -> false
  
let (uu___is_Fatal_ConstructorNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstructorNotFound  -> true
    | uu____36616 -> false
  
let (uu___is_Fatal_ConstsructorBuildWrongType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ConstsructorBuildWrongType  -> true
    | uu____36627 -> false
  
let (uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_CycleInRecTypeAbbreviation  -> true
    | uu____36638 -> false
  
let (uu___is_Fatal_DataContructorNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DataContructorNotFound  -> true
    | uu____36649 -> false
  
let (uu___is_Fatal_DefaultQualifierNotAllowedOnEffects :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DefaultQualifierNotAllowedOnEffects  -> true
    | uu____36660 -> false
  
let (uu___is_Fatal_DefinitionNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DefinitionNotFound  -> true
    | uu____36671 -> false
  
let (uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DisjuctivePatternVarsMismatch  -> true
    | uu____36682 -> false
  
let (uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DivergentComputationCannotBeIncludedInTotal  -> true
    | uu____36693 -> false
  
let (uu___is_Fatal_DuplicateInImplementation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateInImplementation  -> true
    | uu____36704 -> false
  
let (uu___is_Fatal_DuplicateModuleOrInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateModuleOrInterface  -> true
    | uu____36715 -> false
  
let (uu___is_Fatal_DuplicateTopLevelNames : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateTopLevelNames  -> true
    | uu____36726 -> false
  
let (uu___is_Fatal_DuplicateTypeAnnotationAndValDecl :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_DuplicateTypeAnnotationAndValDecl  -> true
    | uu____36737 -> false
  
let (uu___is_Fatal_EffectCannotBeReified : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectCannotBeReified  -> true
    | uu____36748 -> false
  
let (uu___is_Fatal_EffectConstructorNotFullyApplied :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectConstructorNotFullyApplied  -> true
    | uu____36759 -> false
  
let (uu___is_Fatal_EffectfulAndPureComputationMismatch :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectfulAndPureComputationMismatch  -> true
    | uu____36770 -> false
  
let (uu___is_Fatal_EffectNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectNotFound  -> true
    | uu____36781 -> false
  
let (uu___is_Fatal_EffectsCannotBeComposed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectsCannotBeComposed  -> true
    | uu____36792 -> false
  
let (uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_ErrorInSolveDeferredConstraints  -> true
    | uu____36803 -> false
  
let (uu___is_Fatal_ErrorsReported : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ErrorsReported  -> true
    | uu____36814 -> false
  
let (uu___is_Fatal_EscapedBoundVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EscapedBoundVar  -> true
    | uu____36825 -> false
  
let (uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedArrowAnnotatedType  -> true
    | uu____36836 -> false
  
let (uu___is_Fatal_ExpectedGhostExpression : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedGhostExpression  -> true
    | uu____36847 -> false
  
let (uu___is_Fatal_ExpectedPureExpression : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectedPureExpression  -> true
    | uu____36858 -> false
  
let (uu___is_Fatal_ExpectNormalizedEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectNormalizedEffect  -> true
    | uu____36869 -> false
  
let (uu___is_Fatal_ExpectTermGotFunction : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectTermGotFunction  -> true
    | uu____36880 -> false
  
let (uu___is_Fatal_ExpectTrivialPreCondition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ExpectTrivialPreCondition  -> true
    | uu____36891 -> false
  
let (uu___is_Fatal_FailToCompileNativeTactic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToCompileNativeTactic  -> true
    | uu____36902 -> false
  
let (uu___is_Fatal_FailToExtractNativeTactic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToExtractNativeTactic  -> true
    | uu____36913 -> false
  
let (uu___is_Fatal_FailToProcessPragma : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToProcessPragma  -> true
    | uu____36924 -> false
  
let (uu___is_Fatal_FailToResolveImplicitArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToResolveImplicitArgument  -> true
    | uu____36935 -> false
  
let (uu___is_Fatal_FailToSolveUniverseInEquality : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FailToSolveUniverseInEquality  -> true
    | uu____36946 -> false
  
let (uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_FieldsNotBelongToSameRecordType  -> true
    | uu____36957 -> false
  
let (uu___is_Fatal_ForbiddenReferenceToCurrentModule :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ForbiddenReferenceToCurrentModule  -> true
    | uu____36968 -> false
  
let (uu___is_Fatal_FreeVariables : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FreeVariables  -> true
    | uu____36979 -> false
  
let (uu___is_Fatal_FunctionTypeExpected : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FunctionTypeExpected  -> true
    | uu____36990 -> false
  
let (uu___is_Fatal_IdentifierNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IdentifierNotFound  -> true
    | uu____37001 -> false
  
let (uu___is_Fatal_IllAppliedConstant : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IllAppliedConstant  -> true
    | uu____37012 -> false
  
let (uu___is_Fatal_IllegalCharInByteArray : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IllegalCharInByteArray  -> true
    | uu____37023 -> false
  
let (uu___is_Fatal_IllegalCharInOperatorName : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IllegalCharInOperatorName  -> true
    | uu____37034 -> false
  
let (uu___is_Fatal_IllTyped : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_IllTyped  -> true | uu____37045 -> false
  
let (uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleAbbrevLidBundle  -> true
    | uu____37056 -> false
  
let (uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleAbbrevRenameBundle  -> true
    | uu____37067 -> false
  
let (uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleInductiveWithAbbrev  -> true
    | uu____37078 -> false
  
let (uu___is_Fatal_ImpossiblePrePostAbs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossiblePrePostAbs  -> true
    | uu____37089 -> false
  
let (uu___is_Fatal_ImpossiblePrePostArrow : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossiblePrePostArrow  -> true
    | uu____37100 -> false
  
let (uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleToGenerateDMEffect  -> true
    | uu____37111 -> false
  
let (uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevBundle  -> true
    | uu____37122 -> false
  
let (uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevSigeltBundle  -> true
    | uu____37133 -> false
  
let (uu___is_Fatal_IncludeModuleNotPrepared : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncludeModuleNotPrepared  -> true
    | uu____37144 -> false
  
let (uu___is_Fatal_IncoherentInlineUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncoherentInlineUniverse  -> true
    | uu____37155 -> false
  
let (uu___is_Fatal_IncompatibleKinds : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleKinds  -> true
    | uu____37166 -> false
  
let (uu___is_Fatal_IncompatibleNumberOfTypes : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleNumberOfTypes  -> true
    | uu____37177 -> false
  
let (uu___is_Fatal_IncompatibleSetOfUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleSetOfUniverse  -> true
    | uu____37188 -> false
  
let (uu___is_Fatal_IncompatibleUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncompatibleUniverse  -> true
    | uu____37199 -> false
  
let (uu___is_Fatal_InconsistentImplicitArgumentAnnotation :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentImplicitArgumentAnnotation  -> true
    | uu____37210 -> false
  
let (uu___is_Fatal_InconsistentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentImplicitQualifier  -> true
    | uu____37221 -> false
  
let (uu___is_Fatal_InconsistentQualifierAnnotation : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_InconsistentQualifierAnnotation  -> true
    | uu____37232 -> false
  
let (uu___is_Fatal_InferredTypeCauseVarEscape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InferredTypeCauseVarEscape  -> true
    | uu____37243 -> false
  
let (uu___is_Fatal_InlineRenamedAsUnfold : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InlineRenamedAsUnfold  -> true
    | uu____37254 -> false
  
let (uu___is_Fatal_InsufficientPatternArguments : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InsufficientPatternArguments  -> true
    | uu____37265 -> false
  
let (uu___is_Fatal_InterfaceAlreadyProcessed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceAlreadyProcessed  -> true
    | uu____37276 -> false
  
let (uu___is_Fatal_InterfaceNotImplementedByModule : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceNotImplementedByModule  -> true
    | uu____37287 -> false
  
let (uu___is_Fatal_InterfaceWithTypeImplementation : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_InterfaceWithTypeImplementation  -> true
    | uu____37298 -> false
  
let (uu___is_Fatal_InvalidFloatingPointNumber : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidFloatingPointNumber  -> true
    | uu____37309 -> false
  
let (uu___is_Fatal_InvalidFSDocKeyword : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidFSDocKeyword  -> true
    | uu____37320 -> false
  
let (uu___is_Fatal_InvalidIdentifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidIdentifier  -> true
    | uu____37331 -> false
  
let (uu___is_Fatal_InvalidLemmaArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidLemmaArgument  -> true
    | uu____37342 -> false
  
let (uu___is_Fatal_InvalidNumericLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidNumericLiteral  -> true
    | uu____37353 -> false
  
let (uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidRedefinitionOfLexT  -> true
    | uu____37364 -> false
  
let (uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidUnicodeInStringLiteral  -> true
    | uu____37375 -> false
  
let (uu___is_Fatal_InvalidUTF8Encoding : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidUTF8Encoding  -> true
    | uu____37386 -> false
  
let (uu___is_Fatal_InvalidWarnErrorSetting : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_InvalidWarnErrorSetting  -> true
    | uu____37397 -> false
  
let (uu___is_Fatal_LetBoundMonadicMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetBoundMonadicMismatch  -> true
    | uu____37408 -> false
  
let (uu___is_Fatal_LetMutableForVariablesOnly : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetMutableForVariablesOnly  -> true
    | uu____37419 -> false
  
let (uu___is_Fatal_LetOpenModuleOnly : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetOpenModuleOnly  -> true
    | uu____37430 -> false
  
let (uu___is_Fatal_LetRecArgumentMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_LetRecArgumentMismatch  -> true
    | uu____37441 -> false
  
let (uu___is_Fatal_MalformedActionDeclaration : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MalformedActionDeclaration  -> true
    | uu____37452 -> false
  
let (uu___is_Fatal_MismatchedPatternType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MismatchedPatternType  -> true
    | uu____37463 -> false
  
let (uu___is_Fatal_MismatchUniversePolymorphic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MismatchUniversePolymorphic  -> true
    | uu____37474 -> false
  
let (uu___is_Fatal_MissingDataConstructor : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingDataConstructor  -> true
    | uu____37485 -> false
  
let (uu___is_Fatal_MissingExposeInterfacesOption : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingExposeInterfacesOption  -> true
    | uu____37496 -> false
  
let (uu___is_Fatal_MissingFieldInRecord : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingFieldInRecord  -> true
    | uu____37507 -> false
  
let (uu___is_Fatal_MissingImplementation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingImplementation  -> true
    | uu____37518 -> false
  
let (uu___is_Fatal_MissingImplicitArguments : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingImplicitArguments  -> true
    | uu____37529 -> false
  
let (uu___is_Fatal_MissingInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingInterface  -> true
    | uu____37540 -> false
  
let (uu___is_Fatal_MissingNameInBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingNameInBinder  -> true
    | uu____37551 -> false
  
let (uu___is_Fatal_MissingPrimsModule : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingPrimsModule  -> true
    | uu____37562 -> false
  
let (uu___is_Fatal_MissingQuantifierBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MissingQuantifierBinder  -> true
    | uu____37573 -> false
  
let (uu___is_Fatal_ModuleExpected : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleExpected  -> true
    | uu____37584 -> false
  
let (uu___is_Fatal_ModuleFileNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleFileNotFound  -> true
    | uu____37595 -> false
  
let (uu___is_Fatal_ModuleFirstStatement : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleFirstStatement  -> true
    | uu____37606 -> false
  
let (uu___is_Fatal_ModuleNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleNotFound  -> true
    | uu____37617 -> false
  
let (uu___is_Fatal_ModuleOrFileNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ModuleOrFileNotFound  -> true
    | uu____37628 -> false
  
let (uu___is_Fatal_MonadAlreadyDefined : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MonadAlreadyDefined  -> true
    | uu____37639 -> false
  
let (uu___is_Fatal_MoreThanOneDeclaration : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MoreThanOneDeclaration  -> true
    | uu____37650 -> false
  
let (uu___is_Fatal_MultipleLetBinding : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_MultipleLetBinding  -> true
    | uu____37661 -> false
  
let (uu___is_Fatal_NameNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_NameNotFound  -> true | uu____37672 -> false
  
let (uu___is_Fatal_NameSpaceNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NameSpaceNotFound  -> true
    | uu____37683 -> false
  
let (uu___is_Fatal_NegativeUniverseConstFatal_NotSupported :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NegativeUniverseConstFatal_NotSupported  -> true
    | uu____37694 -> false
  
let (uu___is_Fatal_NoFileProvided : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NoFileProvided  -> true
    | uu____37705 -> false
  
let (uu___is_Fatal_NonInductiveInMutuallyDefinedType :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonInductiveInMutuallyDefinedType  -> true
    | uu____37716 -> false
  
let (uu___is_Fatal_NonLinearPatternNotPermitted : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonLinearPatternNotPermitted  -> true
    | uu____37727 -> false
  
let (uu___is_Fatal_NonLinearPatternVars : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonLinearPatternVars  -> true
    | uu____37738 -> false
  
let (uu___is_Fatal_NonSingletonTopLevel : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonSingletonTopLevel  -> true
    | uu____37749 -> false
  
let (uu___is_Fatal_NonSingletonTopLevelModule : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonSingletonTopLevelModule  -> true
    | uu____37760 -> false
  
let (uu___is_Fatal_NonTopRecFunctionNotFullyEncoded :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonTopRecFunctionNotFullyEncoded  -> true
    | uu____37771 -> false
  
let (uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonTrivialPreConditionInPrims  -> true
    | uu____37782 -> false
  
let (uu___is_Fatal_NonVariableInductiveTypeParameter :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NonVariableInductiveTypeParameter  -> true
    | uu____37793 -> false
  
let (uu___is_Fatal_NotApplicationOrFv : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotApplicationOrFv  -> true
    | uu____37804 -> false
  
let (uu___is_Fatal_NotEnoughArgsToEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotEnoughArgsToEffect  -> true
    | uu____37815 -> false
  
let (uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotEnoughArgumentsForEffect  -> true
    | uu____37826 -> false
  
let (uu___is_Fatal_NotFunctionType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotFunctionType  -> true
    | uu____37837 -> false
  
let (uu___is_Fatal_NotSupported : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_NotSupported  -> true | uu____37848 -> false
  
let (uu___is_Fatal_NotTopLevelModule : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotTopLevelModule  -> true
    | uu____37859 -> false
  
let (uu___is_Fatal_NotValidFStarFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotValidFStarFile  -> true
    | uu____37870 -> false
  
let (uu___is_Fatal_NotValidIncludeDirectory : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_NotValidIncludeDirectory  -> true
    | uu____37881 -> false
  
let (uu___is_Fatal_OneModulePerFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_OneModulePerFile  -> true
    | uu____37892 -> false
  
let (uu___is_Fatal_OpenGoalsInSynthesis : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_OpenGoalsInSynthesis  -> true
    | uu____37903 -> false
  
let (uu___is_Fatal_OptionsNotCompatible : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_OptionsNotCompatible  -> true
    | uu____37914 -> false
  
let (uu___is_Fatal_OutOfOrder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_OutOfOrder  -> true | uu____37925 -> false
  
let (uu___is_Fatal_ParseErrors : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_ParseErrors  -> true | uu____37936 -> false
  
let (uu___is_Fatal_ParseItError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_ParseItError  -> true | uu____37947 -> false
  
let (uu___is_Fatal_PolyTypeExpected : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_PolyTypeExpected  -> true
    | uu____37958 -> false
  
let (uu___is_Fatal_PossibleInfiniteTyp : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_PossibleInfiniteTyp  -> true
    | uu____37969 -> false
  
let (uu___is_Fatal_PreModuleMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_PreModuleMismatch  -> true
    | uu____37980 -> false
  
let (uu___is_Fatal_QulifierListNotPermitted : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_QulifierListNotPermitted  -> true
    | uu____37991 -> false
  
let (uu___is_Fatal_RecursiveFunctionLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_RecursiveFunctionLiteral  -> true
    | uu____38002 -> false
  
let (uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ReflectOnlySupportedOnEffects  -> true
    | uu____38013 -> false
  
let (uu___is_Fatal_ReservedPrefix : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ReservedPrefix  -> true
    | uu____38024 -> false
  
let (uu___is_Fatal_SMTOutputParseError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SMTOutputParseError  -> true
    | uu____38035 -> false
  
let (uu___is_Fatal_SMTSolverError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SMTSolverError  -> true
    | uu____38046 -> false
  
let (uu___is_Fatal_SyntaxError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_SyntaxError  -> true | uu____38057 -> false
  
let (uu___is_Fatal_SynthByTacticError : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SynthByTacticError  -> true
    | uu____38068 -> false
  
let (uu___is_Fatal_TacticGotStuck : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TacticGotStuck  -> true
    | uu____38079 -> false
  
let (uu___is_Fatal_TcOneFragmentFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TcOneFragmentFailed  -> true
    | uu____38090 -> false
  
let (uu___is_Fatal_TermOutsideOfDefLanguage : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TermOutsideOfDefLanguage  -> true
    | uu____38101 -> false
  
let (uu___is_Fatal_ToManyArgumentToFunction : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ToManyArgumentToFunction  -> true
    | uu____38112 -> false
  
let (uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyOrTooFewFileMatch  -> true
    | uu____38123 -> false
  
let (uu___is_Fatal_TooManyPatternArguments : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyPatternArguments  -> true
    | uu____38134 -> false
  
let (uu___is_Fatal_TooManyUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TooManyUniverse  -> true
    | uu____38145 -> false
  
let (uu___is_Fatal_TypeMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_TypeMismatch  -> true | uu____38156 -> false
  
let (uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TypeWithinPatternsAllowedOnVariablesOnly  -> true
    | uu____38167 -> false
  
let (uu___is_Fatal_UnableToReadFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnableToReadFile  -> true
    | uu____38178 -> false
  
let (uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnepxectedOrUnboundOperator  -> true
    | uu____38189 -> false
  
let (uu___is_Fatal_UnexpectedBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedBinder  -> true
    | uu____38200 -> false
  
let (uu___is_Fatal_UnexpectedBindShape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedBindShape  -> true
    | uu____38211 -> false
  
let (uu___is_Fatal_UnexpectedChar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedChar  -> true
    | uu____38222 -> false
  
let (uu___is_Fatal_UnexpectedComputationTypeForLetRec :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedComputationTypeForLetRec  -> true
    | uu____38233 -> false
  
let (uu___is_Fatal_UnexpectedConstructorType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedConstructorType  -> true
    | uu____38244 -> false
  
let (uu___is_Fatal_UnexpectedDataConstructor : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedDataConstructor  -> true
    | uu____38255 -> false
  
let (uu___is_Fatal_UnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedEffect  -> true
    | uu____38266 -> false
  
let (uu___is_Fatal_UnexpectedEmptyRecord : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedEmptyRecord  -> true
    | uu____38277 -> false
  
let (uu___is_Fatal_UnexpectedExpressionType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedExpressionType  -> true
    | uu____38288 -> false
  
let (uu___is_Fatal_UnexpectedFunctionParameterType : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedFunctionParameterType  -> true
    | uu____38299 -> false
  
let (uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGeneralizedUniverse  -> true
    | uu____38310 -> false
  
let (uu___is_Fatal_UnexpectedGTotForLetRec : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGTotForLetRec  -> true
    | uu____38321 -> false
  
let (uu___is_Fatal_UnexpectedGuard : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedGuard  -> true
    | uu____38332 -> false
  
let (uu___is_Fatal_UnexpectedIdentifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedIdentifier  -> true
    | uu____38343 -> false
  
let (uu___is_Fatal_UnexpectedImplicitArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedImplicitArgument  -> true
    | uu____38354 -> false
  
let (uu___is_Fatal_UnexpectedImplictArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedImplictArgument  -> true
    | uu____38365 -> false
  
let (uu___is_Fatal_UnexpectedInductivetype : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedInductivetype  -> true
    | uu____38376 -> false
  
let (uu___is_Fatal_UnexpectedLetBinding : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedLetBinding  -> true
    | uu____38387 -> false
  
let (uu___is_Fatal_UnexpectedModuleDeclaration : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedModuleDeclaration  -> true
    | uu____38398 -> false
  
let (uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedNumberOfUniverse  -> true
    | uu____38409 -> false
  
let (uu___is_Fatal_UnexpectedNumericLiteral : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedNumericLiteral  -> true
    | uu____38420 -> false
  
let (uu___is_Fatal_UnexpectedOperatorSymbol : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedOperatorSymbol  -> true
    | uu____38431 -> false
  
let (uu___is_Fatal_UnexpectedPattern : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedPattern  -> true
    | uu____38442 -> false
  
let (uu___is_Fatal_UnexpectedPosition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedPosition  -> true
    | uu____38453 -> false
  
let (uu___is_Fatal_UnExpectedPreCondition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnExpectedPreCondition  -> true
    | uu____38464 -> false
  
let (uu___is_Fatal_UnexpectedReturnShape : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedReturnShape  -> true
    | uu____38475 -> false
  
let (uu___is_Fatal_UnexpectedSignatureForMonad : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedSignatureForMonad  -> true
    | uu____38486 -> false
  
let (uu___is_Fatal_UnexpectedTerm : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTerm  -> true
    | uu____38497 -> false
  
let (uu___is_Fatal_UnexpectedTermInUniverse : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermInUniverse  -> true
    | uu____38508 -> false
  
let (uu___is_Fatal_UnexpectedTermType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermType  -> true
    | uu____38519 -> false
  
let (uu___is_Fatal_UnexpectedTermVQuote : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedTermVQuote  -> true
    | uu____38530 -> false
  
let (uu___is_Fatal_UnexpectedUniversePolymorphicReturn :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedUniversePolymorphicReturn  -> true
    | uu____38541 -> false
  
let (uu___is_Fatal_UnexpectedUniverseVariable : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedUniverseVariable  -> true
    | uu____38552 -> false
  
let (uu___is_Fatal_UnfoldableDeprecated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnfoldableDeprecated  -> true
    | uu____38563 -> false
  
let (uu___is_Fatal_UnificationNotWellFormed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnificationNotWellFormed  -> true
    | uu____38574 -> false
  
let (uu___is_Fatal_Uninstantiated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_Uninstantiated  -> true
    | uu____38585 -> false
  
let (uu___is_Error_UninstantiatedUnificationVarInTactic :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UninstantiatedUnificationVarInTactic  -> true
    | uu____38596 -> false
  
let (uu___is_Fatal_UninstantiatedVarInTactic : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UninstantiatedVarInTactic  -> true
    | uu____38607 -> false
  
let (uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UniverseMightContainSumOfTwoUnivVars  -> true
    | uu____38618 -> false
  
let (uu___is_Fatal_UniversePolymorphicInnerLetBound :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UniversePolymorphicInnerLetBound  -> true
    | uu____38629 -> false
  
let (uu___is_Fatal_UnknownAttribute : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnknownAttribute  -> true
    | uu____38640 -> false
  
let (uu___is_Fatal_UnknownToolForDep : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnknownToolForDep  -> true
    | uu____38651 -> false
  
let (uu___is_Fatal_UnrecognizedExtension : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnrecognizedExtension  -> true
    | uu____38662 -> false
  
let (uu___is_Fatal_UnresolvedPatternVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnresolvedPatternVar  -> true
    | uu____38673 -> false
  
let (uu___is_Fatal_UnsupportedConstant : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedConstant  -> true
    | uu____38684 -> false
  
let (uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedDisjuctivePatterns  -> true
    | uu____38695 -> false
  
let (uu___is_Fatal_UnsupportedQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnsupportedQualifier  -> true
    | uu____38706 -> false
  
let (uu___is_Fatal_UserTacticFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UserTacticFailure  -> true
    | uu____38717 -> false
  
let (uu___is_Fatal_ValueRestriction : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_ValueRestriction  -> true
    | uu____38728 -> false
  
let (uu___is_Fatal_VariableNotFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_VariableNotFound  -> true
    | uu____38739 -> false
  
let (uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WrongBodyTypeForReturnWP  -> true
    | uu____38750 -> false
  
let (uu___is_Fatal_WrongDataAppHeadFormat : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WrongDataAppHeadFormat  -> true
    | uu____38761 -> false
  
let (uu___is_Fatal_WrongDefinitionOrder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WrongDefinitionOrder  -> true
    | uu____38772 -> false
  
let (uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Fatal_WrongResultTypeAfterConstrutor  -> true
    | uu____38783 -> false
  
let (uu___is_Fatal_WrongTerm : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_WrongTerm  -> true | uu____38794 -> false
  
let (uu___is_Fatal_WhenClauseNotSupported : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_WhenClauseNotSupported  -> true
    | uu____38805 -> false
  
let (uu___is_Unused01 : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unused01  -> true | uu____38816 -> false
  
let (uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Warning_AddImplicitAssumeNewQualifier  -> true
    | uu____38827 -> false
  
let (uu___is_Warning_AdmitWithoutDefinition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_AdmitWithoutDefinition  -> true
    | uu____38838 -> false
  
let (uu___is_Warning_CachedFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_CachedFile  -> true | uu____38849 -> false
  
let (uu___is_Warning_DefinitionNotTranslated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DefinitionNotTranslated  -> true
    | uu____38860 -> false
  
let (uu___is_Warning_DependencyFound : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DependencyFound  -> true
    | uu____38871 -> false
  
let (uu___is_Warning_DeprecatedEqualityOnBinder : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedEqualityOnBinder  -> true
    | uu____38882 -> false
  
let (uu___is_Warning_DeprecatedOpaqueQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedOpaqueQualifier  -> true
    | uu____38893 -> false
  
let (uu___is_Warning_DocOverwrite : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DocOverwrite  -> true
    | uu____38904 -> false
  
let (uu___is_Warning_FileNotWritten : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_FileNotWritten  -> true
    | uu____38915 -> false
  
let (uu___is_Warning_Filtered : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_Filtered  -> true | uu____38926 -> false
  
let (uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | Warning_FunctionLiteralPrecisionLoss  -> true
    | uu____38937 -> false
  
let (uu___is_Warning_FunctionNotExtacted : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_FunctionNotExtacted  -> true
    | uu____38948 -> false
  
let (uu___is_Warning_HintFailedToReplayProof : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_HintFailedToReplayProof  -> true
    | uu____38959 -> false
  
let (uu___is_Warning_HitReplayFailed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_HitReplayFailed  -> true
    | uu____38970 -> false
  
let (uu___is_Warning_IDEIgnoreCodeGen : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IDEIgnoreCodeGen  -> true
    | uu____38981 -> false
  
let (uu___is_Warning_IllFormedGoal : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IllFormedGoal  -> true
    | uu____38992 -> false
  
let (uu___is_Warning_InaccessibleArgument : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_InaccessibleArgument  -> true
    | uu____39003 -> false
  
let (uu___is_Warning_IncoherentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IncoherentImplicitQualifier  -> true
    | uu____39014 -> false
  
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReflect :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReflect  -> true
    | uu____39025 -> false
  
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReify :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReify  -> true
    | uu____39036 -> false
  
let (uu___is_Warning_MalformedWarnErrorList : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MalformedWarnErrorList  -> true
    | uu____39047 -> false
  
let (uu___is_Warning_MetaAlienNotATmUnknown : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MetaAlienNotATmUnknown  -> true
    | uu____39058 -> false
  
let (uu___is_Warning_MultipleAscriptions : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MultipleAscriptions  -> true
    | uu____39069 -> false
  
let (uu___is_Warning_NondependentUserDefinedDataType :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NondependentUserDefinedDataType  -> true
    | uu____39080 -> false
  
let (uu___is_Warning_NonListLiteralSMTPattern : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NonListLiteralSMTPattern  -> true
    | uu____39091 -> false
  
let (uu___is_Warning_NormalizationFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NormalizationFailure  -> true
    | uu____39102 -> false
  
let (uu___is_Warning_NotDependentArrow : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NotDependentArrow  -> true
    | uu____39113 -> false
  
let (uu___is_Warning_NotEmbedded : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NotEmbedded  -> true
    | uu____39124 -> false
  
let (uu___is_Warning_PatternMissingBoundVar : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_PatternMissingBoundVar  -> true
    | uu____39135 -> false
  
let (uu___is_Warning_RecursiveDependency : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_RecursiveDependency  -> true
    | uu____39146 -> false
  
let (uu___is_Warning_RedundantExplicitCurrying : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_RedundantExplicitCurrying  -> true
    | uu____39157 -> false
  
let (uu___is_Warning_SMTPatTDeprecated : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_SMTPatTDeprecated  -> true
    | uu____39168 -> false
  
let (uu___is_Warning_SMTPatternIllFormed : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_SMTPatternIllFormed  -> true
    | uu____39179 -> false
  
let (uu___is_Warning_TopLevelEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_TopLevelEffect  -> true
    | uu____39190 -> false
  
let (uu___is_Warning_UnboundModuleReference : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnboundModuleReference  -> true
    | uu____39201 -> false
  
let (uu___is_Warning_UnexpectedFile : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedFile  -> true
    | uu____39212 -> false
  
let (uu___is_Warning_UnexpectedFsTypApp : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedFsTypApp  -> true
    | uu____39223 -> false
  
let (uu___is_Warning_UnexpectedZ3Output : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnexpectedZ3Output  -> true
    | uu____39234 -> false
  
let (uu___is_Warning_UnprotectedTerm : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnprotectedTerm  -> true
    | uu____39245 -> false
  
let (uu___is_Warning_UnrecognizedAttribute : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnrecognizedAttribute  -> true
    | uu____39256 -> false
  
let (uu___is_Warning_UpperBoundCandidateAlreadyVisited :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UpperBoundCandidateAlreadyVisited  -> true
    | uu____39267 -> false
  
let (uu___is_Warning_UseDefaultEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UseDefaultEffect  -> true
    | uu____39278 -> false
  
let (uu___is_Warning_WrongErrorLocation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_WrongErrorLocation  -> true
    | uu____39289 -> false
  
let (uu___is_Warning_Z3InvocationWarning : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_Z3InvocationWarning  -> true
    | uu____39300 -> false
  
let (uu___is_Warning_CallNotImplementedAsWarning : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_CallNotImplementedAsWarning  -> true
    | uu____39311 -> false
  
let (uu___is_Warning_MissingInterfaceOrImplementation :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_MissingInterfaceOrImplementation  -> true
    | uu____39322 -> false
  
let (uu___is_Warning_ConstructorBuildsUnexpectedType :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ConstructorBuildsUnexpectedType  -> true
    | uu____39333 -> false
  
let (uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ModuleOrFileNotFoundWarning  -> true
    | uu____39344 -> false
  
let (uu___is_Error_NoLetMutable : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_NoLetMutable  -> true | uu____39355 -> false
  
let (uu___is_Error_BadImplicit : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_BadImplicit  -> true | uu____39366 -> false
  
let (uu___is_Warning_DeprecatedDefinition : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_DeprecatedDefinition  -> true
    | uu____39377 -> false
  
let (uu___is_Fatal_SMTEncodingArityMismatch : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SMTEncodingArityMismatch  -> true
    | uu____39388 -> false
  
let (uu___is_Warning_Defensive : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_Defensive  -> true | uu____39399 -> false
  
let (uu___is_Warning_CantInspect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_CantInspect  -> true
    | uu____39410 -> false
  
let (uu___is_Warning_NilGivenExplicitArgs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_NilGivenExplicitArgs  -> true
    | uu____39421 -> false
  
let (uu___is_Warning_ConsAppliedExplicitArgs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ConsAppliedExplicitArgs  -> true
    | uu____39432 -> false
  
let (uu___is_Warning_UnembedBinderKnot : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnembedBinderKnot  -> true
    | uu____39443 -> false
  
let (uu___is_Fatal_TacticProofRelevantGoal : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_TacticProofRelevantGoal  -> true
    | uu____39454 -> false
  
let (uu___is_Warning_TacAdmit : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning_TacAdmit  -> true | uu____39465 -> false
  
let (uu___is_Fatal_IncoherentPatterns : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_IncoherentPatterns  -> true
    | uu____39476 -> false
  
let (uu___is_Error_NoSMTButNeeded : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_NoSMTButNeeded  -> true
    | uu____39487 -> false
  
let (uu___is_Fatal_UnexpectedAntiquotation : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_UnexpectedAntiquotation  -> true
    | uu____39498 -> false
  
let (uu___is_Fatal_SplicedUndef : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fatal_SplicedUndef  -> true | uu____39509 -> false
  
let (uu___is_Fatal_SpliceUnembedFail : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_SpliceUnembedFail  -> true
    | uu____39520 -> false
  
let (uu___is_Warning_ExtractionUnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_ExtractionUnexpectedEffect  -> true
    | uu____39531 -> false
  
let (uu___is_Error_DidNotFail : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_DidNotFail  -> true | uu____39542 -> false
  
let (uu___is_Warning_UnappliedFail : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_UnappliedFail  -> true
    | uu____39553 -> false
  
let (uu___is_Warning_QuantifierWithoutPattern : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_QuantifierWithoutPattern  -> true
    | uu____39564 -> false
  
let (uu___is_Error_EmptyFailErrs : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_EmptyFailErrs  -> true
    | uu____39575 -> false
  
let (uu___is_Warning_logicqualifier : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_logicqualifier  -> true
    | uu____39586 -> false
  
let (uu___is_Fatal_CyclicDependence : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_CyclicDependence  -> true
    | uu____39597 -> false
  
let (uu___is_Error_InductiveAnnotNotAType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_InductiveAnnotNotAType  -> true
    | uu____39608 -> false
  
let (uu___is_Fatal_FriendInterface : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_FriendInterface  -> true
    | uu____39619 -> false
  
let (uu___is_Error_CannotRedefineConst : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_CannotRedefineConst  -> true
    | uu____39630 -> false
  
let (uu___is_Error_BadClassDecl : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_BadClassDecl  -> true | uu____39641 -> false
  
let (uu___is_Error_BadInductiveParam : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_BadInductiveParam  -> true
    | uu____39652 -> false
  
let (uu___is_Error_FieldShadow : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error_FieldShadow  -> true | uu____39663 -> false
  
let (uu___is_Error_UnexpectedDM4FType : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_UnexpectedDM4FType  -> true
    | uu____39674 -> false
  
let (uu___is_Fatal_EffectAbbreviationResultTypeMismatch :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EffectAbbreviationResultTypeMismatch  -> true
    | uu____39685 -> false
  
let (uu___is_Error_AlreadyCachedAssertionFailure : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_AlreadyCachedAssertionFailure  -> true
    | uu____39696 -> false
  
let (uu___is_Error_MustEraseMissing : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Error_MustEraseMissing  -> true
    | uu____39707 -> false
  
let (uu___is_Warning_EffectfulArgumentToErasedFunction :
  raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Warning_EffectfulArgumentToErasedFunction  -> true
    | uu____39718 -> false
  
let (uu___is_Fatal_EmptySurfaceLet : raw_error -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Fatal_EmptySurfaceLet  -> true
    | uu____39729 -> false
  
type flag = FStar_Options.error_flag
let (default_flags : (raw_error * FStar_Options.error_flag) Prims.list) =
  [(Error_DependencyAnalysisFailed, FStar_Options.CAlwaysError);
  (Error_IDETooManyPops, FStar_Options.CAlwaysError);
  (Error_IDEUnrecognized, FStar_Options.CAlwaysError);
  (Error_InductiveTypeNotSatisfyPositivityCondition,
    FStar_Options.CAlwaysError);
  (Error_InvalidUniverseVar, FStar_Options.CAlwaysError);
  (Error_MissingFileName, FStar_Options.CAlwaysError);
  (Error_ModuleFileNameMismatch, FStar_Options.CAlwaysError);
  (Error_OpPlusInUniverse, FStar_Options.CAlwaysError);
  (Error_OutOfRange, FStar_Options.CAlwaysError);
  (Error_ProofObligationFailed, FStar_Options.CError);
  (Error_TooManyFiles, FStar_Options.CAlwaysError);
  (Error_TypeCheckerFailToProve, FStar_Options.CAlwaysError);
  (Error_TypeError, FStar_Options.CAlwaysError);
  (Error_UncontrainedUnificationVar, FStar_Options.CAlwaysError);
  (Error_UnexpectedGTotComputation, FStar_Options.CAlwaysError);
  (Error_UnexpectedInstance, FStar_Options.CAlwaysError);
  (Error_UnknownFatal_AssertionFailure, FStar_Options.CError);
  (Error_Z3InvocationError, FStar_Options.CAlwaysError);
  (Error_IDEAssertionFailure, FStar_Options.CAlwaysError);
  (Error_Z3SolverError, FStar_Options.CError);
  (Fatal_AbstractTypeDeclarationInInterface, FStar_Options.CFatal);
  (Fatal_ActionMustHaveFunctionType, FStar_Options.CFatal);
  (Fatal_AlreadyDefinedTopLevelDeclaration, FStar_Options.CFatal);
  (Fatal_ArgumentLengthMismatch, FStar_Options.CFatal);
  (Fatal_AssertionFailure, FStar_Options.CFatal);
  (Fatal_AssignToImmutableValues, FStar_Options.CFatal);
  (Fatal_AssumeValInInterface, FStar_Options.CFatal);
  (Fatal_BadlyInstantiatedSynthByTactic, FStar_Options.CFatal);
  (Fatal_BadSignatureShape, FStar_Options.CFatal);
  (Fatal_BinderAndArgsLengthMismatch, FStar_Options.CFatal);
  (Fatal_BothValAndLetInInterface, FStar_Options.CFatal);
  (Fatal_CardinalityConstraintViolated, FStar_Options.CFatal);
  (Fatal_ComputationNotTotal, FStar_Options.CFatal);
  (Fatal_ComputationTypeNotAllowed, FStar_Options.CFatal);
  (Fatal_ComputedTypeNotMatchAnnotation, FStar_Options.CFatal);
  (Fatal_ConstructorArgLengthMismatch, FStar_Options.CFatal);
  (Fatal_ConstructorFailedCheck, FStar_Options.CFatal);
  (Fatal_ConstructorNotFound, FStar_Options.CFatal);
  (Fatal_ConstsructorBuildWrongType, FStar_Options.CFatal);
  (Fatal_CycleInRecTypeAbbreviation, FStar_Options.CFatal);
  (Fatal_DataContructorNotFound, FStar_Options.CFatal);
  (Fatal_DefaultQualifierNotAllowedOnEffects, FStar_Options.CFatal);
  (Fatal_DefinitionNotFound, FStar_Options.CFatal);
  (Fatal_DisjuctivePatternVarsMismatch, FStar_Options.CFatal);
  (Fatal_DivergentComputationCannotBeIncludedInTotal, FStar_Options.CFatal);
  (Fatal_DuplicateInImplementation, FStar_Options.CFatal);
  (Fatal_DuplicateModuleOrInterface, FStar_Options.CFatal);
  (Fatal_DuplicateTopLevelNames, FStar_Options.CFatal);
  (Fatal_DuplicateTypeAnnotationAndValDecl, FStar_Options.CFatal);
  (Fatal_EffectCannotBeReified, FStar_Options.CFatal);
  (Fatal_EffectConstructorNotFullyApplied, FStar_Options.CFatal);
  (Fatal_EffectfulAndPureComputationMismatch, FStar_Options.CFatal);
  (Fatal_EffectNotFound, FStar_Options.CFatal);
  (Fatal_EffectsCannotBeComposed, FStar_Options.CFatal);
  (Fatal_ErrorInSolveDeferredConstraints, FStar_Options.CFatal);
  (Fatal_ErrorsReported, FStar_Options.CFatal);
  (Fatal_EscapedBoundVar, FStar_Options.CFatal);
  (Fatal_ExpectedArrowAnnotatedType, FStar_Options.CFatal);
  (Fatal_ExpectedGhostExpression, FStar_Options.CFatal);
  (Fatal_ExpectedPureExpression, FStar_Options.CFatal);
  (Fatal_ExpectNormalizedEffect, FStar_Options.CFatal);
  (Fatal_ExpectTermGotFunction, FStar_Options.CFatal);
  (Fatal_ExpectTrivialPreCondition, FStar_Options.CFatal);
  (Fatal_FailToExtractNativeTactic, FStar_Options.CFatal);
  (Fatal_FailToCompileNativeTactic, FStar_Options.CFatal);
  (Fatal_FailToProcessPragma, FStar_Options.CFatal);
  (Fatal_FailToResolveImplicitArgument, FStar_Options.CFatal);
  (Fatal_FailToSolveUniverseInEquality, FStar_Options.CFatal);
  (Fatal_FieldsNotBelongToSameRecordType, FStar_Options.CFatal);
  (Fatal_ForbiddenReferenceToCurrentModule, FStar_Options.CFatal);
  (Fatal_FreeVariables, FStar_Options.CFatal);
  (Fatal_FunctionTypeExpected, FStar_Options.CFatal);
  (Fatal_IdentifierNotFound, FStar_Options.CFatal);
  (Fatal_IllAppliedConstant, FStar_Options.CFatal);
  (Fatal_IllegalCharInByteArray, FStar_Options.CFatal);
  (Fatal_IllegalCharInOperatorName, FStar_Options.CFatal);
  (Fatal_IllTyped, FStar_Options.CFatal);
  (Fatal_ImpossibleAbbrevLidBundle, FStar_Options.CFatal);
  (Fatal_ImpossibleAbbrevRenameBundle, FStar_Options.CFatal);
  (Fatal_ImpossibleInductiveWithAbbrev, FStar_Options.CFatal);
  (Fatal_ImpossiblePrePostAbs, FStar_Options.CFatal);
  (Fatal_ImpossiblePrePostArrow, FStar_Options.CFatal);
  (Fatal_ImpossibleToGenerateDMEffect, FStar_Options.CFatal);
  (Fatal_ImpossibleTypeAbbrevBundle, FStar_Options.CFatal);
  (Fatal_ImpossibleTypeAbbrevSigeltBundle, FStar_Options.CFatal);
  (Fatal_IncludeModuleNotPrepared, FStar_Options.CFatal);
  (Fatal_IncoherentInlineUniverse, FStar_Options.CFatal);
  (Fatal_IncompatibleKinds, FStar_Options.CFatal);
  (Fatal_IncompatibleNumberOfTypes, FStar_Options.CFatal);
  (Fatal_IncompatibleSetOfUniverse, FStar_Options.CFatal);
  (Fatal_IncompatibleUniverse, FStar_Options.CFatal);
  (Fatal_InconsistentImplicitArgumentAnnotation, FStar_Options.CFatal);
  (Fatal_InconsistentImplicitQualifier, FStar_Options.CFatal);
  (Fatal_InconsistentQualifierAnnotation, FStar_Options.CFatal);
  (Fatal_InferredTypeCauseVarEscape, FStar_Options.CFatal);
  (Fatal_InlineRenamedAsUnfold, FStar_Options.CFatal);
  (Fatal_InsufficientPatternArguments, FStar_Options.CFatal);
  (Fatal_InterfaceAlreadyProcessed, FStar_Options.CFatal);
  (Fatal_InterfaceNotImplementedByModule, FStar_Options.CFatal);
  (Fatal_InterfaceWithTypeImplementation, FStar_Options.CFatal);
  (Fatal_InvalidFloatingPointNumber, FStar_Options.CFatal);
  (Fatal_InvalidFSDocKeyword, FStar_Options.CFatal);
  (Fatal_InvalidIdentifier, FStar_Options.CFatal);
  (Fatal_InvalidLemmaArgument, FStar_Options.CFatal);
  (Fatal_InvalidNumericLiteral, FStar_Options.CFatal);
  (Fatal_InvalidRedefinitionOfLexT, FStar_Options.CFatal);
  (Fatal_InvalidUnicodeInStringLiteral, FStar_Options.CFatal);
  (Fatal_InvalidUTF8Encoding, FStar_Options.CFatal);
  (Fatal_InvalidWarnErrorSetting, FStar_Options.CFatal);
  (Fatal_LetBoundMonadicMismatch, FStar_Options.CFatal);
  (Fatal_LetMutableForVariablesOnly, FStar_Options.CFatal);
  (Fatal_LetOpenModuleOnly, FStar_Options.CFatal);
  (Fatal_LetRecArgumentMismatch, FStar_Options.CFatal);
  (Fatal_MalformedActionDeclaration, FStar_Options.CFatal);
  (Fatal_MismatchedPatternType, FStar_Options.CFatal);
  (Fatal_MismatchUniversePolymorphic, FStar_Options.CFatal);
  (Fatal_MissingDataConstructor, FStar_Options.CFatal);
  (Fatal_MissingExposeInterfacesOption, FStar_Options.CFatal);
  (Fatal_MissingFieldInRecord, FStar_Options.CFatal);
  (Fatal_MissingImplementation, FStar_Options.CFatal);
  (Fatal_MissingImplicitArguments, FStar_Options.CFatal);
  (Fatal_MissingInterface, FStar_Options.CFatal);
  (Fatal_MissingNameInBinder, FStar_Options.CFatal);
  (Fatal_MissingPrimsModule, FStar_Options.CFatal);
  (Fatal_MissingQuantifierBinder, FStar_Options.CFatal);
  (Fatal_ModuleExpected, FStar_Options.CFatal);
  (Fatal_ModuleFileNotFound, FStar_Options.CFatal);
  (Fatal_ModuleFirstStatement, FStar_Options.CFatal);
  (Fatal_ModuleNotFound, FStar_Options.CFatal);
  (Fatal_ModuleOrFileNotFound, FStar_Options.CFatal);
  (Fatal_MonadAlreadyDefined, FStar_Options.CFatal);
  (Fatal_MoreThanOneDeclaration, FStar_Options.CFatal);
  (Fatal_MultipleLetBinding, FStar_Options.CFatal);
  (Fatal_NameNotFound, FStar_Options.CFatal);
  (Fatal_NameSpaceNotFound, FStar_Options.CFatal);
  (Fatal_NegativeUniverseConstFatal_NotSupported, FStar_Options.CFatal);
  (Fatal_NoFileProvided, FStar_Options.CFatal);
  (Fatal_NonInductiveInMutuallyDefinedType, FStar_Options.CFatal);
  (Fatal_NonLinearPatternNotPermitted, FStar_Options.CFatal);
  (Fatal_NonLinearPatternVars, FStar_Options.CFatal);
  (Fatal_NonSingletonTopLevel, FStar_Options.CFatal);
  (Fatal_NonSingletonTopLevelModule, FStar_Options.CFatal);
  (Fatal_NonTopRecFunctionNotFullyEncoded, FStar_Options.CFatal);
  (Fatal_NonTrivialPreConditionInPrims, FStar_Options.CFatal);
  (Fatal_NonVariableInductiveTypeParameter, FStar_Options.CFatal);
  (Fatal_NotApplicationOrFv, FStar_Options.CFatal);
  (Fatal_NotEnoughArgsToEffect, FStar_Options.CFatal);
  (Fatal_NotEnoughArgumentsForEffect, FStar_Options.CFatal);
  (Fatal_NotFunctionType, FStar_Options.CFatal);
  (Fatal_NotSupported, FStar_Options.CFatal);
  (Fatal_NotTopLevelModule, FStar_Options.CFatal);
  (Fatal_NotValidFStarFile, FStar_Options.CFatal);
  (Fatal_NotValidIncludeDirectory, FStar_Options.CFatal);
  (Fatal_OneModulePerFile, FStar_Options.CFatal);
  (Fatal_OpenGoalsInSynthesis, FStar_Options.CFatal);
  (Fatal_OptionsNotCompatible, FStar_Options.CFatal);
  (Fatal_OutOfOrder, FStar_Options.CFatal);
  (Fatal_ParseErrors, FStar_Options.CFatal);
  (Fatal_ParseItError, FStar_Options.CFatal);
  (Fatal_PolyTypeExpected, FStar_Options.CFatal);
  (Fatal_PossibleInfiniteTyp, FStar_Options.CFatal);
  (Fatal_PreModuleMismatch, FStar_Options.CFatal);
  (Fatal_QulifierListNotPermitted, FStar_Options.CFatal);
  (Fatal_RecursiveFunctionLiteral, FStar_Options.CFatal);
  (Fatal_ReflectOnlySupportedOnEffects, FStar_Options.CFatal);
  (Fatal_ReservedPrefix, FStar_Options.CFatal);
  (Fatal_SMTOutputParseError, FStar_Options.CFatal);
  (Fatal_SMTSolverError, FStar_Options.CFatal);
  (Fatal_SyntaxError, FStar_Options.CFatal);
  (Fatal_SynthByTacticError, FStar_Options.CFatal);
  (Fatal_TacticGotStuck, FStar_Options.CFatal);
  (Fatal_TcOneFragmentFailed, FStar_Options.CFatal);
  (Fatal_TermOutsideOfDefLanguage, FStar_Options.CFatal);
  (Fatal_ToManyArgumentToFunction, FStar_Options.CFatal);
  (Fatal_TooManyOrTooFewFileMatch, FStar_Options.CFatal);
  (Fatal_TooManyPatternArguments, FStar_Options.CFatal);
  (Fatal_TooManyUniverse, FStar_Options.CFatal);
  (Fatal_TypeMismatch, FStar_Options.CFatal);
  (Fatal_TypeWithinPatternsAllowedOnVariablesOnly, FStar_Options.CFatal);
  (Fatal_UnableToReadFile, FStar_Options.CFatal);
  (Fatal_UnepxectedOrUnboundOperator, FStar_Options.CFatal);
  (Fatal_UnexpectedBinder, FStar_Options.CFatal);
  (Fatal_UnexpectedBindShape, FStar_Options.CFatal);
  (Fatal_UnexpectedChar, FStar_Options.CFatal);
  (Fatal_UnexpectedComputationTypeForLetRec, FStar_Options.CFatal);
  (Fatal_UnexpectedConstructorType, FStar_Options.CFatal);
  (Fatal_UnexpectedDataConstructor, FStar_Options.CFatal);
  (Fatal_UnexpectedEffect, FStar_Options.CFatal);
  (Fatal_UnexpectedEmptyRecord, FStar_Options.CFatal);
  (Fatal_UnexpectedExpressionType, FStar_Options.CFatal);
  (Fatal_UnexpectedFunctionParameterType, FStar_Options.CFatal);
  (Fatal_UnexpectedGeneralizedUniverse, FStar_Options.CFatal);
  (Fatal_UnexpectedGTotForLetRec, FStar_Options.CFatal);
  (Fatal_UnexpectedGuard, FStar_Options.CFatal);
  (Fatal_UnexpectedIdentifier, FStar_Options.CFatal);
  (Fatal_UnexpectedImplicitArgument, FStar_Options.CFatal);
  (Fatal_UnexpectedImplictArgument, FStar_Options.CFatal);
  (Fatal_UnexpectedInductivetype, FStar_Options.CFatal);
  (Fatal_UnexpectedLetBinding, FStar_Options.CFatal);
  (Fatal_UnexpectedModuleDeclaration, FStar_Options.CFatal);
  (Fatal_UnexpectedNumberOfUniverse, FStar_Options.CFatal);
  (Fatal_UnexpectedNumericLiteral, FStar_Options.CFatal);
  (Fatal_UnexpectedOperatorSymbol, FStar_Options.CFatal);
  (Fatal_UnexpectedPattern, FStar_Options.CFatal);
  (Fatal_UnexpectedPosition, FStar_Options.CFatal);
  (Fatal_UnExpectedPreCondition, FStar_Options.CFatal);
  (Fatal_UnexpectedReturnShape, FStar_Options.CFatal);
  (Fatal_UnexpectedSignatureForMonad, FStar_Options.CFatal);
  (Fatal_UnexpectedTerm, FStar_Options.CFatal);
  (Fatal_UnexpectedTermInUniverse, FStar_Options.CFatal);
  (Fatal_UnexpectedTermType, FStar_Options.CFatal);
  (Fatal_UnexpectedTermVQuote, FStar_Options.CFatal);
  (Fatal_UnexpectedUniversePolymorphicReturn, FStar_Options.CFatal);
  (Fatal_UnexpectedUniverseVariable, FStar_Options.CFatal);
  (Fatal_UnfoldableDeprecated, FStar_Options.CFatal);
  (Fatal_UnificationNotWellFormed, FStar_Options.CFatal);
  (Fatal_Uninstantiated, FStar_Options.CFatal);
  (Error_UninstantiatedUnificationVarInTactic, FStar_Options.CError);
  (Fatal_UninstantiatedVarInTactic, FStar_Options.CFatal);
  (Fatal_UniverseMightContainSumOfTwoUnivVars, FStar_Options.CFatal);
  (Fatal_UniversePolymorphicInnerLetBound, FStar_Options.CFatal);
  (Fatal_UnknownAttribute, FStar_Options.CFatal);
  (Fatal_UnknownToolForDep, FStar_Options.CFatal);
  (Fatal_UnrecognizedExtension, FStar_Options.CFatal);
  (Fatal_UnresolvedPatternVar, FStar_Options.CFatal);
  (Fatal_UnsupportedConstant, FStar_Options.CFatal);
  (Fatal_UnsupportedDisjuctivePatterns, FStar_Options.CFatal);
  (Fatal_UnsupportedQualifier, FStar_Options.CFatal);
  (Fatal_UserTacticFailure, FStar_Options.CFatal);
  (Fatal_ValueRestriction, FStar_Options.CFatal);
  (Fatal_VariableNotFound, FStar_Options.CFatal);
  (Fatal_WrongBodyTypeForReturnWP, FStar_Options.CFatal);
  (Fatal_WrongDataAppHeadFormat, FStar_Options.CFatal);
  (Fatal_WrongDefinitionOrder, FStar_Options.CFatal);
  (Fatal_WrongResultTypeAfterConstrutor, FStar_Options.CFatal);
  (Fatal_WrongTerm, FStar_Options.CFatal);
  (Fatal_WhenClauseNotSupported, FStar_Options.CFatal);
  (Unused01, FStar_Options.CFatal);
  (Warning_CallNotImplementedAsWarning, FStar_Options.CWarning);
  (Warning_AddImplicitAssumeNewQualifier, FStar_Options.CWarning);
  (Warning_AdmitWithoutDefinition, FStar_Options.CWarning);
  (Warning_CachedFile, FStar_Options.CWarning);
  (Warning_DefinitionNotTranslated, FStar_Options.CWarning);
  (Warning_DependencyFound, FStar_Options.CWarning);
  (Warning_DeprecatedEqualityOnBinder, FStar_Options.CWarning);
  (Warning_DeprecatedOpaqueQualifier, FStar_Options.CWarning);
  (Warning_DocOverwrite, FStar_Options.CWarning);
  (Warning_FileNotWritten, FStar_Options.CWarning);
  (Warning_Filtered, FStar_Options.CWarning);
  (Warning_FunctionLiteralPrecisionLoss, FStar_Options.CWarning);
  (Warning_FunctionNotExtacted, FStar_Options.CWarning);
  (Warning_HintFailedToReplayProof, FStar_Options.CWarning);
  (Warning_HitReplayFailed, FStar_Options.CWarning);
  (Warning_IDEIgnoreCodeGen, FStar_Options.CWarning);
  (Warning_IllFormedGoal, FStar_Options.CWarning);
  (Warning_InaccessibleArgument, FStar_Options.CWarning);
  (Warning_IncoherentImplicitQualifier, FStar_Options.CWarning);
  (Warning_IrrelevantQualifierOnArgumentToReflect, FStar_Options.CWarning);
  (Warning_IrrelevantQualifierOnArgumentToReify, FStar_Options.CWarning);
  (Warning_MalformedWarnErrorList, FStar_Options.CWarning);
  (Warning_MetaAlienNotATmUnknown, FStar_Options.CWarning);
  (Warning_MultipleAscriptions, FStar_Options.CWarning);
  (Warning_NondependentUserDefinedDataType, FStar_Options.CWarning);
  (Warning_NonListLiteralSMTPattern, FStar_Options.CWarning);
  (Warning_NormalizationFailure, FStar_Options.CWarning);
  (Warning_NotDependentArrow, FStar_Options.CWarning);
  (Warning_NotEmbedded, FStar_Options.CWarning);
  (Warning_PatternMissingBoundVar, FStar_Options.CWarning);
  (Warning_RecursiveDependency, FStar_Options.CWarning);
  (Warning_RedundantExplicitCurrying, FStar_Options.CWarning);
  (Warning_SMTPatTDeprecated, FStar_Options.CWarning);
  (Warning_SMTPatternIllFormed, FStar_Options.CWarning);
  (Warning_TopLevelEffect, FStar_Options.CWarning);
  (Warning_UnboundModuleReference, FStar_Options.CWarning);
  (Warning_UnexpectedFile, FStar_Options.CWarning);
  (Warning_UnexpectedFsTypApp, FStar_Options.CWarning);
  (Warning_UnexpectedZ3Output, FStar_Options.CError);
  (Warning_UnprotectedTerm, FStar_Options.CWarning);
  (Warning_UnrecognizedAttribute, FStar_Options.CWarning);
  (Warning_UpperBoundCandidateAlreadyVisited, FStar_Options.CWarning);
  (Warning_UseDefaultEffect, FStar_Options.CWarning);
  (Warning_WrongErrorLocation, FStar_Options.CWarning);
  (Warning_Z3InvocationWarning, FStar_Options.CWarning);
  (Warning_MissingInterfaceOrImplementation, FStar_Options.CWarning);
  (Warning_ConstructorBuildsUnexpectedType, FStar_Options.CWarning);
  (Warning_ModuleOrFileNotFoundWarning, FStar_Options.CWarning);
  (Error_NoLetMutable, FStar_Options.CAlwaysError);
  (Error_BadImplicit, FStar_Options.CAlwaysError);
  (Warning_DeprecatedDefinition, FStar_Options.CWarning);
  (Fatal_SMTEncodingArityMismatch, FStar_Options.CFatal);
  (Warning_Defensive, FStar_Options.CWarning);
  (Warning_CantInspect, FStar_Options.CWarning);
  (Warning_NilGivenExplicitArgs, FStar_Options.CWarning);
  (Warning_ConsAppliedExplicitArgs, FStar_Options.CWarning);
  (Warning_UnembedBinderKnot, FStar_Options.CWarning);
  (Fatal_TacticProofRelevantGoal, FStar_Options.CFatal);
  (Warning_TacAdmit, FStar_Options.CWarning);
  (Fatal_IncoherentPatterns, FStar_Options.CFatal);
  (Error_NoSMTButNeeded, FStar_Options.CAlwaysError);
  (Fatal_UnexpectedAntiquotation, FStar_Options.CFatal);
  (Fatal_SplicedUndef, FStar_Options.CFatal);
  (Fatal_SpliceUnembedFail, FStar_Options.CFatal);
  (Warning_ExtractionUnexpectedEffect, FStar_Options.CWarning);
  (Error_DidNotFail, FStar_Options.CAlwaysError);
  (Warning_UnappliedFail, FStar_Options.CWarning);
  (Warning_QuantifierWithoutPattern, FStar_Options.CSilent);
  (Error_EmptyFailErrs, FStar_Options.CAlwaysError);
  (Warning_logicqualifier, FStar_Options.CWarning);
  (Fatal_CyclicDependence, FStar_Options.CFatal);
  (Error_InductiveAnnotNotAType, FStar_Options.CError);
  (Fatal_FriendInterface, FStar_Options.CFatal);
  (Error_CannotRedefineConst, FStar_Options.CError);
  (Error_BadClassDecl, FStar_Options.CError);
  (Error_BadInductiveParam, FStar_Options.CFatal);
  (Error_FieldShadow, FStar_Options.CFatal);
  (Error_UnexpectedDM4FType, FStar_Options.CFatal);
  (Fatal_EffectAbbreviationResultTypeMismatch, FStar_Options.CFatal);
  (Error_AlreadyCachedAssertionFailure, FStar_Options.CFatal);
  (Error_MustEraseMissing, FStar_Options.CWarning);
  (Warning_EffectfulArgumentToErasedFunction, FStar_Options.CWarning);
  (Fatal_EmptySurfaceLet, FStar_Options.CFatal)] 
exception Err of (raw_error * Prims.string) 
let (uu___is_Err : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Err uu____41043 -> true | uu____41050 -> false
  
let (__proj__Err__item__uu___ : Prims.exn -> (raw_error * Prims.string)) =
  fun projectee  -> match projectee with | Err uu____41069 -> uu____41069 
exception Error of (raw_error * Prims.string * FStar_Range.range) 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Error uu____41094 -> true | uu____41103 -> false
  
let (__proj__Error__item__uu___ :
  Prims.exn -> (raw_error * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Error uu____41126 -> uu____41126 
exception Warning of (raw_error * Prims.string * FStar_Range.range) 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Warning uu____41153 -> true | uu____41162 -> false
  
let (__proj__Warning__item__uu___ :
  Prims.exn -> (raw_error * Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Warning uu____41185 -> uu____41185 
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Stop  -> true | uu____41202 -> false
  
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Empty_frag  -> true | uu____41213 -> false
  
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | ENotImplemented  -> true | uu____41224 -> false
  
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | EInfo  -> true | uu____41235 -> false
  
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | EWarning  -> true | uu____41246 -> false
  
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | EError  -> true | uu____41257 -> false
  
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
    let uu____41552 =
      match issue.issue_range with
      | FStar_Pervasives_Native.None  -> ("", "")
      | FStar_Pervasives_Native.Some r when r = FStar_Range.dummyRange ->
          ("", "")
      | FStar_Pervasives_Native.Some r ->
          let uu____41575 =
            let uu____41577 = FStar_Range.string_of_use_range r  in
            FStar_Util.format1 "%s: " uu____41577  in
          let uu____41580 =
            let uu____41582 =
              let uu____41584 = FStar_Range.use_range r  in
              let uu____41585 = FStar_Range.def_range r  in
              uu____41584 = uu____41585  in
            if uu____41582
            then ""
            else
              (let uu____41591 = FStar_Range.string_of_range r  in
               FStar_Util.format1 " (see also %s)" uu____41591)
             in
          (uu____41575, uu____41580)
       in
    match uu____41552 with
    | (range_str,see_also_str) ->
        let issue_number =
          match issue.issue_number with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some n1 ->
              let uu____41611 = FStar_Util.string_of_int n1  in
              FStar_Util.format1 " %s" uu____41611
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
    let uu____41631 = format_issue issue  in printer uu____41631
  
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1  ->
    fun i2  ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          (Prims.parse_int "0")
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some
         uu____41655) -> ~- (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some
         uu____41661,FStar_Pervasives_Native.None ) -> (Prims.parse_int "1")
      | (FStar_Pervasives_Native.Some r1,FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
  
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print7  ->
    let errs = FStar_Util.mk_ref []  in
    let add_one e =
      match e.issue_level with
      | EError  ->
          let uu____41694 =
            let uu____41697 = FStar_ST.op_Bang errs  in e :: uu____41697  in
          FStar_ST.op_Colon_Equals errs uu____41694
      | uu____41790 -> print_issue e  in
    let count_errors uu____41796 =
      let uu____41797 = FStar_ST.op_Bang errs  in
      FStar_List.length uu____41797  in
    let report uu____41852 =
      let sorted1 =
        let uu____41856 = FStar_ST.op_Bang errs  in
        FStar_List.sortWith compare_issues uu____41856  in
      if print7 then FStar_List.iter print_issue sorted1 else (); sorted1  in
    let clear1 uu____41913 = FStar_ST.op_Colon_Equals errs []  in
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
  fun uu____42018  ->
    let uu____42019 =
      let uu____42025 = FStar_ST.op_Bang current_handler  in
      uu____42025.eh_count_errors  in
    uu____42019 ()
  
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h  ->
    fun issue  ->
      h.eh_add_one issue;
      if issue.issue_level <> EInfo
      then
        ((let uu____42059 =
            let uu____42061 = FStar_ST.op_Bang FStar_Options.abort_counter
               in
            uu____42061 - (Prims.parse_int "1")  in
          FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____42059);
         (let uu____42106 =
            let uu____42108 = FStar_ST.op_Bang FStar_Options.abort_counter
               in
            uu____42108 = (Prims.parse_int "0")  in
          if uu____42106 then failwith "Aborting due to --abort_on" else ()))
      else ()
  
let (add_one : issue -> unit) =
  fun issue  ->
    FStar_Util.atomically
      (fun uu____42147  ->
         let uu____42148 = FStar_ST.op_Bang current_handler  in
         wrapped_eh_add_one uu____42148 issue)
  
let (add_many : issue Prims.list -> unit) =
  fun issues  ->
    FStar_Util.atomically
      (fun uu____42180  ->
         let uu____42181 =
           let uu____42186 = FStar_ST.op_Bang current_handler  in
           wrapped_eh_add_one uu____42186  in
         FStar_List.iter uu____42181 issues)
  
let (report_all : unit -> issue Prims.list) =
  fun uu____42213  ->
    let uu____42214 =
      let uu____42221 = FStar_ST.op_Bang current_handler  in
      uu____42221.eh_report  in
    uu____42214 ()
  
let (clear : unit -> unit) =
  fun uu____42246  ->
    let uu____42247 =
      let uu____42252 = FStar_ST.op_Bang current_handler  in
      uu____42252.eh_clear  in
    uu____42247 ()
  
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
  let clear_prefix uu____42497 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None  in
  let append_prefix s =
    let uu____42555 = FStar_ST.op_Bang pfx  in
    match uu____42555 with
    | FStar_Pervasives_Native.None  -> s
    | FStar_Pervasives_Native.Some p ->
        let uu____42611 = FStar_String.op_Hat ": " s  in
        FStar_String.op_Hat p uu____42611
     in
  { set_prefix; append_prefix; clear_prefix } 
let findIndex :
  'Auu____42623 'Auu____42624 .
    ('Auu____42623 * 'Auu____42624) Prims.list -> 'Auu____42623 -> Prims.int
  =
  fun l  ->
    fun v1  ->
      FStar_All.pipe_right l
        (FStar_List.index
           (fun uu___289_42662  ->
              match uu___289_42662 with
              | (e,uu____42669) when e = v1 -> true
              | uu____42671 -> false))
  
let (errno_of_error : raw_error -> Prims.int) =
  fun e  -> findIndex default_flags e 
let (init_warn_error_flags : FStar_Options.error_flag Prims.list) =
  FStar_List.map FStar_Pervasives_Native.snd default_flags 
let (diag : FStar_Range.range -> Prims.string -> unit) =
  fun r  ->
    fun msg  ->
      let uu____42704 = FStar_Options.debug_any ()  in
      if uu____42704
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None)
      else ()
  
let (defensive_errno : Prims.int) = errno_of_error Warning_Defensive 
let (lookup :
  FStar_Options.error_flag Prims.list ->
    Prims.int -> FStar_Options.error_flag)
  =
  fun flags  ->
    fun errno  ->
      let uu____42729 =
        (errno = defensive_errno) && (FStar_Options.defensive_fail ())  in
      if uu____42729
      then FStar_Options.CAlwaysError
      else FStar_List.nth flags errno
  
let (log_issue : FStar_Range.range -> (raw_error * Prims.string) -> unit) =
  fun r  ->
    fun uu____42750  ->
      match uu____42750 with
      | (e,msg) ->
          let errno = errno_of_error e  in
          let uu____42762 =
            let uu____42763 = FStar_Options.error_flags ()  in
            lookup uu____42763 errno  in
          (match uu____42762 with
           | FStar_Options.CAlwaysError  ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | FStar_Options.CError  ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | FStar_Options.CWarning  ->
               add_one
                 (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | FStar_Options.CSilent  -> ()
           | FStar_Options.CFatal  ->
               let i =
                 mk_issue EError (FStar_Pervasives_Native.Some r) msg
                   (FStar_Pervasives_Native.Some errno)
                  in
               let uu____42771 = FStar_Options.ide ()  in
               if uu____42771
               then add_one i
               else
                 (let uu____42776 =
                    let uu____42778 = format_issue i  in
                    FStar_String.op_Hat
                      "don't use log_issue to report fatal error, should use raise_error: "
                      uu____42778
                     in
                  failwith uu____42776))
  
let (add_errors :
  (raw_error * Prims.string * FStar_Range.range) Prims.list -> unit) =
  fun errs  ->
    FStar_Util.atomically
      (fun uu____42806  ->
         FStar_List.iter
           (fun uu____42819  ->
              match uu____42819 with
              | (e,msg,r) ->
                  let uu____42832 =
                    let uu____42838 = message_prefix.append_prefix msg  in
                    (e, uu____42838)  in
                  log_issue r uu____42832) errs)
  
let (issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option) =
  fun uu___290_42848  ->
    match uu___290_42848 with
    | Error (e,msg,r) ->
        let errno = errno_of_error e  in
        let uu____42858 =
          let uu____42859 = message_prefix.append_prefix msg  in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____42859
            (FStar_Pervasives_Native.Some errno)
           in
        FStar_Pervasives_Native.Some uu____42858
    | FStar_Util.NYI msg ->
        let uu____42864 =
          let uu____42865 = message_prefix.append_prefix msg  in
          mk_issue ENotImplemented FStar_Pervasives_Native.None uu____42865
            FStar_Pervasives_Native.None
           in
        FStar_Pervasives_Native.Some uu____42864
    | Err (e,msg) ->
        let errno = errno_of_error e  in
        let uu____42874 =
          let uu____42875 = message_prefix.append_prefix msg  in
          mk_issue EError FStar_Pervasives_Native.None uu____42875
            (FStar_Pervasives_Native.Some errno)
           in
        FStar_Pervasives_Native.Some uu____42874
    | uu____42878 -> FStar_Pervasives_Native.None
  
let (err_exn : Prims.exn -> unit) =
  fun exn  ->
    if exn = Stop
    then ()
    else
      (let uu____42888 = issue_of_exn exn  in
       match uu____42888 with
       | FStar_Pervasives_Native.Some issue -> add_one issue
       | FStar_Pervasives_Native.None  -> FStar_Exn.raise exn)
  
let (handleable : Prims.exn -> Prims.bool) =
  fun uu___291_42898  ->
    match uu___291_42898 with
    | Error uu____42900 -> true
    | FStar_Util.NYI uu____42909 -> true
    | Stop  -> true
    | Err uu____42913 -> true
    | uu____42920 -> false
  
let (stop_if_err : unit -> unit) =
  fun uu____42927  ->
    let uu____42928 =
      let uu____42930 = get_err_count ()  in
      uu____42930 > (Prims.parse_int "0")  in
    if uu____42928 then FStar_Exn.raise Stop else ()
  
let raise_error :
  'Auu____42943 .
    (raw_error * Prims.string) -> FStar_Range.range -> 'Auu____42943
  =
  fun uu____42957  ->
    fun r  ->
      match uu____42957 with | (e,msg) -> FStar_Exn.raise (Error (e, msg, r))
  
let raise_err : 'Auu____42974 . (raw_error * Prims.string) -> 'Auu____42974 =
  fun uu____42984  ->
    match uu____42984 with | (e,msg) -> FStar_Exn.raise (Err (e, msg))
  
let (update_flags :
  (FStar_Options.error_flag * Prims.string) Prims.list ->
    FStar_Options.error_flag Prims.list)
  =
  fun l  ->
    let flags = init_warn_error_flags  in
    let compare1 uu____43052 uu____43053 =
      match (uu____43052, uu____43053) with
      | ((uu____43095,(a,uu____43097)),(uu____43098,(b,uu____43100))) ->
          if a > b
          then (Prims.parse_int "1")
          else
            if a < b then ~- (Prims.parse_int "1") else (Prims.parse_int "0")
       in
    let set_one_flag f d =
      match (f, d) with
      | (FStar_Options.CWarning ,FStar_Options.CAlwaysError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot turn an error into warning")
      | (FStar_Options.CError ,FStar_Options.CAlwaysError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot turn an error into warning")
      | (FStar_Options.CSilent ,FStar_Options.CAlwaysError ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting, "cannot silence an error")
      | (uu____43169,FStar_Options.CFatal ) ->
          raise_err
            (Fatal_InvalidWarnErrorSetting,
              "cannot reset the error level of a fatal error")
      | uu____43172 -> f  in
    let rec set_flag i l1 =
      let d = FStar_List.nth flags i  in
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
          let uu____43330 =
            let uu____43333 =
              let uu____43336 = set_flag i sorted1  in [uu____43336]  in
            FStar_List.append f uu____43333  in
          aux uu____43330 (i + (Prims.parse_int "1")) tl1 sorted1
       in
    let rec compute_range result l1 =
      match l1 with
      | [] -> result
      | (f,s)::tl1 ->
          let r = FStar_Util.split s ".."  in
          let uu____43438 =
            match r with
            | r1::r2::[] ->
                let uu____43458 = FStar_Util.int_of_string r1  in
                let uu____43460 = FStar_Util.int_of_string r2  in
                (uu____43458, uu____43460)
            | uu____43464 ->
                let uu____43468 =
                  let uu____43474 =
                    FStar_Util.format1 "Malformed warn-error range %s" s  in
                  (Fatal_InvalidWarnErrorSetting, uu____43474)  in
                raise_err uu____43468
             in
          (match uu____43438 with
           | (l2,h) ->
               (if
                  (l2 < (Prims.parse_int "0")) ||
                    (h >= (FStar_List.length default_flags))
                then
                  (let uu____43509 =
                     let uu____43515 =
                       let uu____43517 = FStar_Util.string_of_int l2  in
                       let uu____43519 = FStar_Util.string_of_int h  in
                       FStar_Util.format2 "No error for warn_error %s..%s"
                         uu____43517 uu____43519
                        in
                     (Fatal_InvalidWarnErrorSetting, uu____43515)  in
                   raise_err uu____43509)
                else ();
                compute_range (FStar_List.append result [(f, (l2, h))]) tl1))
       in
    let range = compute_range [] l  in
    let sorted1 = FStar_List.sortWith compare1 range  in
    aux [] (Prims.parse_int "0") init_warn_error_flags sorted1
  
let catch_errors :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f  ->
    let newh = mk_default_handler false  in
    let old = FStar_ST.op_Bang current_handler  in
    FStar_ST.op_Colon_Equals current_handler newh;
    (let r =
       try
         (fun uu___568_43683  ->
            match () with
            | () -> let r = f ()  in FStar_Pervasives_Native.Some r) ()
       with
       | uu___567_43689 ->
           (err_exn uu___567_43689; FStar_Pervasives_Native.None)
        in
     let errs = newh.eh_report ()  in
     FStar_ST.op_Colon_Equals current_handler old; (errs, r))
  