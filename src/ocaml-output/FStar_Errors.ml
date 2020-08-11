open Prims
exception Invalid_warn_error_setting of Prims.string 
let (uu___is_Invalid_warn_error_setting : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Invalid_warn_error_setting uu____21 -> true
    | uu____22 -> false
let (__proj__Invalid_warn_error_setting__item__uu___ :
  Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Invalid_warn_error_setting uu____28 -> uu____28
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CFatal -> true | uu____34 -> false
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CAlwaysError -> true | uu____40 -> false
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CError -> true | uu____46 -> false
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CWarning -> true | uu____52 -> false
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CSilent -> true | uu____58 -> false
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
  | Error_NonTopRecFunctionNotFullyEncoded 
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
  | Warning_PluginNotImplemented 
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
  | Warning_UnexpectedCheckedFile 
  | Fatal_ExtractionUnsupported 
  | Warning_SMTErrorReason 
  | Warning_CoercionNotFound 
  | Error_QuakeFailed 
  | Error_IllSMTPat 
  | Error_IllScopedTerm 
  | Warning_UnusedLetRec 
  | Fatal_Effects_Ordering_Coherence 
  | Warning_BleedingEdge_Feature 
  | Warning_IgnoredBinding 
  | Warning_CouldNotReadHints 
  | Fatal_BadUvar 
  | Warning_WarnOnUse 
  | Warning_DeprecatedAttributeSyntax 
  | Warning_DeprecatedGeneric 
let (uu___is_Error_DependencyAnalysisFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_DependencyAnalysisFailed -> true
    | uu____64 -> false
let (uu___is_Error_IDETooManyPops : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IDETooManyPops -> true | uu____70 -> false
let (uu___is_Error_IDEUnrecognized : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IDEUnrecognized -> true | uu____76 -> false
let (uu___is_Error_InductiveTypeNotSatisfyPositivityCondition :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InductiveTypeNotSatisfyPositivityCondition -> true
    | uu____82 -> false
let (uu___is_Error_InvalidUniverseVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InvalidUniverseVar -> true
    | uu____88 -> false
let (uu___is_Error_MissingFileName : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_MissingFileName -> true | uu____94 -> false
let (uu___is_Error_ModuleFileNameMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_ModuleFileNameMismatch -> true
    | uu____100 -> false
let (uu___is_Error_OpPlusInUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_OpPlusInUniverse -> true
    | uu____106 -> false
let (uu___is_Error_OutOfRange : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_OutOfRange -> true | uu____112 -> false
let (uu___is_Error_ProofObligationFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_ProofObligationFailed -> true
    | uu____118 -> false
let (uu___is_Error_TooManyFiles : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_TooManyFiles -> true | uu____124 -> false
let (uu___is_Error_TypeCheckerFailToProve : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_TypeCheckerFailToProve -> true
    | uu____130 -> false
let (uu___is_Error_TypeError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_TypeError -> true | uu____136 -> false
let (uu___is_Error_UncontrainedUnificationVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UncontrainedUnificationVar -> true
    | uu____142 -> false
let (uu___is_Error_UnexpectedGTotComputation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedGTotComputation -> true
    | uu____148 -> false
let (uu___is_Error_UnexpectedInstance : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedInstance -> true
    | uu____154 -> false
let (uu___is_Error_UnknownFatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnknownFatal_AssertionFailure -> true
    | uu____160 -> false
let (uu___is_Error_Z3InvocationError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_Z3InvocationError -> true
    | uu____166 -> false
let (uu___is_Error_IDEAssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_IDEAssertionFailure -> true
    | uu____172 -> false
let (uu___is_Error_Z3SolverError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_Z3SolverError -> true | uu____178 -> false
let (uu___is_Fatal_AbstractTypeDeclarationInInterface :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AbstractTypeDeclarationInInterface -> true
    | uu____184 -> false
let (uu___is_Fatal_ActionMustHaveFunctionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ActionMustHaveFunctionType -> true
    | uu____190 -> false
let (uu___is_Fatal_AlreadyDefinedTopLevelDeclaration :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AlreadyDefinedTopLevelDeclaration -> true
    | uu____196 -> false
let (uu___is_Fatal_ArgumentLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ArgumentLengthMismatch -> true
    | uu____202 -> false
let (uu___is_Fatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssertionFailure -> true
    | uu____208 -> false
let (uu___is_Fatal_AssignToImmutableValues : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssignToImmutableValues -> true
    | uu____214 -> false
let (uu___is_Fatal_AssumeValInInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssumeValInInterface -> true
    | uu____220 -> false
let (uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_BadlyInstantiatedSynthByTactic -> true
    | uu____226 -> false
let (uu___is_Fatal_BadSignatureShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BadSignatureShape -> true
    | uu____232 -> false
let (uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BinderAndArgsLengthMismatch -> true
    | uu____238 -> false
let (uu___is_Fatal_BothValAndLetInInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BothValAndLetInInterface -> true
    | uu____244 -> false
let (uu___is_Fatal_CardinalityConstraintViolated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CardinalityConstraintViolated -> true
    | uu____250 -> false
let (uu___is_Fatal_ComputationNotTotal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ComputationNotTotal -> true
    | uu____256 -> false
let (uu___is_Fatal_ComputationTypeNotAllowed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ComputationTypeNotAllowed -> true
    | uu____262 -> false
let (uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_ComputedTypeNotMatchAnnotation -> true
    | uu____268 -> false
let (uu___is_Fatal_ConstructorArgLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorArgLengthMismatch -> true
    | uu____274 -> false
let (uu___is_Fatal_ConstructorFailedCheck : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorFailedCheck -> true
    | uu____280 -> false
let (uu___is_Fatal_ConstructorNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorNotFound -> true
    | uu____286 -> false
let (uu___is_Fatal_ConstsructorBuildWrongType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstsructorBuildWrongType -> true
    | uu____292 -> false
let (uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CycleInRecTypeAbbreviation -> true
    | uu____298 -> false
let (uu___is_Fatal_DataContructorNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DataContructorNotFound -> true
    | uu____304 -> false
let (uu___is_Fatal_DefaultQualifierNotAllowedOnEffects :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DefaultQualifierNotAllowedOnEffects -> true
    | uu____310 -> false
let (uu___is_Fatal_DefinitionNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DefinitionNotFound -> true
    | uu____316 -> false
let (uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DisjuctivePatternVarsMismatch -> true
    | uu____322 -> false
let (uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DivergentComputationCannotBeIncludedInTotal -> true
    | uu____328 -> false
let (uu___is_Fatal_DuplicateInImplementation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateInImplementation -> true
    | uu____334 -> false
let (uu___is_Fatal_DuplicateModuleOrInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateModuleOrInterface -> true
    | uu____340 -> false
let (uu___is_Fatal_DuplicateTopLevelNames : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateTopLevelNames -> true
    | uu____346 -> false
let (uu___is_Fatal_DuplicateTypeAnnotationAndValDecl :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateTypeAnnotationAndValDecl -> true
    | uu____352 -> false
let (uu___is_Fatal_EffectCannotBeReified : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectCannotBeReified -> true
    | uu____358 -> false
let (uu___is_Fatal_EffectConstructorNotFullyApplied :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectConstructorNotFullyApplied -> true
    | uu____364 -> false
let (uu___is_Fatal_EffectfulAndPureComputationMismatch :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectfulAndPureComputationMismatch -> true
    | uu____370 -> false
let (uu___is_Fatal_EffectNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_EffectNotFound -> true | uu____376 -> false
let (uu___is_Fatal_EffectsCannotBeComposed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectsCannotBeComposed -> true
    | uu____382 -> false
let (uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_ErrorInSolveDeferredConstraints -> true
    | uu____388 -> false
let (uu___is_Fatal_ErrorsReported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ErrorsReported -> true | uu____394 -> false
let (uu___is_Fatal_EscapedBoundVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_EscapedBoundVar -> true | uu____400 -> false
let (uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedArrowAnnotatedType -> true
    | uu____406 -> false
let (uu___is_Fatal_ExpectedGhostExpression : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedGhostExpression -> true
    | uu____412 -> false
let (uu___is_Fatal_ExpectedPureExpression : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedPureExpression -> true
    | uu____418 -> false
let (uu___is_Fatal_ExpectNormalizedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectNormalizedEffect -> true
    | uu____424 -> false
let (uu___is_Fatal_ExpectTermGotFunction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectTermGotFunction -> true
    | uu____430 -> false
let (uu___is_Fatal_ExpectTrivialPreCondition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectTrivialPreCondition -> true
    | uu____436 -> false
let (uu___is_Fatal_FailToCompileNativeTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToCompileNativeTactic -> true
    | uu____442 -> false
let (uu___is_Fatal_FailToExtractNativeTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToExtractNativeTactic -> true
    | uu____448 -> false
let (uu___is_Fatal_FailToProcessPragma : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToProcessPragma -> true
    | uu____454 -> false
let (uu___is_Fatal_FailToResolveImplicitArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToResolveImplicitArgument -> true
    | uu____460 -> false
let (uu___is_Fatal_FailToSolveUniverseInEquality : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToSolveUniverseInEquality -> true
    | uu____466 -> false
let (uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_FieldsNotBelongToSameRecordType -> true
    | uu____472 -> false
let (uu___is_Fatal_ForbiddenReferenceToCurrentModule :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ForbiddenReferenceToCurrentModule -> true
    | uu____478 -> false
let (uu___is_Fatal_FreeVariables : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_FreeVariables -> true | uu____484 -> false
let (uu___is_Fatal_FunctionTypeExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FunctionTypeExpected -> true
    | uu____490 -> false
let (uu___is_Fatal_IdentifierNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IdentifierNotFound -> true
    | uu____496 -> false
let (uu___is_Fatal_IllAppliedConstant : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllAppliedConstant -> true
    | uu____502 -> false
let (uu___is_Fatal_IllegalCharInByteArray : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllegalCharInByteArray -> true
    | uu____508 -> false
let (uu___is_Fatal_IllegalCharInOperatorName : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllegalCharInOperatorName -> true
    | uu____514 -> false
let (uu___is_Fatal_IllTyped : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_IllTyped -> true | uu____520 -> false
let (uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleAbbrevLidBundle -> true
    | uu____526 -> false
let (uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleAbbrevRenameBundle -> true
    | uu____532 -> false
let (uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleInductiveWithAbbrev -> true
    | uu____538 -> false
let (uu___is_Fatal_ImpossiblePrePostAbs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossiblePrePostAbs -> true
    | uu____544 -> false
let (uu___is_Fatal_ImpossiblePrePostArrow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossiblePrePostArrow -> true
    | uu____550 -> false
let (uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleToGenerateDMEffect -> true
    | uu____556 -> false
let (uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevBundle -> true
    | uu____562 -> false
let (uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevSigeltBundle -> true
    | uu____568 -> false
let (uu___is_Fatal_IncludeModuleNotPrepared : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncludeModuleNotPrepared -> true
    | uu____574 -> false
let (uu___is_Fatal_IncoherentInlineUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncoherentInlineUniverse -> true
    | uu____580 -> false
let (uu___is_Fatal_IncompatibleKinds : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleKinds -> true
    | uu____586 -> false
let (uu___is_Fatal_IncompatibleNumberOfTypes : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleNumberOfTypes -> true
    | uu____592 -> false
let (uu___is_Fatal_IncompatibleSetOfUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleSetOfUniverse -> true
    | uu____598 -> false
let (uu___is_Fatal_IncompatibleUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleUniverse -> true
    | uu____604 -> false
let (uu___is_Fatal_InconsistentImplicitArgumentAnnotation :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentImplicitArgumentAnnotation -> true
    | uu____610 -> false
let (uu___is_Fatal_InconsistentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentImplicitQualifier -> true
    | uu____616 -> false
let (uu___is_Fatal_InconsistentQualifierAnnotation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentQualifierAnnotation -> true
    | uu____622 -> false
let (uu___is_Fatal_InferredTypeCauseVarEscape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InferredTypeCauseVarEscape -> true
    | uu____628 -> false
let (uu___is_Fatal_InlineRenamedAsUnfold : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InlineRenamedAsUnfold -> true
    | uu____634 -> false
let (uu___is_Fatal_InsufficientPatternArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InsufficientPatternArguments -> true
    | uu____640 -> false
let (uu___is_Fatal_InterfaceAlreadyProcessed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceAlreadyProcessed -> true
    | uu____646 -> false
let (uu___is_Fatal_InterfaceNotImplementedByModule : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceNotImplementedByModule -> true
    | uu____652 -> false
let (uu___is_Fatal_InterfaceWithTypeImplementation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceWithTypeImplementation -> true
    | uu____658 -> false
let (uu___is_Fatal_InvalidFloatingPointNumber : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidFloatingPointNumber -> true
    | uu____664 -> false
let (uu___is_Fatal_InvalidFSDocKeyword : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidFSDocKeyword -> true
    | uu____670 -> false
let (uu___is_Fatal_InvalidIdentifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidIdentifier -> true
    | uu____676 -> false
let (uu___is_Fatal_InvalidLemmaArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidLemmaArgument -> true
    | uu____682 -> false
let (uu___is_Fatal_InvalidNumericLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidNumericLiteral -> true
    | uu____688 -> false
let (uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidRedefinitionOfLexT -> true
    | uu____694 -> false
let (uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidUnicodeInStringLiteral -> true
    | uu____700 -> false
let (uu___is_Fatal_InvalidUTF8Encoding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidUTF8Encoding -> true
    | uu____706 -> false
let (uu___is_Fatal_InvalidWarnErrorSetting : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidWarnErrorSetting -> true
    | uu____712 -> false
let (uu___is_Fatal_LetBoundMonadicMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetBoundMonadicMismatch -> true
    | uu____718 -> false
let (uu___is_Fatal_LetMutableForVariablesOnly : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetMutableForVariablesOnly -> true
    | uu____724 -> false
let (uu___is_Fatal_LetOpenModuleOnly : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetOpenModuleOnly -> true
    | uu____730 -> false
let (uu___is_Fatal_LetRecArgumentMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetRecArgumentMismatch -> true
    | uu____736 -> false
let (uu___is_Fatal_MalformedActionDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MalformedActionDeclaration -> true
    | uu____742 -> false
let (uu___is_Fatal_MismatchedPatternType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MismatchedPatternType -> true
    | uu____748 -> false
let (uu___is_Fatal_MismatchUniversePolymorphic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MismatchUniversePolymorphic -> true
    | uu____754 -> false
let (uu___is_Fatal_MissingDataConstructor : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingDataConstructor -> true
    | uu____760 -> false
let (uu___is_Fatal_MissingExposeInterfacesOption : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingExposeInterfacesOption -> true
    | uu____766 -> false
let (uu___is_Fatal_MissingFieldInRecord : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingFieldInRecord -> true
    | uu____772 -> false
let (uu___is_Fatal_MissingImplementation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingImplementation -> true
    | uu____778 -> false
let (uu___is_Fatal_MissingImplicitArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingImplicitArguments -> true
    | uu____784 -> false
let (uu___is_Fatal_MissingInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingInterface -> true
    | uu____790 -> false
let (uu___is_Fatal_MissingNameInBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingNameInBinder -> true
    | uu____796 -> false
let (uu___is_Fatal_MissingPrimsModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingPrimsModule -> true
    | uu____802 -> false
let (uu___is_Fatal_MissingQuantifierBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingQuantifierBinder -> true
    | uu____808 -> false
let (uu___is_Fatal_ModuleExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ModuleExpected -> true | uu____814 -> false
let (uu___is_Fatal_ModuleFileNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleFileNotFound -> true
    | uu____820 -> false
let (uu___is_Fatal_ModuleFirstStatement : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleFirstStatement -> true
    | uu____826 -> false
let (uu___is_Fatal_ModuleNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ModuleNotFound -> true | uu____832 -> false
let (uu___is_Fatal_ModuleOrFileNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleOrFileNotFound -> true
    | uu____838 -> false
let (uu___is_Fatal_MonadAlreadyDefined : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MonadAlreadyDefined -> true
    | uu____844 -> false
let (uu___is_Fatal_MoreThanOneDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MoreThanOneDeclaration -> true
    | uu____850 -> false
let (uu___is_Fatal_MultipleLetBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MultipleLetBinding -> true
    | uu____856 -> false
let (uu___is_Fatal_NameNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NameNotFound -> true | uu____862 -> false
let (uu___is_Fatal_NameSpaceNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NameSpaceNotFound -> true
    | uu____868 -> false
let (uu___is_Fatal_NegativeUniverseConstFatal_NotSupported :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NegativeUniverseConstFatal_NotSupported -> true
    | uu____874 -> false
let (uu___is_Fatal_NoFileProvided : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NoFileProvided -> true | uu____880 -> false
let (uu___is_Fatal_NonInductiveInMutuallyDefinedType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonInductiveInMutuallyDefinedType -> true
    | uu____886 -> false
let (uu___is_Fatal_NonLinearPatternNotPermitted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonLinearPatternNotPermitted -> true
    | uu____892 -> false
let (uu___is_Fatal_NonLinearPatternVars : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonLinearPatternVars -> true
    | uu____898 -> false
let (uu___is_Fatal_NonSingletonTopLevel : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonSingletonTopLevel -> true
    | uu____904 -> false
let (uu___is_Fatal_NonSingletonTopLevelModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonSingletonTopLevelModule -> true
    | uu____910 -> false
let (uu___is_Error_NonTopRecFunctionNotFullyEncoded :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_NonTopRecFunctionNotFullyEncoded -> true
    | uu____916 -> false
let (uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonTrivialPreConditionInPrims -> true
    | uu____922 -> false
let (uu___is_Fatal_NonVariableInductiveTypeParameter :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonVariableInductiveTypeParameter -> true
    | uu____928 -> false
let (uu___is_Fatal_NotApplicationOrFv : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotApplicationOrFv -> true
    | uu____934 -> false
let (uu___is_Fatal_NotEnoughArgsToEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotEnoughArgsToEffect -> true
    | uu____940 -> false
let (uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotEnoughArgumentsForEffect -> true
    | uu____946 -> false
let (uu___is_Fatal_NotFunctionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NotFunctionType -> true | uu____952 -> false
let (uu___is_Fatal_NotSupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NotSupported -> true | uu____958 -> false
let (uu___is_Fatal_NotTopLevelModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotTopLevelModule -> true
    | uu____964 -> false
let (uu___is_Fatal_NotValidFStarFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotValidFStarFile -> true
    | uu____970 -> false
let (uu___is_Fatal_NotValidIncludeDirectory : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotValidIncludeDirectory -> true
    | uu____976 -> false
let (uu___is_Fatal_OneModulePerFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OneModulePerFile -> true
    | uu____982 -> false
let (uu___is_Fatal_OpenGoalsInSynthesis : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OpenGoalsInSynthesis -> true
    | uu____988 -> false
let (uu___is_Fatal_OptionsNotCompatible : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OptionsNotCompatible -> true
    | uu____994 -> false
let (uu___is_Fatal_OutOfOrder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_OutOfOrder -> true | uu____1000 -> false
let (uu___is_Fatal_ParseErrors : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ParseErrors -> true | uu____1006 -> false
let (uu___is_Fatal_ParseItError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ParseItError -> true | uu____1012 -> false
let (uu___is_Fatal_PolyTypeExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PolyTypeExpected -> true
    | uu____1018 -> false
let (uu___is_Fatal_PossibleInfiniteTyp : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PossibleInfiniteTyp -> true
    | uu____1024 -> false
let (uu___is_Fatal_PreModuleMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PreModuleMismatch -> true
    | uu____1030 -> false
let (uu___is_Fatal_QulifierListNotPermitted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_QulifierListNotPermitted -> true
    | uu____1036 -> false
let (uu___is_Fatal_RecursiveFunctionLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_RecursiveFunctionLiteral -> true
    | uu____1042 -> false
let (uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ReflectOnlySupportedOnEffects -> true
    | uu____1048 -> false
let (uu___is_Fatal_ReservedPrefix : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ReservedPrefix -> true | uu____1054 -> false
let (uu___is_Fatal_SMTOutputParseError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SMTOutputParseError -> true
    | uu____1060 -> false
let (uu___is_Fatal_SMTSolverError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SMTSolverError -> true | uu____1066 -> false
let (uu___is_Fatal_SyntaxError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SyntaxError -> true | uu____1072 -> false
let (uu___is_Fatal_SynthByTacticError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SynthByTacticError -> true
    | uu____1078 -> false
let (uu___is_Fatal_TacticGotStuck : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_TacticGotStuck -> true | uu____1084 -> false
let (uu___is_Fatal_TcOneFragmentFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TcOneFragmentFailed -> true
    | uu____1090 -> false
let (uu___is_Fatal_TermOutsideOfDefLanguage : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TermOutsideOfDefLanguage -> true
    | uu____1096 -> false
let (uu___is_Fatal_ToManyArgumentToFunction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ToManyArgumentToFunction -> true
    | uu____1102 -> false
let (uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyOrTooFewFileMatch -> true
    | uu____1108 -> false
let (uu___is_Fatal_TooManyPatternArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyPatternArguments -> true
    | uu____1114 -> false
let (uu___is_Fatal_TooManyUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyUniverse -> true
    | uu____1120 -> false
let (uu___is_Fatal_TypeMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_TypeMismatch -> true | uu____1126 -> false
let (uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TypeWithinPatternsAllowedOnVariablesOnly -> true
    | uu____1132 -> false
let (uu___is_Fatal_UnableToReadFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnableToReadFile -> true
    | uu____1138 -> false
let (uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnepxectedOrUnboundOperator -> true
    | uu____1144 -> false
let (uu___is_Fatal_UnexpectedBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedBinder -> true
    | uu____1150 -> false
let (uu___is_Fatal_UnexpectedBindShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedBindShape -> true
    | uu____1156 -> false
let (uu___is_Fatal_UnexpectedChar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_UnexpectedChar -> true | uu____1162 -> false
let (uu___is_Fatal_UnexpectedComputationTypeForLetRec :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedComputationTypeForLetRec -> true
    | uu____1168 -> false
let (uu___is_Fatal_UnexpectedConstructorType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedConstructorType -> true
    | uu____1174 -> false
let (uu___is_Fatal_UnexpectedDataConstructor : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedDataConstructor -> true
    | uu____1180 -> false
let (uu___is_Fatal_UnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedEffect -> true
    | uu____1186 -> false
let (uu___is_Fatal_UnexpectedEmptyRecord : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedEmptyRecord -> true
    | uu____1192 -> false
let (uu___is_Fatal_UnexpectedExpressionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedExpressionType -> true
    | uu____1198 -> false
let (uu___is_Fatal_UnexpectedFunctionParameterType : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedFunctionParameterType -> true
    | uu____1204 -> false
let (uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGeneralizedUniverse -> true
    | uu____1210 -> false
let (uu___is_Fatal_UnexpectedGTotForLetRec : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGTotForLetRec -> true
    | uu____1216 -> false
let (uu___is_Fatal_UnexpectedGuard : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGuard -> true
    | uu____1222 -> false
let (uu___is_Fatal_UnexpectedIdentifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedIdentifier -> true
    | uu____1228 -> false
let (uu___is_Fatal_UnexpectedImplicitArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedImplicitArgument -> true
    | uu____1234 -> false
let (uu___is_Fatal_UnexpectedImplictArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedImplictArgument -> true
    | uu____1240 -> false
let (uu___is_Fatal_UnexpectedInductivetype : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedInductivetype -> true
    | uu____1246 -> false
let (uu___is_Fatal_UnexpectedLetBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedLetBinding -> true
    | uu____1252 -> false
let (uu___is_Fatal_UnexpectedModuleDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedModuleDeclaration -> true
    | uu____1258 -> false
let (uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedNumberOfUniverse -> true
    | uu____1264 -> false
let (uu___is_Fatal_UnexpectedNumericLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedNumericLiteral -> true
    | uu____1270 -> false
let (uu___is_Fatal_UnexpectedOperatorSymbol : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedOperatorSymbol -> true
    | uu____1276 -> false
let (uu___is_Fatal_UnexpectedPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedPattern -> true
    | uu____1282 -> false
let (uu___is_Fatal_UnexpectedPosition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedPosition -> true
    | uu____1288 -> false
let (uu___is_Fatal_UnExpectedPreCondition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnExpectedPreCondition -> true
    | uu____1294 -> false
let (uu___is_Fatal_UnexpectedReturnShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedReturnShape -> true
    | uu____1300 -> false
let (uu___is_Fatal_UnexpectedSignatureForMonad : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedSignatureForMonad -> true
    | uu____1306 -> false
let (uu___is_Fatal_UnexpectedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_UnexpectedTerm -> true | uu____1312 -> false
let (uu___is_Fatal_UnexpectedTermInUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermInUniverse -> true
    | uu____1318 -> false
let (uu___is_Fatal_UnexpectedTermType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermType -> true
    | uu____1324 -> false
let (uu___is_Fatal_UnexpectedTermVQuote : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermVQuote -> true
    | uu____1330 -> false
let (uu___is_Fatal_UnexpectedUniversePolymorphicReturn :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedUniversePolymorphicReturn -> true
    | uu____1336 -> false
let (uu___is_Fatal_UnexpectedUniverseVariable : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedUniverseVariable -> true
    | uu____1342 -> false
let (uu___is_Fatal_UnfoldableDeprecated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnfoldableDeprecated -> true
    | uu____1348 -> false
let (uu___is_Fatal_UnificationNotWellFormed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnificationNotWellFormed -> true
    | uu____1354 -> false
let (uu___is_Fatal_Uninstantiated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_Uninstantiated -> true | uu____1360 -> false
let (uu___is_Error_UninstantiatedUnificationVarInTactic :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UninstantiatedUnificationVarInTactic -> true
    | uu____1366 -> false
let (uu___is_Fatal_UninstantiatedVarInTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UninstantiatedVarInTactic -> true
    | uu____1372 -> false
let (uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UniverseMightContainSumOfTwoUnivVars -> true
    | uu____1378 -> false
let (uu___is_Fatal_UniversePolymorphicInnerLetBound :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UniversePolymorphicInnerLetBound -> true
    | uu____1384 -> false
let (uu___is_Fatal_UnknownAttribute : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnknownAttribute -> true
    | uu____1390 -> false
let (uu___is_Fatal_UnknownToolForDep : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnknownToolForDep -> true
    | uu____1396 -> false
let (uu___is_Fatal_UnrecognizedExtension : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnrecognizedExtension -> true
    | uu____1402 -> false
let (uu___is_Fatal_UnresolvedPatternVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnresolvedPatternVar -> true
    | uu____1408 -> false
let (uu___is_Fatal_UnsupportedConstant : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedConstant -> true
    | uu____1414 -> false
let (uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedDisjuctivePatterns -> true
    | uu____1420 -> false
let (uu___is_Fatal_UnsupportedQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedQualifier -> true
    | uu____1426 -> false
let (uu___is_Fatal_UserTacticFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UserTacticFailure -> true
    | uu____1432 -> false
let (uu___is_Fatal_ValueRestriction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ValueRestriction -> true
    | uu____1438 -> false
let (uu___is_Fatal_VariableNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_VariableNotFound -> true
    | uu____1444 -> false
let (uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongBodyTypeForReturnWP -> true
    | uu____1450 -> false
let (uu___is_Fatal_WrongDataAppHeadFormat : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongDataAppHeadFormat -> true
    | uu____1456 -> false
let (uu___is_Fatal_WrongDefinitionOrder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongDefinitionOrder -> true
    | uu____1462 -> false
let (uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_WrongResultTypeAfterConstrutor -> true
    | uu____1468 -> false
let (uu___is_Fatal_WrongTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_WrongTerm -> true | uu____1474 -> false
let (uu___is_Fatal_WhenClauseNotSupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WhenClauseNotSupported -> true
    | uu____1480 -> false
let (uu___is_Unused01 : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Unused01 -> true | uu____1486 -> false
let (uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Warning_AddImplicitAssumeNewQualifier -> true
    | uu____1492 -> false
let (uu___is_Warning_AdmitWithoutDefinition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_AdmitWithoutDefinition -> true
    | uu____1498 -> false
let (uu___is_Warning_CachedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_CachedFile -> true | uu____1504 -> false
let (uu___is_Warning_DefinitionNotTranslated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DefinitionNotTranslated -> true
    | uu____1510 -> false
let (uu___is_Warning_DependencyFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DependencyFound -> true
    | uu____1516 -> false
let (uu___is_Warning_DeprecatedEqualityOnBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedEqualityOnBinder -> true
    | uu____1522 -> false
let (uu___is_Warning_DeprecatedOpaqueQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedOpaqueQualifier -> true
    | uu____1528 -> false
let (uu___is_Warning_DocOverwrite : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_DocOverwrite -> true | uu____1534 -> false
let (uu___is_Warning_FileNotWritten : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_FileNotWritten -> true
    | uu____1540 -> false
let (uu___is_Warning_Filtered : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_Filtered -> true | uu____1546 -> false
let (uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Warning_FunctionLiteralPrecisionLoss -> true
    | uu____1552 -> false
let (uu___is_Warning_FunctionNotExtacted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_FunctionNotExtacted -> true
    | uu____1558 -> false
let (uu___is_Warning_HintFailedToReplayProof : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_HintFailedToReplayProof -> true
    | uu____1564 -> false
let (uu___is_Warning_HitReplayFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_HitReplayFailed -> true
    | uu____1570 -> false
let (uu___is_Warning_IDEIgnoreCodeGen : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IDEIgnoreCodeGen -> true
    | uu____1576 -> false
let (uu___is_Warning_IllFormedGoal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IllFormedGoal -> true
    | uu____1582 -> false
let (uu___is_Warning_InaccessibleArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_InaccessibleArgument -> true
    | uu____1588 -> false
let (uu___is_Warning_IncoherentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IncoherentImplicitQualifier -> true
    | uu____1594 -> false
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReflect :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReflect -> true
    | uu____1600 -> false
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReify :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReify -> true
    | uu____1606 -> false
let (uu___is_Warning_MalformedWarnErrorList : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MalformedWarnErrorList -> true
    | uu____1612 -> false
let (uu___is_Warning_MetaAlienNotATmUnknown : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MetaAlienNotATmUnknown -> true
    | uu____1618 -> false
let (uu___is_Warning_MultipleAscriptions : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MultipleAscriptions -> true
    | uu____1624 -> false
let (uu___is_Warning_NondependentUserDefinedDataType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NondependentUserDefinedDataType -> true
    | uu____1630 -> false
let (uu___is_Warning_NonListLiteralSMTPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NonListLiteralSMTPattern -> true
    | uu____1636 -> false
let (uu___is_Warning_NormalizationFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NormalizationFailure -> true
    | uu____1642 -> false
let (uu___is_Warning_NotDependentArrow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NotDependentArrow -> true
    | uu____1648 -> false
let (uu___is_Warning_NotEmbedded : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_NotEmbedded -> true | uu____1654 -> false
let (uu___is_Warning_PatternMissingBoundVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_PatternMissingBoundVar -> true
    | uu____1660 -> false
let (uu___is_Warning_RecursiveDependency : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_RecursiveDependency -> true
    | uu____1666 -> false
let (uu___is_Warning_RedundantExplicitCurrying : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_RedundantExplicitCurrying -> true
    | uu____1672 -> false
let (uu___is_Warning_SMTPatTDeprecated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTPatTDeprecated -> true
    | uu____1678 -> false
let (uu___is_Warning_SMTPatternIllFormed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTPatternIllFormed -> true
    | uu____1684 -> false
let (uu___is_Warning_TopLevelEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_TopLevelEffect -> true
    | uu____1690 -> false
let (uu___is_Warning_UnboundModuleReference : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnboundModuleReference -> true
    | uu____1696 -> false
let (uu___is_Warning_UnexpectedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedFile -> true
    | uu____1702 -> false
let (uu___is_Warning_UnexpectedFsTypApp : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedFsTypApp -> true
    | uu____1708 -> false
let (uu___is_Warning_UnexpectedZ3Output : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedZ3Output -> true
    | uu____1714 -> false
let (uu___is_Warning_UnprotectedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnprotectedTerm -> true
    | uu____1720 -> false
let (uu___is_Warning_UnrecognizedAttribute : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnrecognizedAttribute -> true
    | uu____1726 -> false
let (uu___is_Warning_UpperBoundCandidateAlreadyVisited :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UpperBoundCandidateAlreadyVisited -> true
    | uu____1732 -> false
let (uu___is_Warning_UseDefaultEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UseDefaultEffect -> true
    | uu____1738 -> false
let (uu___is_Warning_WrongErrorLocation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_WrongErrorLocation -> true
    | uu____1744 -> false
let (uu___is_Warning_Z3InvocationWarning : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_Z3InvocationWarning -> true
    | uu____1750 -> false
let (uu___is_Warning_PluginNotImplemented : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_PluginNotImplemented -> true
    | uu____1756 -> false
let (uu___is_Warning_MissingInterfaceOrImplementation :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MissingInterfaceOrImplementation -> true
    | uu____1762 -> false
let (uu___is_Warning_ConstructorBuildsUnexpectedType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ConstructorBuildsUnexpectedType -> true
    | uu____1768 -> false
let (uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ModuleOrFileNotFoundWarning -> true
    | uu____1774 -> false
let (uu___is_Error_NoLetMutable : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_NoLetMutable -> true | uu____1780 -> false
let (uu___is_Error_BadImplicit : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadImplicit -> true | uu____1786 -> false
let (uu___is_Warning_DeprecatedDefinition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedDefinition -> true
    | uu____1792 -> false
let (uu___is_Fatal_SMTEncodingArityMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SMTEncodingArityMismatch -> true
    | uu____1798 -> false
let (uu___is_Warning_Defensive : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_Defensive -> true | uu____1804 -> false
let (uu___is_Warning_CantInspect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_CantInspect -> true | uu____1810 -> false
let (uu___is_Warning_NilGivenExplicitArgs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NilGivenExplicitArgs -> true
    | uu____1816 -> false
let (uu___is_Warning_ConsAppliedExplicitArgs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ConsAppliedExplicitArgs -> true
    | uu____1822 -> false
let (uu___is_Warning_UnembedBinderKnot : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnembedBinderKnot -> true
    | uu____1828 -> false
let (uu___is_Fatal_TacticProofRelevantGoal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TacticProofRelevantGoal -> true
    | uu____1834 -> false
let (uu___is_Warning_TacAdmit : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_TacAdmit -> true | uu____1840 -> false
let (uu___is_Fatal_IncoherentPatterns : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncoherentPatterns -> true
    | uu____1846 -> false
let (uu___is_Error_NoSMTButNeeded : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_NoSMTButNeeded -> true | uu____1852 -> false
let (uu___is_Fatal_UnexpectedAntiquotation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedAntiquotation -> true
    | uu____1858 -> false
let (uu___is_Fatal_SplicedUndef : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SplicedUndef -> true | uu____1864 -> false
let (uu___is_Fatal_SpliceUnembedFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SpliceUnembedFail -> true
    | uu____1870 -> false
let (uu___is_Warning_ExtractionUnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ExtractionUnexpectedEffect -> true
    | uu____1876 -> false
let (uu___is_Error_DidNotFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_DidNotFail -> true | uu____1882 -> false
let (uu___is_Warning_UnappliedFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnappliedFail -> true
    | uu____1888 -> false
let (uu___is_Warning_QuantifierWithoutPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_QuantifierWithoutPattern -> true
    | uu____1894 -> false
let (uu___is_Error_EmptyFailErrs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_EmptyFailErrs -> true | uu____1900 -> false
let (uu___is_Warning_logicqualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_logicqualifier -> true
    | uu____1906 -> false
let (uu___is_Fatal_CyclicDependence : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CyclicDependence -> true
    | uu____1912 -> false
let (uu___is_Error_InductiveAnnotNotAType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InductiveAnnotNotAType -> true
    | uu____1918 -> false
let (uu___is_Fatal_FriendInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FriendInterface -> true
    | uu____1924 -> false
let (uu___is_Error_CannotRedefineConst : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_CannotRedefineConst -> true
    | uu____1930 -> false
let (uu___is_Error_BadClassDecl : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadClassDecl -> true | uu____1936 -> false
let (uu___is_Error_BadInductiveParam : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_BadInductiveParam -> true
    | uu____1942 -> false
let (uu___is_Error_FieldShadow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_FieldShadow -> true | uu____1948 -> false
let (uu___is_Error_UnexpectedDM4FType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedDM4FType -> true
    | uu____1954 -> false
let (uu___is_Fatal_EffectAbbreviationResultTypeMismatch :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectAbbreviationResultTypeMismatch -> true
    | uu____1960 -> false
let (uu___is_Error_AlreadyCachedAssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_AlreadyCachedAssertionFailure -> true
    | uu____1966 -> false
let (uu___is_Error_MustEraseMissing : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_MustEraseMissing -> true
    | uu____1972 -> false
let (uu___is_Warning_EffectfulArgumentToErasedFunction :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_EffectfulArgumentToErasedFunction -> true
    | uu____1978 -> false
let (uu___is_Fatal_EmptySurfaceLet : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EmptySurfaceLet -> true
    | uu____1984 -> false
let (uu___is_Warning_UnexpectedCheckedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedCheckedFile -> true
    | uu____1990 -> false
let (uu___is_Fatal_ExtractionUnsupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExtractionUnsupported -> true
    | uu____1996 -> false
let (uu___is_Warning_SMTErrorReason : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTErrorReason -> true
    | uu____2002 -> false
let (uu___is_Warning_CoercionNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_CoercionNotFound -> true
    | uu____2008 -> false
let (uu___is_Error_QuakeFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_QuakeFailed -> true | uu____2014 -> false
let (uu___is_Error_IllSMTPat : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IllSMTPat -> true | uu____2020 -> false
let (uu___is_Error_IllScopedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IllScopedTerm -> true | uu____2026 -> false
let (uu___is_Warning_UnusedLetRec : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_UnusedLetRec -> true | uu____2032 -> false
let (uu___is_Fatal_Effects_Ordering_Coherence : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_Effects_Ordering_Coherence -> true
    | uu____2038 -> false
let (uu___is_Warning_BleedingEdge_Feature : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_BleedingEdge_Feature -> true
    | uu____2044 -> false
let (uu___is_Warning_IgnoredBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IgnoredBinding -> true
    | uu____2050 -> false
let (uu___is_Warning_CouldNotReadHints : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_CouldNotReadHints -> true
    | uu____2056 -> false
let (uu___is_Fatal_BadUvar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_BadUvar -> true | uu____2062 -> false
let (uu___is_Warning_WarnOnUse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_WarnOnUse -> true | uu____2068 -> false
let (uu___is_Warning_DeprecatedAttributeSyntax : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedAttributeSyntax -> true
    | uu____2074 -> false
let (uu___is_Warning_DeprecatedGeneric : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedGeneric -> true
    | uu____2080 -> false
type flag = error_flag
type error_setting = (raw_error * error_flag * Prims.int)
let (default_settings : error_setting Prims.list) =
  [(Error_DependencyAnalysisFailed, CAlwaysError, Prims.int_zero);
  (Error_IDETooManyPops, CAlwaysError, Prims.int_one);
  (Error_IDEUnrecognized, CAlwaysError, (Prims.of_int (2)));
  (Error_InductiveTypeNotSatisfyPositivityCondition, CAlwaysError,
    (Prims.of_int (3)));
  (Error_InvalidUniverseVar, CAlwaysError, (Prims.of_int (4)));
  (Error_MissingFileName, CAlwaysError, (Prims.of_int (5)));
  (Error_ModuleFileNameMismatch, CAlwaysError, (Prims.of_int (6)));
  (Error_OpPlusInUniverse, CAlwaysError, (Prims.of_int (7)));
  (Error_OutOfRange, CAlwaysError, (Prims.of_int (8)));
  (Error_ProofObligationFailed, CError, (Prims.of_int (9)));
  (Error_TooManyFiles, CAlwaysError, (Prims.of_int (10)));
  (Error_TypeCheckerFailToProve, CAlwaysError, (Prims.of_int (11)));
  (Error_TypeError, CAlwaysError, (Prims.of_int (12)));
  (Error_UncontrainedUnificationVar, CAlwaysError, (Prims.of_int (13)));
  (Error_UnexpectedGTotComputation, CAlwaysError, (Prims.of_int (14)));
  (Error_UnexpectedInstance, CAlwaysError, (Prims.of_int (15)));
  (Error_UnknownFatal_AssertionFailure, CError, (Prims.of_int (16)));
  (Error_Z3InvocationError, CAlwaysError, (Prims.of_int (17)));
  (Error_IDEAssertionFailure, CAlwaysError, (Prims.of_int (18)));
  (Error_Z3SolverError, CError, (Prims.of_int (19)));
  (Fatal_AbstractTypeDeclarationInInterface, CFatal, (Prims.of_int (20)));
  (Fatal_ActionMustHaveFunctionType, CFatal, (Prims.of_int (21)));
  (Fatal_AlreadyDefinedTopLevelDeclaration, CFatal, (Prims.of_int (22)));
  (Fatal_ArgumentLengthMismatch, CFatal, (Prims.of_int (23)));
  (Fatal_AssertionFailure, CFatal, (Prims.of_int (24)));
  (Fatal_AssignToImmutableValues, CFatal, (Prims.of_int (25)));
  (Fatal_AssumeValInInterface, CFatal, (Prims.of_int (26)));
  (Fatal_BadlyInstantiatedSynthByTactic, CFatal, (Prims.of_int (27)));
  (Fatal_BadSignatureShape, CFatal, (Prims.of_int (28)));
  (Fatal_BinderAndArgsLengthMismatch, CFatal, (Prims.of_int (29)));
  (Fatal_BothValAndLetInInterface, CFatal, (Prims.of_int (30)));
  (Fatal_CardinalityConstraintViolated, CFatal, (Prims.of_int (31)));
  (Fatal_ComputationNotTotal, CFatal, (Prims.of_int (32)));
  (Fatal_ComputationTypeNotAllowed, CFatal, (Prims.of_int (33)));
  (Fatal_ComputedTypeNotMatchAnnotation, CFatal, (Prims.of_int (34)));
  (Fatal_ConstructorArgLengthMismatch, CFatal, (Prims.of_int (35)));
  (Fatal_ConstructorFailedCheck, CFatal, (Prims.of_int (36)));
  (Fatal_ConstructorNotFound, CFatal, (Prims.of_int (37)));
  (Fatal_ConstsructorBuildWrongType, CFatal, (Prims.of_int (38)));
  (Fatal_CycleInRecTypeAbbreviation, CFatal, (Prims.of_int (39)));
  (Fatal_DataContructorNotFound, CFatal, (Prims.of_int (40)));
  (Fatal_DefaultQualifierNotAllowedOnEffects, CFatal, (Prims.of_int (41)));
  (Fatal_DefinitionNotFound, CFatal, (Prims.of_int (42)));
  (Fatal_DisjuctivePatternVarsMismatch, CFatal, (Prims.of_int (43)));
  (Fatal_DivergentComputationCannotBeIncludedInTotal, CFatal,
    (Prims.of_int (44)));
  (Fatal_DuplicateInImplementation, CFatal, (Prims.of_int (45)));
  (Fatal_DuplicateModuleOrInterface, CFatal, (Prims.of_int (46)));
  (Fatal_DuplicateTopLevelNames, CFatal, (Prims.of_int (47)));
  (Fatal_DuplicateTypeAnnotationAndValDecl, CFatal, (Prims.of_int (48)));
  (Fatal_EffectCannotBeReified, CFatal, (Prims.of_int (49)));
  (Fatal_EffectConstructorNotFullyApplied, CFatal, (Prims.of_int (50)));
  (Fatal_EffectfulAndPureComputationMismatch, CFatal, (Prims.of_int (51)));
  (Fatal_EffectNotFound, CFatal, (Prims.of_int (52)));
  (Fatal_EffectsCannotBeComposed, CFatal, (Prims.of_int (53)));
  (Fatal_ErrorInSolveDeferredConstraints, CFatal, (Prims.of_int (54)));
  (Fatal_ErrorsReported, CFatal, (Prims.of_int (55)));
  (Fatal_EscapedBoundVar, CFatal, (Prims.of_int (56)));
  (Fatal_ExpectedArrowAnnotatedType, CFatal, (Prims.of_int (57)));
  (Fatal_ExpectedGhostExpression, CFatal, (Prims.of_int (58)));
  (Fatal_ExpectedPureExpression, CFatal, (Prims.of_int (59)));
  (Fatal_ExpectNormalizedEffect, CFatal, (Prims.of_int (60)));
  (Fatal_ExpectTermGotFunction, CFatal, (Prims.of_int (61)));
  (Fatal_ExpectTrivialPreCondition, CFatal, (Prims.of_int (62)));
  (Fatal_FailToExtractNativeTactic, CFatal, (Prims.of_int (63)));
  (Fatal_FailToCompileNativeTactic, CFatal, (Prims.of_int (64)));
  (Fatal_FailToProcessPragma, CFatal, (Prims.of_int (65)));
  (Fatal_FailToResolveImplicitArgument, CFatal, (Prims.of_int (66)));
  (Fatal_FailToSolveUniverseInEquality, CFatal, (Prims.of_int (67)));
  (Fatal_FieldsNotBelongToSameRecordType, CFatal, (Prims.of_int (68)));
  (Fatal_ForbiddenReferenceToCurrentModule, CFatal, (Prims.of_int (69)));
  (Fatal_FreeVariables, CFatal, (Prims.of_int (70)));
  (Fatal_FunctionTypeExpected, CFatal, (Prims.of_int (71)));
  (Fatal_IdentifierNotFound, CFatal, (Prims.of_int (72)));
  (Fatal_IllAppliedConstant, CFatal, (Prims.of_int (73)));
  (Fatal_IllegalCharInByteArray, CFatal, (Prims.of_int (74)));
  (Fatal_IllegalCharInOperatorName, CFatal, (Prims.of_int (75)));
  (Fatal_IllTyped, CFatal, (Prims.of_int (76)));
  (Fatal_ImpossibleAbbrevLidBundle, CFatal, (Prims.of_int (77)));
  (Fatal_ImpossibleAbbrevRenameBundle, CFatal, (Prims.of_int (78)));
  (Fatal_ImpossibleInductiveWithAbbrev, CFatal, (Prims.of_int (79)));
  (Fatal_ImpossiblePrePostAbs, CFatal, (Prims.of_int (80)));
  (Fatal_ImpossiblePrePostArrow, CFatal, (Prims.of_int (81)));
  (Fatal_ImpossibleToGenerateDMEffect, CFatal, (Prims.of_int (82)));
  (Fatal_ImpossibleTypeAbbrevBundle, CFatal, (Prims.of_int (83)));
  (Fatal_ImpossibleTypeAbbrevSigeltBundle, CFatal, (Prims.of_int (84)));
  (Fatal_IncludeModuleNotPrepared, CFatal, (Prims.of_int (85)));
  (Fatal_IncoherentInlineUniverse, CFatal, (Prims.of_int (86)));
  (Fatal_IncompatibleKinds, CFatal, (Prims.of_int (87)));
  (Fatal_IncompatibleNumberOfTypes, CFatal, (Prims.of_int (88)));
  (Fatal_IncompatibleSetOfUniverse, CFatal, (Prims.of_int (89)));
  (Fatal_IncompatibleUniverse, CFatal, (Prims.of_int (90)));
  (Fatal_InconsistentImplicitArgumentAnnotation, CFatal, (Prims.of_int (91)));
  (Fatal_InconsistentImplicitQualifier, CFatal, (Prims.of_int (92)));
  (Fatal_InconsistentQualifierAnnotation, CFatal, (Prims.of_int (93)));
  (Fatal_InferredTypeCauseVarEscape, CFatal, (Prims.of_int (94)));
  (Fatal_InlineRenamedAsUnfold, CFatal, (Prims.of_int (95)));
  (Fatal_InsufficientPatternArguments, CFatal, (Prims.of_int (96)));
  (Fatal_InterfaceAlreadyProcessed, CFatal, (Prims.of_int (97)));
  (Fatal_InterfaceNotImplementedByModule, CFatal, (Prims.of_int (98)));
  (Fatal_InterfaceWithTypeImplementation, CFatal, (Prims.of_int (99)));
  (Fatal_InvalidFloatingPointNumber, CFatal, (Prims.of_int (100)));
  (Fatal_InvalidFSDocKeyword, CFatal, (Prims.of_int (101)));
  (Fatal_InvalidIdentifier, CFatal, (Prims.of_int (102)));
  (Fatal_InvalidLemmaArgument, CFatal, (Prims.of_int (103)));
  (Fatal_InvalidNumericLiteral, CFatal, (Prims.of_int (104)));
  (Fatal_InvalidRedefinitionOfLexT, CFatal, (Prims.of_int (105)));
  (Fatal_InvalidUnicodeInStringLiteral, CFatal, (Prims.of_int (106)));
  (Fatal_InvalidUTF8Encoding, CFatal, (Prims.of_int (107)));
  (Fatal_InvalidWarnErrorSetting, CFatal, (Prims.of_int (108)));
  (Fatal_LetBoundMonadicMismatch, CFatal, (Prims.of_int (109)));
  (Fatal_LetMutableForVariablesOnly, CFatal, (Prims.of_int (110)));
  (Fatal_LetOpenModuleOnly, CFatal, (Prims.of_int (111)));
  (Fatal_LetRecArgumentMismatch, CFatal, (Prims.of_int (112)));
  (Fatal_MalformedActionDeclaration, CFatal, (Prims.of_int (113)));
  (Fatal_MismatchedPatternType, CFatal, (Prims.of_int (114)));
  (Fatal_MismatchUniversePolymorphic, CFatal, (Prims.of_int (115)));
  (Fatal_MissingDataConstructor, CFatal, (Prims.of_int (116)));
  (Fatal_MissingExposeInterfacesOption, CFatal, (Prims.of_int (117)));
  (Fatal_MissingFieldInRecord, CFatal, (Prims.of_int (118)));
  (Fatal_MissingImplementation, CFatal, (Prims.of_int (119)));
  (Fatal_MissingImplicitArguments, CFatal, (Prims.of_int (120)));
  (Fatal_MissingInterface, CFatal, (Prims.of_int (121)));
  (Fatal_MissingNameInBinder, CFatal, (Prims.of_int (122)));
  (Fatal_MissingPrimsModule, CFatal, (Prims.of_int (123)));
  (Fatal_MissingQuantifierBinder, CFatal, (Prims.of_int (124)));
  (Fatal_ModuleExpected, CFatal, (Prims.of_int (125)));
  (Fatal_ModuleFileNotFound, CFatal, (Prims.of_int (126)));
  (Fatal_ModuleFirstStatement, CFatal, (Prims.of_int (127)));
  (Fatal_ModuleNotFound, CFatal, (Prims.of_int (128)));
  (Fatal_ModuleOrFileNotFound, CFatal, (Prims.of_int (129)));
  (Fatal_MonadAlreadyDefined, CFatal, (Prims.of_int (130)));
  (Fatal_MoreThanOneDeclaration, CFatal, (Prims.of_int (131)));
  (Fatal_MultipleLetBinding, CFatal, (Prims.of_int (132)));
  (Fatal_NameNotFound, CFatal, (Prims.of_int (133)));
  (Fatal_NameSpaceNotFound, CFatal, (Prims.of_int (134)));
  (Fatal_NegativeUniverseConstFatal_NotSupported, CFatal,
    (Prims.of_int (135)));
  (Fatal_NoFileProvided, CFatal, (Prims.of_int (136)));
  (Fatal_NonInductiveInMutuallyDefinedType, CFatal, (Prims.of_int (137)));
  (Fatal_NonLinearPatternNotPermitted, CFatal, (Prims.of_int (138)));
  (Fatal_NonLinearPatternVars, CFatal, (Prims.of_int (139)));
  (Fatal_NonSingletonTopLevel, CFatal, (Prims.of_int (140)));
  (Fatal_NonSingletonTopLevelModule, CFatal, (Prims.of_int (141)));
  (Error_NonTopRecFunctionNotFullyEncoded, CError, (Prims.of_int (142)));
  (Fatal_NonTrivialPreConditionInPrims, CFatal, (Prims.of_int (143)));
  (Fatal_NonVariableInductiveTypeParameter, CFatal, (Prims.of_int (144)));
  (Fatal_NotApplicationOrFv, CFatal, (Prims.of_int (145)));
  (Fatal_NotEnoughArgsToEffect, CFatal, (Prims.of_int (146)));
  (Fatal_NotEnoughArgumentsForEffect, CFatal, (Prims.of_int (147)));
  (Fatal_NotFunctionType, CFatal, (Prims.of_int (148)));
  (Fatal_NotSupported, CFatal, (Prims.of_int (149)));
  (Fatal_NotTopLevelModule, CFatal, (Prims.of_int (150)));
  (Fatal_NotValidFStarFile, CFatal, (Prims.of_int (151)));
  (Fatal_NotValidIncludeDirectory, CFatal, (Prims.of_int (152)));
  (Fatal_OneModulePerFile, CFatal, (Prims.of_int (153)));
  (Fatal_OpenGoalsInSynthesis, CFatal, (Prims.of_int (154)));
  (Fatal_OptionsNotCompatible, CFatal, (Prims.of_int (155)));
  (Fatal_OutOfOrder, CFatal, (Prims.of_int (156)));
  (Fatal_ParseErrors, CFatal, (Prims.of_int (157)));
  (Fatal_ParseItError, CFatal, (Prims.of_int (158)));
  (Fatal_PolyTypeExpected, CFatal, (Prims.of_int (159)));
  (Fatal_PossibleInfiniteTyp, CFatal, (Prims.of_int (160)));
  (Fatal_PreModuleMismatch, CFatal, (Prims.of_int (161)));
  (Fatal_QulifierListNotPermitted, CFatal, (Prims.of_int (162)));
  (Fatal_RecursiveFunctionLiteral, CFatal, (Prims.of_int (163)));
  (Fatal_ReflectOnlySupportedOnEffects, CFatal, (Prims.of_int (164)));
  (Fatal_ReservedPrefix, CFatal, (Prims.of_int (165)));
  (Fatal_SMTOutputParseError, CFatal, (Prims.of_int (166)));
  (Fatal_SMTSolverError, CFatal, (Prims.of_int (167)));
  (Fatal_SyntaxError, CFatal, (Prims.of_int (168)));
  (Fatal_SynthByTacticError, CFatal, (Prims.of_int (169)));
  (Fatal_TacticGotStuck, CFatal, (Prims.of_int (170)));
  (Fatal_TcOneFragmentFailed, CFatal, (Prims.of_int (171)));
  (Fatal_TermOutsideOfDefLanguage, CFatal, (Prims.of_int (172)));
  (Fatal_ToManyArgumentToFunction, CFatal, (Prims.of_int (173)));
  (Fatal_TooManyOrTooFewFileMatch, CFatal, (Prims.of_int (174)));
  (Fatal_TooManyPatternArguments, CFatal, (Prims.of_int (175)));
  (Fatal_TooManyUniverse, CFatal, (Prims.of_int (176)));
  (Fatal_TypeMismatch, CFatal, (Prims.of_int (177)));
  (Fatal_TypeWithinPatternsAllowedOnVariablesOnly, CFatal,
    (Prims.of_int (178)));
  (Fatal_UnableToReadFile, CFatal, (Prims.of_int (179)));
  (Fatal_UnepxectedOrUnboundOperator, CFatal, (Prims.of_int (180)));
  (Fatal_UnexpectedBinder, CFatal, (Prims.of_int (181)));
  (Fatal_UnexpectedBindShape, CFatal, (Prims.of_int (182)));
  (Fatal_UnexpectedChar, CFatal, (Prims.of_int (183)));
  (Fatal_UnexpectedComputationTypeForLetRec, CFatal, (Prims.of_int (184)));
  (Fatal_UnexpectedConstructorType, CFatal, (Prims.of_int (185)));
  (Fatal_UnexpectedDataConstructor, CFatal, (Prims.of_int (186)));
  (Fatal_UnexpectedEffect, CFatal, (Prims.of_int (187)));
  (Fatal_UnexpectedEmptyRecord, CFatal, (Prims.of_int (188)));
  (Fatal_UnexpectedExpressionType, CFatal, (Prims.of_int (189)));
  (Fatal_UnexpectedFunctionParameterType, CFatal, (Prims.of_int (190)));
  (Fatal_UnexpectedGeneralizedUniverse, CFatal, (Prims.of_int (191)));
  (Fatal_UnexpectedGTotForLetRec, CFatal, (Prims.of_int (192)));
  (Fatal_UnexpectedGuard, CFatal, (Prims.of_int (193)));
  (Fatal_UnexpectedIdentifier, CFatal, (Prims.of_int (194)));
  (Fatal_UnexpectedImplicitArgument, CFatal, (Prims.of_int (195)));
  (Fatal_UnexpectedImplictArgument, CFatal, (Prims.of_int (196)));
  (Fatal_UnexpectedInductivetype, CFatal, (Prims.of_int (197)));
  (Fatal_UnexpectedLetBinding, CFatal, (Prims.of_int (198)));
  (Fatal_UnexpectedModuleDeclaration, CFatal, (Prims.of_int (199)));
  (Fatal_UnexpectedNumberOfUniverse, CFatal, (Prims.of_int (200)));
  (Fatal_UnexpectedNumericLiteral, CFatal, (Prims.of_int (201)));
  (Fatal_UnexpectedOperatorSymbol, CFatal, (Prims.of_int (202)));
  (Fatal_UnexpectedPattern, CFatal, (Prims.of_int (203)));
  (Fatal_UnexpectedPosition, CFatal, (Prims.of_int (204)));
  (Fatal_UnExpectedPreCondition, CFatal, (Prims.of_int (205)));
  (Fatal_UnexpectedReturnShape, CFatal, (Prims.of_int (206)));
  (Fatal_UnexpectedSignatureForMonad, CFatal, (Prims.of_int (207)));
  (Fatal_UnexpectedTerm, CFatal, (Prims.of_int (208)));
  (Fatal_UnexpectedTermInUniverse, CFatal, (Prims.of_int (209)));
  (Fatal_UnexpectedTermType, CFatal, (Prims.of_int (210)));
  (Fatal_UnexpectedTermVQuote, CFatal, (Prims.of_int (211)));
  (Fatal_UnexpectedUniversePolymorphicReturn, CFatal, (Prims.of_int (212)));
  (Fatal_UnexpectedUniverseVariable, CFatal, (Prims.of_int (213)));
  (Fatal_UnfoldableDeprecated, CFatal, (Prims.of_int (214)));
  (Fatal_UnificationNotWellFormed, CFatal, (Prims.of_int (215)));
  (Fatal_Uninstantiated, CFatal, (Prims.of_int (216)));
  (Error_UninstantiatedUnificationVarInTactic, CError, (Prims.of_int (217)));
  (Fatal_UninstantiatedVarInTactic, CFatal, (Prims.of_int (218)));
  (Fatal_UniverseMightContainSumOfTwoUnivVars, CFatal, (Prims.of_int (219)));
  (Fatal_UniversePolymorphicInnerLetBound, CFatal, (Prims.of_int (220)));
  (Fatal_UnknownAttribute, CFatal, (Prims.of_int (221)));
  (Fatal_UnknownToolForDep, CFatal, (Prims.of_int (222)));
  (Fatal_UnrecognizedExtension, CFatal, (Prims.of_int (223)));
  (Fatal_UnresolvedPatternVar, CFatal, (Prims.of_int (224)));
  (Fatal_UnsupportedConstant, CFatal, (Prims.of_int (225)));
  (Fatal_UnsupportedDisjuctivePatterns, CFatal, (Prims.of_int (226)));
  (Fatal_UnsupportedQualifier, CFatal, (Prims.of_int (227)));
  (Fatal_UserTacticFailure, CFatal, (Prims.of_int (228)));
  (Fatal_ValueRestriction, CFatal, (Prims.of_int (229)));
  (Fatal_VariableNotFound, CFatal, (Prims.of_int (230)));
  (Fatal_WrongBodyTypeForReturnWP, CFatal, (Prims.of_int (231)));
  (Fatal_WrongDataAppHeadFormat, CFatal, (Prims.of_int (232)));
  (Fatal_WrongDefinitionOrder, CFatal, (Prims.of_int (233)));
  (Fatal_WrongResultTypeAfterConstrutor, CFatal, (Prims.of_int (234)));
  (Fatal_WrongTerm, CFatal, (Prims.of_int (235)));
  (Fatal_WhenClauseNotSupported, CFatal, (Prims.of_int (236)));
  (Unused01, CFatal, (Prims.of_int (237)));
  (Warning_PluginNotImplemented, CError, (Prims.of_int (238)));
  (Warning_AddImplicitAssumeNewQualifier, CWarning, (Prims.of_int (239)));
  (Warning_AdmitWithoutDefinition, CWarning, (Prims.of_int (240)));
  (Warning_CachedFile, CWarning, (Prims.of_int (241)));
  (Warning_DefinitionNotTranslated, CWarning, (Prims.of_int (242)));
  (Warning_DependencyFound, CWarning, (Prims.of_int (243)));
  (Warning_DeprecatedEqualityOnBinder, CWarning, (Prims.of_int (244)));
  (Warning_DeprecatedOpaqueQualifier, CWarning, (Prims.of_int (245)));
  (Warning_DocOverwrite, CWarning, (Prims.of_int (246)));
  (Warning_FileNotWritten, CWarning, (Prims.of_int (247)));
  (Warning_Filtered, CWarning, (Prims.of_int (248)));
  (Warning_FunctionLiteralPrecisionLoss, CWarning, (Prims.of_int (249)));
  (Warning_FunctionNotExtacted, CWarning, (Prims.of_int (250)));
  (Warning_HintFailedToReplayProof, CWarning, (Prims.of_int (251)));
  (Warning_HitReplayFailed, CWarning, (Prims.of_int (252)));
  (Warning_IDEIgnoreCodeGen, CWarning, (Prims.of_int (253)));
  (Warning_IllFormedGoal, CWarning, (Prims.of_int (254)));
  (Warning_InaccessibleArgument, CWarning, (Prims.of_int (255)));
  (Warning_IncoherentImplicitQualifier, CWarning, (Prims.of_int (256)));
  (Warning_IrrelevantQualifierOnArgumentToReflect, CWarning,
    (Prims.of_int (257)));
  (Warning_IrrelevantQualifierOnArgumentToReify, CWarning,
    (Prims.of_int (258)));
  (Warning_MalformedWarnErrorList, CWarning, (Prims.of_int (259)));
  (Warning_MetaAlienNotATmUnknown, CWarning, (Prims.of_int (260)));
  (Warning_MultipleAscriptions, CWarning, (Prims.of_int (261)));
  (Warning_NondependentUserDefinedDataType, CWarning, (Prims.of_int (262)));
  (Warning_NonListLiteralSMTPattern, CWarning, (Prims.of_int (263)));
  (Warning_NormalizationFailure, CWarning, (Prims.of_int (264)));
  (Warning_NotDependentArrow, CWarning, (Prims.of_int (265)));
  (Warning_NotEmbedded, CWarning, (Prims.of_int (266)));
  (Warning_PatternMissingBoundVar, CWarning, (Prims.of_int (267)));
  (Warning_RecursiveDependency, CWarning, (Prims.of_int (268)));
  (Warning_RedundantExplicitCurrying, CWarning, (Prims.of_int (269)));
  (Warning_SMTPatTDeprecated, CWarning, (Prims.of_int (270)));
  (Warning_SMTPatternIllFormed, CWarning, (Prims.of_int (271)));
  (Warning_TopLevelEffect, CWarning, (Prims.of_int (272)));
  (Warning_UnboundModuleReference, CWarning, (Prims.of_int (273)));
  (Warning_UnexpectedFile, CWarning, (Prims.of_int (274)));
  (Warning_UnexpectedFsTypApp, CWarning, (Prims.of_int (275)));
  (Warning_UnexpectedZ3Output, CError, (Prims.of_int (276)));
  (Warning_UnprotectedTerm, CWarning, (Prims.of_int (277)));
  (Warning_UnrecognizedAttribute, CWarning, (Prims.of_int (278)));
  (Warning_UpperBoundCandidateAlreadyVisited, CWarning, (Prims.of_int (279)));
  (Warning_UseDefaultEffect, CWarning, (Prims.of_int (280)));
  (Warning_WrongErrorLocation, CWarning, (Prims.of_int (281)));
  (Warning_Z3InvocationWarning, CWarning, (Prims.of_int (282)));
  (Warning_MissingInterfaceOrImplementation, CWarning, (Prims.of_int (283)));
  (Warning_ConstructorBuildsUnexpectedType, CWarning, (Prims.of_int (284)));
  (Warning_ModuleOrFileNotFoundWarning, CWarning, (Prims.of_int (285)));
  (Error_NoLetMutable, CAlwaysError, (Prims.of_int (286)));
  (Error_BadImplicit, CAlwaysError, (Prims.of_int (287)));
  (Warning_DeprecatedDefinition, CWarning, (Prims.of_int (288)));
  (Fatal_SMTEncodingArityMismatch, CFatal, (Prims.of_int (289)));
  (Warning_Defensive, CWarning, (Prims.of_int (290)));
  (Warning_CantInspect, CWarning, (Prims.of_int (291)));
  (Warning_NilGivenExplicitArgs, CWarning, (Prims.of_int (292)));
  (Warning_ConsAppliedExplicitArgs, CWarning, (Prims.of_int (293)));
  (Warning_UnembedBinderKnot, CWarning, (Prims.of_int (294)));
  (Fatal_TacticProofRelevantGoal, CFatal, (Prims.of_int (295)));
  (Warning_TacAdmit, CWarning, (Prims.of_int (296)));
  (Fatal_IncoherentPatterns, CFatal, (Prims.of_int (297)));
  (Error_NoSMTButNeeded, CAlwaysError, (Prims.of_int (298)));
  (Fatal_UnexpectedAntiquotation, CFatal, (Prims.of_int (299)));
  (Fatal_SplicedUndef, CFatal, (Prims.of_int (300)));
  (Fatal_SpliceUnembedFail, CFatal, (Prims.of_int (301)));
  (Warning_ExtractionUnexpectedEffect, CWarning, (Prims.of_int (302)));
  (Error_DidNotFail, CAlwaysError, (Prims.of_int (303)));
  (Warning_UnappliedFail, CWarning, (Prims.of_int (304)));
  (Warning_QuantifierWithoutPattern, CSilent, (Prims.of_int (305)));
  (Error_EmptyFailErrs, CAlwaysError, (Prims.of_int (306)));
  (Warning_logicqualifier, CWarning, (Prims.of_int (307)));
  (Fatal_CyclicDependence, CFatal, (Prims.of_int (308)));
  (Error_InductiveAnnotNotAType, CError, (Prims.of_int (309)));
  (Fatal_FriendInterface, CFatal, (Prims.of_int (310)));
  (Error_CannotRedefineConst, CError, (Prims.of_int (311)));
  (Error_BadClassDecl, CError, (Prims.of_int (312)));
  (Error_BadInductiveParam, CFatal, (Prims.of_int (313)));
  (Error_FieldShadow, CFatal, (Prims.of_int (314)));
  (Error_UnexpectedDM4FType, CFatal, (Prims.of_int (315)));
  (Fatal_EffectAbbreviationResultTypeMismatch, CFatal, (Prims.of_int (316)));
  (Error_AlreadyCachedAssertionFailure, CFatal, (Prims.of_int (317)));
  (Error_MustEraseMissing, CWarning, (Prims.of_int (318)));
  (Warning_EffectfulArgumentToErasedFunction, CWarning, (Prims.of_int (319)));
  (Fatal_EmptySurfaceLet, CFatal, (Prims.of_int (320)));
  (Warning_UnexpectedCheckedFile, CWarning, (Prims.of_int (321)));
  (Fatal_ExtractionUnsupported, CFatal, (Prims.of_int (322)));
  (Warning_SMTErrorReason, CWarning, (Prims.of_int (323)));
  (Warning_CoercionNotFound, CWarning, (Prims.of_int (324)));
  (Error_QuakeFailed, CError, (Prims.of_int (325)));
  (Error_IllSMTPat, CError, (Prims.of_int (326)));
  (Error_IllScopedTerm, CError, (Prims.of_int (327)));
  (Warning_UnusedLetRec, CWarning, (Prims.of_int (328)));
  (Fatal_Effects_Ordering_Coherence, CError, (Prims.of_int (329)));
  (Warning_BleedingEdge_Feature, CWarning, (Prims.of_int (330)));
  (Warning_IgnoredBinding, CWarning, (Prims.of_int (331)));
  (Warning_CouldNotReadHints, CWarning, (Prims.of_int (333)));
  (Fatal_BadUvar, CFatal, (Prims.of_int (334)));
  (Warning_WarnOnUse, CSilent, (Prims.of_int (335)));
  (Warning_DeprecatedAttributeSyntax, CSilent, (Prims.of_int (336)));
  (Warning_DeprecatedGeneric, CWarning, (Prims.of_int (337)))]
let lookup_error :
  'uuuuuu2099 'uuuuuu2100 'uuuuuu2101 .
    ('uuuuuu2099 * 'uuuuuu2100 * 'uuuuuu2101) Prims.list ->
      'uuuuuu2099 -> ('uuuuuu2099 * 'uuuuuu2100 * 'uuuuuu2101)
  =
  fun settings ->
    fun e ->
      let uu____2134 =
        FStar_Util.try_find
          (fun uu____2153 ->
             match uu____2153 with | (v, uu____2161, i) -> e = v) settings in
      match uu____2134 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          failwith "Impossible: unrecognized error"
let lookup_error_range :
  'uuuuuu2202 'uuuuuu2203 .
    ('uuuuuu2202 * 'uuuuuu2203 * Prims.int) Prims.list ->
      (Prims.int * Prims.int) ->
        ('uuuuuu2202 * 'uuuuuu2203 * Prims.int) Prims.list
  =
  fun settings ->
    fun uu____2233 ->
      match uu____2233 with
      | (l, h) ->
          let uu____2248 =
            FStar_List.partition
              (fun uu____2279 ->
                 match uu____2279 with
                 | (uu____2286, uu____2287, i) -> (l <= i) && (i <= h))
              settings in
          (match uu____2248 with | (matches, uu____2298) -> matches)
let error_number :
  'uuuuuu2339 'uuuuuu2340 'uuuuuu2341 .
    ('uuuuuu2339 * 'uuuuuu2340 * 'uuuuuu2341) -> 'uuuuuu2341
  =
  fun uu____2352 -> match uu____2352 with | (uu____2359, uu____2360, i) -> i
let (warn_on_use_errno : Prims.int) =
  let uu____2362 = lookup_error default_settings Warning_WarnOnUse in
  error_number uu____2362
let (defensive_errno : Prims.int) =
  let uu____2369 = lookup_error default_settings Warning_Defensive in
  error_number uu____2369
let (update_flags :
  (error_flag * Prims.string) Prims.list -> error_setting Prims.list) =
  fun l ->
    let set_one_flag i flag1 default_flag =
      match (flag1, default_flag) with
      | (CWarning, CAlwaysError) ->
          let uu____2413 =
            let uu____2414 =
              let uu____2415 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot turn error %s into warning"
                uu____2415 in
            Invalid_warn_error_setting uu____2414 in
          FStar_Exn.raise uu____2413
      | (CError, CAlwaysError) ->
          let uu____2416 =
            let uu____2417 =
              let uu____2418 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot turn error %s into warning"
                uu____2418 in
            Invalid_warn_error_setting uu____2417 in
          FStar_Exn.raise uu____2416
      | (CSilent, CAlwaysError) ->
          let uu____2419 =
            let uu____2420 =
              let uu____2421 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot silence error %s" uu____2421 in
            Invalid_warn_error_setting uu____2420 in
          FStar_Exn.raise uu____2419
      | (uu____2422, CFatal) ->
          let uu____2423 =
            let uu____2424 =
              let uu____2425 = FStar_Util.string_of_int i in
              FStar_Util.format1
                "cannot change the error level of fatal error %s" uu____2425 in
            Invalid_warn_error_setting uu____2424 in
          FStar_Exn.raise uu____2423
      | uu____2426 -> flag1 in
    let set_flag_for_range uu____2452 =
      match uu____2452 with
      | (flag1, range) ->
          let errs = lookup_error_range default_settings range in
          FStar_List.map
            (fun uu____2505 ->
               match uu____2505 with
               | (v, default_flag, i) ->
                   let uu____2521 = set_one_flag i flag1 default_flag in
                   (v, uu____2521, i)) errs in
    let compute_range uu____2539 =
      match uu____2539 with
      | (flag1, s) ->
          let r = FStar_Util.split s ".." in
          let uu____2557 =
            match r with
            | r1::r2::[] ->
                let uu____2568 = FStar_Util.int_of_string r1 in
                let uu____2569 = FStar_Util.int_of_string r2 in
                (uu____2568, uu____2569)
            | uu____2570 ->
                let uu____2573 =
                  let uu____2574 =
                    FStar_Util.format1 "Malformed warn-error range %s" s in
                  Invalid_warn_error_setting uu____2574 in
                FStar_Exn.raise uu____2573 in
          (match uu____2557 with | (l1, h) -> (flag1, (l1, h))) in
    let error_range_settings = FStar_List.map compute_range l in
    let uu____2616 =
      FStar_List.collect set_flag_for_range error_range_settings in
    FStar_List.append uu____2616 default_settings
type error = (raw_error * Prims.string * FStar_Range.range)
exception Err of (raw_error * Prims.string) 
let (uu___is_Err : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Err uu____2664 -> true | uu____2669 -> false
let (__proj__Err__item__uu___ : Prims.exn -> (raw_error * Prims.string)) =
  fun projectee -> match projectee with | Err uu____2683 -> uu____2683
exception Error of error 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Error uu____2697 -> true | uu____2698 -> false
let (__proj__Error__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Error uu____2704 -> uu____2704
exception Warning of error 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning uu____2714 -> true | uu____2715 -> false
let (__proj__Warning__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Warning uu____2721 -> uu____2721
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Stop -> true | uu____2727 -> false
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Empty_frag -> true | uu____2733 -> false
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | ENotImplemented -> true | uu____2739 -> false
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EInfo -> true | uu____2745 -> false
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | EWarning -> true | uu____2751 -> false
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | EError -> true | uu____2757 -> false
type issue =
  {
  issue_message: Prims.string ;
  issue_level: issue_level ;
  issue_range: FStar_Range.range FStar_Pervasives_Native.option ;
  issue_number: Prims.int FStar_Pervasives_Native.option }
let (__proj__Mkissue__item__issue_message : issue -> Prims.string) =
  fun projectee ->
    match projectee with
    | { issue_message; issue_level = issue_level1; issue_range;
        issue_number;_} -> issue_message
let (__proj__Mkissue__item__issue_level : issue -> issue_level) =
  fun projectee ->
    match projectee with
    | { issue_message; issue_level = issue_level1; issue_range;
        issue_number;_} -> issue_level1
let (__proj__Mkissue__item__issue_range :
  issue -> FStar_Range.range FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_message; issue_level = issue_level1; issue_range;
        issue_number;_} -> issue_range
let (__proj__Mkissue__item__issue_number :
  issue -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { issue_message; issue_level = issue_level1; issue_range;
        issue_number;_} -> issue_number
type error_handler =
  {
  eh_add_one: issue -> unit ;
  eh_count_errors: unit -> Prims.int ;
  eh_report: unit -> issue Prims.list ;
  eh_clear: unit -> unit }
let (__proj__Mkerror_handler__item__eh_add_one :
  error_handler -> issue -> unit) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_add_one
let (__proj__Mkerror_handler__item__eh_count_errors :
  error_handler -> unit -> Prims.int) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} ->
        eh_count_errors
let (__proj__Mkerror_handler__item__eh_report :
  error_handler -> unit -> issue Prims.list) =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_report
let (__proj__Mkerror_handler__item__eh_clear : error_handler -> unit -> unit)
  =
  fun projectee ->
    match projectee with
    | { eh_add_one; eh_count_errors; eh_report; eh_clear;_} -> eh_clear
let (format_issue : issue -> Prims.string) =
  fun issue1 ->
    let level_header =
      match issue1.issue_level with
      | EInfo -> "Info"
      | EWarning -> "Warning"
      | EError -> "Error"
      | ENotImplemented -> "Feature not yet implemented: " in
    let uu____3014 =
      match issue1.issue_range with
      | FStar_Pervasives_Native.None -> ("", "")
      | FStar_Pervasives_Native.Some r when r = FStar_Range.dummyRange ->
          let uu____3024 =
            let uu____3025 =
              let uu____3026 = FStar_Range.def_range r in
              let uu____3027 = FStar_Range.def_range FStar_Range.dummyRange in
              uu____3026 = uu____3027 in
            if uu____3025
            then ""
            else
              (let uu____3029 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____3029) in
          ("", uu____3024)
      | FStar_Pervasives_Native.Some r ->
          let uu____3031 =
            let uu____3032 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____3032 in
          let uu____3033 =
            let uu____3034 =
              (let uu____3039 = FStar_Range.use_range r in
               let uu____3040 = FStar_Range.def_range r in
               uu____3039 = uu____3040) ||
                (let uu____3043 = FStar_Range.def_range r in
                 let uu____3044 =
                   FStar_Range.def_range FStar_Range.dummyRange in
                 uu____3043 = uu____3044) in
            if uu____3034
            then ""
            else
              (let uu____3046 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____3046) in
          (uu____3031, uu____3033) in
    match uu____3014 with
    | (range_str, see_also_str) ->
        let issue_number =
          match issue1.issue_number with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some n ->
              let uu____3051 = FStar_Util.string_of_int n in
              FStar_Util.format1 " %s" uu____3051 in
        FStar_Util.format5 "%s(%s%s) %s%s\n" range_str level_header
          issue_number issue1.issue_message see_also_str
let (print_issue : issue -> unit) =
  fun issue1 ->
    let printer =
      match issue1.issue_level with
      | EInfo -> FStar_Util.print_string
      | EWarning -> FStar_Util.print_warning
      | EError -> FStar_Util.print_error
      | ENotImplemented -> FStar_Util.print_error in
    let uu____3065 = format_issue issue1 in printer uu____3065
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1 ->
    fun i2 ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          Prims.int_zero
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
         uu____3084) -> ~- Prims.int_one
      | (FStar_Pervasives_Native.Some uu____3089,
         FStar_Pervasives_Native.None) -> Prims.int_one
      | (FStar_Pervasives_Native.Some r1, FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print ->
    let issues = FStar_Util.mk_ref [] in
    let add_one e =
      (let uu____3119 =
         (FStar_Options.defensive_abort ()) &&
           (e.issue_number = (FStar_Pervasives_Native.Some defensive_errno)) in
       if uu____3119
       then failwith "Aborting due to --defensive abort"
       else ());
      (match e.issue_level with
       | EInfo -> print_issue e
       | uu____3123 ->
           let uu____3124 =
             let uu____3127 = FStar_ST.op_Bang issues in e :: uu____3127 in
           FStar_ST.op_Colon_Equals issues uu____3124) in
    let count_errors uu____3155 =
      let uu____3156 = FStar_ST.op_Bang issues in
      FStar_List.fold_left
        (fun n ->
           fun i ->
             match i.issue_level with
             | EError -> n + Prims.int_one
             | uu____3173 -> n) Prims.int_zero uu____3156 in
    let report uu____3181 =
      let unique_issues =
        let uu____3185 = FStar_ST.op_Bang issues in
        FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu____3185 in
      let sorted_unique_issues =
        FStar_List.sortWith compare_issues unique_issues in
      if print then FStar_List.iter print_issue sorted_unique_issues else ();
      sorted_unique_issues in
    let clear uu____3212 = FStar_ST.op_Colon_Equals issues [] in
    {
      eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear
    }
let (default_handler : error_handler) = mk_default_handler true
let (current_handler : error_handler FStar_ST.ref) =
  FStar_Util.mk_ref default_handler
let (mk_issue :
  issue_level ->
    FStar_Range.range FStar_Pervasives_Native.option ->
      Prims.string -> Prims.int FStar_Pervasives_Native.option -> issue)
  =
  fun level ->
    fun range ->
      fun msg ->
        fun n ->
          {
            issue_message = msg;
            issue_level = level;
            issue_range = range;
            issue_number = n
          }
let (get_err_count : unit -> Prims.int) =
  fun uu____3257 ->
    let uu____3258 =
      let uu____3263 = FStar_ST.op_Bang current_handler in
      uu____3263.eh_count_errors in
    uu____3258 ()
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h ->
    fun issue1 ->
      h.eh_add_one issue1;
      if issue1.issue_level <> EInfo
      then
        ((let uu____3282 =
            let uu____3283 = FStar_ST.op_Bang FStar_Options.abort_counter in
            uu____3283 - Prims.int_one in
          FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____3282);
         (let uu____3296 =
            let uu____3297 = FStar_ST.op_Bang FStar_Options.abort_counter in
            uu____3297 = Prims.int_zero in
          if uu____3296 then failwith "Aborting due to --abort_on" else ()))
      else ()
let (add_one : issue -> unit) =
  fun issue1 ->
    FStar_Util.atomically
      (fun uu____3313 ->
         let uu____3314 = FStar_ST.op_Bang current_handler in
         wrapped_eh_add_one uu____3314 issue1)
let (add_many : issue Prims.list -> unit) =
  fun issues ->
    FStar_Util.atomically
      (fun uu____3332 ->
         let uu____3333 =
           let uu____3338 = FStar_ST.op_Bang current_handler in
           wrapped_eh_add_one uu____3338 in
         FStar_List.iter uu____3333 issues)
let (report_all : unit -> issue Prims.list) =
  fun uu____3351 ->
    let uu____3352 =
      let uu____3359 = FStar_ST.op_Bang current_handler in
      uu____3359.eh_report in
    uu____3352 ()
let (clear : unit -> unit) =
  fun uu____3370 ->
    let uu____3371 =
      let uu____3376 = FStar_ST.op_Bang current_handler in
      uu____3376.eh_clear in
    uu____3371 ()
let (set_handler : error_handler -> unit) =
  fun handler ->
    let issues = report_all () in
    clear ();
    FStar_ST.op_Colon_Equals current_handler handler;
    add_many issues
type error_message_prefix =
  {
  push_prefix: Prims.string -> unit ;
  pop_prefix: unit -> Prims.string ;
  clear_prefixs: unit -> unit ;
  append_prefixs: Prims.string -> Prims.string }
let (__proj__Mkerror_message_prefix__item__push_prefix :
  error_message_prefix -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { push_prefix; pop_prefix; clear_prefixs; append_prefixs;_} ->
        push_prefix
let (__proj__Mkerror_message_prefix__item__pop_prefix :
  error_message_prefix -> unit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push_prefix; pop_prefix; clear_prefixs; append_prefixs;_} ->
        pop_prefix
let (__proj__Mkerror_message_prefix__item__clear_prefixs :
  error_message_prefix -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { push_prefix; pop_prefix; clear_prefixs; append_prefixs;_} ->
        clear_prefixs
let (__proj__Mkerror_message_prefix__item__append_prefixs :
  error_message_prefix -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { push_prefix; pop_prefix; clear_prefixs; append_prefixs;_} ->
        append_prefixs
let (message_prefix : error_message_prefix) =
  let pfxs = FStar_Util.mk_ref [] in
  let push_prefix s =
    let uu____3564 =
      let uu____3567 = FStar_ST.op_Bang pfxs in s :: uu____3567 in
    FStar_ST.op_Colon_Equals pfxs uu____3564 in
  let pop_prefix s =
    let uu____3596 = FStar_ST.op_Bang pfxs in
    match uu____3596 with
    | h::t -> (FStar_ST.op_Colon_Equals pfxs t; h)
    | uu____3624 -> failwith "cannot pop error prefix..." in
  let clear_prefixs uu____3632 = FStar_ST.op_Colon_Equals pfxs [] in
  let append_prefixs s =
    let uu____3649 = FStar_ST.op_Bang pfxs in
    FStar_List.fold_left
      (fun s1 ->
         fun p ->
           let uu____3667 = FStar_String.op_Hat ":\n\t" s1 in
           FStar_String.op_Hat p uu____3667) s uu____3649 in
  { push_prefix; pop_prefix; clear_prefixs; append_prefixs }
let (diag : FStar_Range.range -> Prims.string -> unit) =
  fun r ->
    fun msg ->
      let uu____3678 = FStar_Options.debug_any () in
      if uu____3678
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None)
      else ()
let (warn_unsafe_options :
  FStar_Range.range FStar_Pervasives_Native.option -> Prims.string -> unit) =
  fun rng_opt ->
    fun msg ->
      let uu____3694 = FStar_Options.report_assumes () in
      match uu____3694 with
      | FStar_Pervasives_Native.Some "warn" ->
          let uu____3697 =
            let uu____3698 =
              FStar_String.op_Hat
                "Every use of this option triggers a warning: " msg in
            mk_issue EWarning rng_opt uu____3698
              (FStar_Pervasives_Native.Some warn_on_use_errno) in
          add_one uu____3697
      | FStar_Pervasives_Native.Some "error" ->
          let uu____3699 =
            let uu____3700 =
              FStar_String.op_Hat
                "Every use of this option triggers an error: " msg in
            mk_issue EError rng_opt uu____3700
              (FStar_Pervasives_Native.Some warn_on_use_errno) in
          add_one uu____3699
      | uu____3701 -> ()
let (set_option_warning_callback_range :
  FStar_Range.range FStar_Pervasives_Native.option -> unit) =
  fun ropt ->
    FStar_Options.set_option_warning_callback (warn_unsafe_options ropt)
let (uu___222 :
  (((Prims.string -> error_setting Prims.list) -> unit) *
    (unit -> error_setting Prims.list)))
  =
  let parser_callback = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let error_flags = FStar_Util.smap_create (Prims.of_int (10)) in
  let set_error_flags uu____3768 =
    let parse s =
      let uu____3777 = FStar_ST.op_Bang parser_callback in
      match uu____3777 with
      | FStar_Pervasives_Native.None ->
          failwith "Callback for parsing warn_error strings is not set"
      | FStar_Pervasives_Native.Some f -> f s in
    let we = FStar_Options.warn_error () in
    try
      (fun uu___234_3829 ->
         match () with
         | () ->
             let r = parse we in
             (FStar_Util.smap_add error_flags we
                (FStar_Pervasives_Native.Some r);
              FStar_Getopt.Success)) ()
    with
    | Invalid_warn_error_setting msg ->
        (FStar_Util.smap_add error_flags we FStar_Pervasives_Native.None;
         (let uu____3853 =
            FStar_String.op_Hat "Invalid --warn_error setting: " msg in
          FStar_Getopt.Error uu____3853)) in
  let get_error_flags uu____3861 =
    let we = FStar_Options.warn_error () in
    let uu____3863 = FStar_Util.smap_try_find error_flags we in
    match uu____3863 with
    | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some w) -> w
    | uu____3885 -> default_settings in
  let set_callbacks f =
    FStar_ST.op_Colon_Equals parser_callback (FStar_Pervasives_Native.Some f);
    FStar_Options.set_error_flags_callback set_error_flags;
    FStar_Options.set_option_warning_callback
      (warn_unsafe_options FStar_Pervasives_Native.None) in
  (set_callbacks, get_error_flags)
let (set_parse_warn_error :
  (Prims.string -> error_setting Prims.list) -> unit) =
  match uu___222 with
  | (set_parse_warn_error, error_flags) -> set_parse_warn_error
let (error_flags : unit -> error_setting Prims.list) =
  match uu___222 with | (set_parse_warn_error1, error_flags) -> error_flags
let (lookup : raw_error -> (raw_error * error_flag * Prims.int)) =
  fun err ->
    let flags = error_flags () in
    let uu____4045 = lookup_error flags err in
    match uu____4045 with
    | (v, level, i) ->
        let with_level level1 = (v, level1, i) in
        (match v with
         | Warning_Defensive when
             (FStar_Options.defensive_error ()) ||
               (FStar_Options.defensive_abort ())
             -> with_level CAlwaysError
         | Warning_WarnOnUse ->
             let level' =
               let uu____4080 = FStar_Options.report_assumes () in
               match uu____4080 with
               | FStar_Pervasives_Native.None -> level
               | FStar_Pervasives_Native.Some "warn" ->
                   (match level with
                    | CSilent -> CWarning
                    | uu____4083 -> level)
               | FStar_Pervasives_Native.Some "error" ->
                   (match level with
                    | CWarning -> CError
                    | CSilent -> CError
                    | uu____4084 -> level)
               | FStar_Pervasives_Native.Some uu____4085 -> level in
             with_level level'
         | uu____4086 -> with_level level)
let (log_issue : FStar_Range.range -> (raw_error * Prims.string) -> unit) =
  fun r ->
    fun uu____4100 ->
      match uu____4100 with
      | (e, msg) ->
          let uu____4107 = lookup e in
          (match uu____4107 with
           | (uu____4114, CAlwaysError, errno) ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | (uu____4116, CError, errno) ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | (uu____4118, CWarning, errno) ->
               add_one
                 (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | (uu____4120, CSilent, uu____4121) -> ()
           | (uu____4122, CFatal, errno) ->
               let i =
                 mk_issue EError (FStar_Pervasives_Native.Some r) msg
                   (FStar_Pervasives_Native.Some errno) in
               let uu____4125 = FStar_Options.ide () in
               if uu____4125
               then add_one i
               else
                 (let uu____4127 =
                    let uu____4128 = format_issue i in
                    FStar_String.op_Hat
                      "don't use log_issue to report fatal error, should use raise_error: "
                      uu____4128 in
                  failwith uu____4127))
let (add_errors :
  (raw_error * Prims.string * FStar_Range.range) Prims.list -> unit) =
  fun errs ->
    FStar_Util.atomically
      (fun uu____4151 ->
         FStar_List.iter
           (fun uu____4163 ->
              match uu____4163 with
              | (e, msg, r) ->
                  let uu____4173 =
                    let uu____4178 = message_prefix.append_prefixs msg in
                    (e, uu____4178) in
                  log_issue r uu____4173) errs)
let (issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option) =
  fun uu___0_4185 ->
    match uu___0_4185 with
    | Error (e, msg, r) ->
        let errno = let uu____4192 = lookup e in error_number uu____4192 in
        let uu____4199 =
          let uu____4200 = message_prefix.append_prefixs msg in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____4200
            (FStar_Pervasives_Native.Some errno) in
        FStar_Pervasives_Native.Some uu____4199
    | Err (e, msg) ->
        let errno = let uu____4204 = lookup e in error_number uu____4204 in
        let uu____4211 =
          let uu____4212 = message_prefix.append_prefixs msg in
          mk_issue EError FStar_Pervasives_Native.None uu____4212
            (FStar_Pervasives_Native.Some errno) in
        FStar_Pervasives_Native.Some uu____4211
    | uu____4213 -> FStar_Pervasives_Native.None
let (err_exn : Prims.exn -> unit) =
  fun exn ->
    if exn = Stop
    then ()
    else
      (let uu____4220 = issue_of_exn exn in
       match uu____4220 with
       | FStar_Pervasives_Native.Some issue1 -> add_one issue1
       | FStar_Pervasives_Native.None -> FStar_Exn.raise exn)
let (handleable : Prims.exn -> Prims.bool) =
  fun uu___1_4228 ->
    match uu___1_4228 with
    | Error uu____4229 -> true
    | Stop -> true
    | Err uu____4230 -> true
    | uu____4235 -> false
let (stop_if_err : unit -> unit) =
  fun uu____4240 ->
    let uu____4241 =
      let uu____4242 = get_err_count () in uu____4242 > Prims.int_zero in
    if uu____4241 then FStar_Exn.raise Stop else ()
let raise_error :
  'uuuuuu4250 .
    (raw_error * Prims.string) -> FStar_Range.range -> 'uuuuuu4250
  =
  fun uu____4263 ->
    fun r ->
      match uu____4263 with | (e, msg) -> FStar_Exn.raise (Error (e, msg, r))
let raise_err : 'uuuuuu4275 . (raw_error * Prims.string) -> 'uuuuuu4275 =
  fun uu____4284 ->
    match uu____4284 with | (e, msg) -> FStar_Exn.raise (Err (e, msg))
let catch_errors :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f ->
    let newh = mk_default_handler false in
    let old = FStar_ST.op_Bang current_handler in
    FStar_ST.op_Colon_Equals current_handler newh;
    (let r =
       try
         (fun uu___355_4336 ->
            match () with
            | () -> let r = f () in FStar_Pervasives_Native.Some r) ()
       with
       | uu___354_4342 ->
           (err_exn uu___354_4342; FStar_Pervasives_Native.None) in
     let all_issues = newh.eh_report () in
     FStar_ST.op_Colon_Equals current_handler old;
     (let uu____4356 =
        FStar_List.partition (fun i -> i.issue_level = EError) all_issues in
      match uu____4356 with
      | (errs, rest) -> (FStar_List.iter old.eh_add_one rest; (errs, r))))
let (find_multiset_discrepancy :
  Prims.int Prims.list ->
    Prims.int Prims.list ->
      (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  =
  fun l1 ->
    fun l2 ->
      let sort = FStar_List.sortWith (fun x -> fun y -> x - y) in
      let rec collect l =
        match l with
        | [] -> []
        | hd::tl ->
            let uu____4466 = collect tl in
            (match uu____4466 with
             | [] -> [(hd, Prims.int_one)]
             | (h, n)::t ->
                 if h = hd
                 then (h, (n + Prims.int_one)) :: t
                 else (hd, Prims.int_one) :: (h, n) :: t) in
      let summ l = collect l in
      let l11 = let uu____4546 = sort l1 in summ uu____4546 in
      let l21 = let uu____4556 = sort l2 in summ uu____4556 in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([], []) -> FStar_Pervasives_Native.None
        | ((e, n)::uu____4650, []) ->
            FStar_Pervasives_Native.Some (e, n, Prims.int_zero)
        | ([], (e, n)::uu____4685) ->
            FStar_Pervasives_Native.Some (e, Prims.int_zero, n)
        | ((hd1, n1)::tl1, (hd2, n2)::tl2) ->
            if hd1 < hd2
            then FStar_Pervasives_Native.Some (hd1, n1, Prims.int_zero)
            else
              if hd1 > hd2
              then FStar_Pervasives_Native.Some (hd2, Prims.int_zero, n2)
              else
                if n1 <> n2
                then FStar_Pervasives_Native.Some (hd1, n1, n2)
                else aux tl1 tl2 in
      aux l11 l21