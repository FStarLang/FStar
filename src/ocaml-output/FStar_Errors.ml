open Prims
exception Invalid_warn_error_setting of Prims.string 
let (uu___is_Invalid_warn_error_setting : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Invalid_warn_error_setting uu____20 -> true
    | uu____21 -> false
let (__proj__Invalid_warn_error_setting__item__uu___ :
  Prims.exn -> Prims.string) =
  fun projectee ->
    match projectee with | Invalid_warn_error_setting uu____27 -> uu____27
type error_flag =
  | CFatal 
  | CAlwaysError 
  | CError 
  | CWarning 
  | CSilent 
let (uu___is_CFatal : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CFatal -> true | uu____33 -> false
let (uu___is_CAlwaysError : error_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CAlwaysError -> true | uu____39 -> false
let (uu___is_CError : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CError -> true | uu____45 -> false
let (uu___is_CWarning : error_flag -> Prims.bool) =
  fun projectee ->
    match projectee with | CWarning -> true | uu____51 -> false
let (uu___is_CSilent : error_flag -> Prims.bool) =
  fun projectee -> match projectee with | CSilent -> true | uu____57 -> false
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
  | Warning_AbstractQualifier 
  | Warning_CouldNotReadHints 
  | Fatal_BadUvar 
  | Warning_WarnOnUse 
  | Warning_DeprecatedAttributeSyntax 
  | Warning_DeprecatedGeneric 
let (uu___is_Error_DependencyAnalysisFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_DependencyAnalysisFailed -> true
    | uu____63 -> false
let (uu___is_Error_IDETooManyPops : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IDETooManyPops -> true | uu____69 -> false
let (uu___is_Error_IDEUnrecognized : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IDEUnrecognized -> true | uu____75 -> false
let (uu___is_Error_InductiveTypeNotSatisfyPositivityCondition :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InductiveTypeNotSatisfyPositivityCondition -> true
    | uu____81 -> false
let (uu___is_Error_InvalidUniverseVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InvalidUniverseVar -> true
    | uu____87 -> false
let (uu___is_Error_MissingFileName : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_MissingFileName -> true | uu____93 -> false
let (uu___is_Error_ModuleFileNameMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_ModuleFileNameMismatch -> true
    | uu____99 -> false
let (uu___is_Error_OpPlusInUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_OpPlusInUniverse -> true
    | uu____105 -> false
let (uu___is_Error_OutOfRange : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_OutOfRange -> true | uu____111 -> false
let (uu___is_Error_ProofObligationFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_ProofObligationFailed -> true
    | uu____117 -> false
let (uu___is_Error_TooManyFiles : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_TooManyFiles -> true | uu____123 -> false
let (uu___is_Error_TypeCheckerFailToProve : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_TypeCheckerFailToProve -> true
    | uu____129 -> false
let (uu___is_Error_TypeError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_TypeError -> true | uu____135 -> false
let (uu___is_Error_UncontrainedUnificationVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UncontrainedUnificationVar -> true
    | uu____141 -> false
let (uu___is_Error_UnexpectedGTotComputation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedGTotComputation -> true
    | uu____147 -> false
let (uu___is_Error_UnexpectedInstance : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedInstance -> true
    | uu____153 -> false
let (uu___is_Error_UnknownFatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnknownFatal_AssertionFailure -> true
    | uu____159 -> false
let (uu___is_Error_Z3InvocationError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_Z3InvocationError -> true
    | uu____165 -> false
let (uu___is_Error_IDEAssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_IDEAssertionFailure -> true
    | uu____171 -> false
let (uu___is_Error_Z3SolverError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_Z3SolverError -> true | uu____177 -> false
let (uu___is_Fatal_AbstractTypeDeclarationInInterface :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AbstractTypeDeclarationInInterface -> true
    | uu____183 -> false
let (uu___is_Fatal_ActionMustHaveFunctionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ActionMustHaveFunctionType -> true
    | uu____189 -> false
let (uu___is_Fatal_AlreadyDefinedTopLevelDeclaration :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AlreadyDefinedTopLevelDeclaration -> true
    | uu____195 -> false
let (uu___is_Fatal_ArgumentLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ArgumentLengthMismatch -> true
    | uu____201 -> false
let (uu___is_Fatal_AssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssertionFailure -> true
    | uu____207 -> false
let (uu___is_Fatal_AssignToImmutableValues : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssignToImmutableValues -> true
    | uu____213 -> false
let (uu___is_Fatal_AssumeValInInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_AssumeValInInterface -> true
    | uu____219 -> false
let (uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_BadlyInstantiatedSynthByTactic -> true
    | uu____225 -> false
let (uu___is_Fatal_BadSignatureShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BadSignatureShape -> true
    | uu____231 -> false
let (uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BinderAndArgsLengthMismatch -> true
    | uu____237 -> false
let (uu___is_Fatal_BothValAndLetInInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_BothValAndLetInInterface -> true
    | uu____243 -> false
let (uu___is_Fatal_CardinalityConstraintViolated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CardinalityConstraintViolated -> true
    | uu____249 -> false
let (uu___is_Fatal_ComputationNotTotal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ComputationNotTotal -> true
    | uu____255 -> false
let (uu___is_Fatal_ComputationTypeNotAllowed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ComputationTypeNotAllowed -> true
    | uu____261 -> false
let (uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_ComputedTypeNotMatchAnnotation -> true
    | uu____267 -> false
let (uu___is_Fatal_ConstructorArgLengthMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorArgLengthMismatch -> true
    | uu____273 -> false
let (uu___is_Fatal_ConstructorFailedCheck : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorFailedCheck -> true
    | uu____279 -> false
let (uu___is_Fatal_ConstructorNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstructorNotFound -> true
    | uu____285 -> false
let (uu___is_Fatal_ConstsructorBuildWrongType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ConstsructorBuildWrongType -> true
    | uu____291 -> false
let (uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CycleInRecTypeAbbreviation -> true
    | uu____297 -> false
let (uu___is_Fatal_DataContructorNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DataContructorNotFound -> true
    | uu____303 -> false
let (uu___is_Fatal_DefaultQualifierNotAllowedOnEffects :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DefaultQualifierNotAllowedOnEffects -> true
    | uu____309 -> false
let (uu___is_Fatal_DefinitionNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DefinitionNotFound -> true
    | uu____315 -> false
let (uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DisjuctivePatternVarsMismatch -> true
    | uu____321 -> false
let (uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DivergentComputationCannotBeIncludedInTotal -> true
    | uu____327 -> false
let (uu___is_Fatal_DuplicateInImplementation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateInImplementation -> true
    | uu____333 -> false
let (uu___is_Fatal_DuplicateModuleOrInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateModuleOrInterface -> true
    | uu____339 -> false
let (uu___is_Fatal_DuplicateTopLevelNames : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateTopLevelNames -> true
    | uu____345 -> false
let (uu___is_Fatal_DuplicateTypeAnnotationAndValDecl :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_DuplicateTypeAnnotationAndValDecl -> true
    | uu____351 -> false
let (uu___is_Fatal_EffectCannotBeReified : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectCannotBeReified -> true
    | uu____357 -> false
let (uu___is_Fatal_EffectConstructorNotFullyApplied :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectConstructorNotFullyApplied -> true
    | uu____363 -> false
let (uu___is_Fatal_EffectfulAndPureComputationMismatch :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectfulAndPureComputationMismatch -> true
    | uu____369 -> false
let (uu___is_Fatal_EffectNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_EffectNotFound -> true | uu____375 -> false
let (uu___is_Fatal_EffectsCannotBeComposed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectsCannotBeComposed -> true
    | uu____381 -> false
let (uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_ErrorInSolveDeferredConstraints -> true
    | uu____387 -> false
let (uu___is_Fatal_ErrorsReported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ErrorsReported -> true | uu____393 -> false
let (uu___is_Fatal_EscapedBoundVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_EscapedBoundVar -> true | uu____399 -> false
let (uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedArrowAnnotatedType -> true
    | uu____405 -> false
let (uu___is_Fatal_ExpectedGhostExpression : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedGhostExpression -> true
    | uu____411 -> false
let (uu___is_Fatal_ExpectedPureExpression : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectedPureExpression -> true
    | uu____417 -> false
let (uu___is_Fatal_ExpectNormalizedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectNormalizedEffect -> true
    | uu____423 -> false
let (uu___is_Fatal_ExpectTermGotFunction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectTermGotFunction -> true
    | uu____429 -> false
let (uu___is_Fatal_ExpectTrivialPreCondition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExpectTrivialPreCondition -> true
    | uu____435 -> false
let (uu___is_Fatal_FailToCompileNativeTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToCompileNativeTactic -> true
    | uu____441 -> false
let (uu___is_Fatal_FailToExtractNativeTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToExtractNativeTactic -> true
    | uu____447 -> false
let (uu___is_Fatal_FailToProcessPragma : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToProcessPragma -> true
    | uu____453 -> false
let (uu___is_Fatal_FailToResolveImplicitArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToResolveImplicitArgument -> true
    | uu____459 -> false
let (uu___is_Fatal_FailToSolveUniverseInEquality : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FailToSolveUniverseInEquality -> true
    | uu____465 -> false
let (uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_FieldsNotBelongToSameRecordType -> true
    | uu____471 -> false
let (uu___is_Fatal_ForbiddenReferenceToCurrentModule :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ForbiddenReferenceToCurrentModule -> true
    | uu____477 -> false
let (uu___is_Fatal_FreeVariables : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_FreeVariables -> true | uu____483 -> false
let (uu___is_Fatal_FunctionTypeExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FunctionTypeExpected -> true
    | uu____489 -> false
let (uu___is_Fatal_IdentifierNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IdentifierNotFound -> true
    | uu____495 -> false
let (uu___is_Fatal_IllAppliedConstant : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllAppliedConstant -> true
    | uu____501 -> false
let (uu___is_Fatal_IllegalCharInByteArray : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllegalCharInByteArray -> true
    | uu____507 -> false
let (uu___is_Fatal_IllegalCharInOperatorName : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IllegalCharInOperatorName -> true
    | uu____513 -> false
let (uu___is_Fatal_IllTyped : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_IllTyped -> true | uu____519 -> false
let (uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleAbbrevLidBundle -> true
    | uu____525 -> false
let (uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleAbbrevRenameBundle -> true
    | uu____531 -> false
let (uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleInductiveWithAbbrev -> true
    | uu____537 -> false
let (uu___is_Fatal_ImpossiblePrePostAbs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossiblePrePostAbs -> true
    | uu____543 -> false
let (uu___is_Fatal_ImpossiblePrePostArrow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossiblePrePostArrow -> true
    | uu____549 -> false
let (uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleToGenerateDMEffect -> true
    | uu____555 -> false
let (uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevBundle -> true
    | uu____561 -> false
let (uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ImpossibleTypeAbbrevSigeltBundle -> true
    | uu____567 -> false
let (uu___is_Fatal_IncludeModuleNotPrepared : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncludeModuleNotPrepared -> true
    | uu____573 -> false
let (uu___is_Fatal_IncoherentInlineUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncoherentInlineUniverse -> true
    | uu____579 -> false
let (uu___is_Fatal_IncompatibleKinds : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleKinds -> true
    | uu____585 -> false
let (uu___is_Fatal_IncompatibleNumberOfTypes : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleNumberOfTypes -> true
    | uu____591 -> false
let (uu___is_Fatal_IncompatibleSetOfUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleSetOfUniverse -> true
    | uu____597 -> false
let (uu___is_Fatal_IncompatibleUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncompatibleUniverse -> true
    | uu____603 -> false
let (uu___is_Fatal_InconsistentImplicitArgumentAnnotation :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentImplicitArgumentAnnotation -> true
    | uu____609 -> false
let (uu___is_Fatal_InconsistentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentImplicitQualifier -> true
    | uu____615 -> false
let (uu___is_Fatal_InconsistentQualifierAnnotation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InconsistentQualifierAnnotation -> true
    | uu____621 -> false
let (uu___is_Fatal_InferredTypeCauseVarEscape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InferredTypeCauseVarEscape -> true
    | uu____627 -> false
let (uu___is_Fatal_InlineRenamedAsUnfold : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InlineRenamedAsUnfold -> true
    | uu____633 -> false
let (uu___is_Fatal_InsufficientPatternArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InsufficientPatternArguments -> true
    | uu____639 -> false
let (uu___is_Fatal_InterfaceAlreadyProcessed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceAlreadyProcessed -> true
    | uu____645 -> false
let (uu___is_Fatal_InterfaceNotImplementedByModule : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceNotImplementedByModule -> true
    | uu____651 -> false
let (uu___is_Fatal_InterfaceWithTypeImplementation : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_InterfaceWithTypeImplementation -> true
    | uu____657 -> false
let (uu___is_Fatal_InvalidFloatingPointNumber : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidFloatingPointNumber -> true
    | uu____663 -> false
let (uu___is_Fatal_InvalidFSDocKeyword : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidFSDocKeyword -> true
    | uu____669 -> false
let (uu___is_Fatal_InvalidIdentifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidIdentifier -> true
    | uu____675 -> false
let (uu___is_Fatal_InvalidLemmaArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidLemmaArgument -> true
    | uu____681 -> false
let (uu___is_Fatal_InvalidNumericLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidNumericLiteral -> true
    | uu____687 -> false
let (uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidRedefinitionOfLexT -> true
    | uu____693 -> false
let (uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidUnicodeInStringLiteral -> true
    | uu____699 -> false
let (uu___is_Fatal_InvalidUTF8Encoding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidUTF8Encoding -> true
    | uu____705 -> false
let (uu___is_Fatal_InvalidWarnErrorSetting : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_InvalidWarnErrorSetting -> true
    | uu____711 -> false
let (uu___is_Fatal_LetBoundMonadicMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetBoundMonadicMismatch -> true
    | uu____717 -> false
let (uu___is_Fatal_LetMutableForVariablesOnly : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetMutableForVariablesOnly -> true
    | uu____723 -> false
let (uu___is_Fatal_LetOpenModuleOnly : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetOpenModuleOnly -> true
    | uu____729 -> false
let (uu___is_Fatal_LetRecArgumentMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_LetRecArgumentMismatch -> true
    | uu____735 -> false
let (uu___is_Fatal_MalformedActionDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MalformedActionDeclaration -> true
    | uu____741 -> false
let (uu___is_Fatal_MismatchedPatternType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MismatchedPatternType -> true
    | uu____747 -> false
let (uu___is_Fatal_MismatchUniversePolymorphic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MismatchUniversePolymorphic -> true
    | uu____753 -> false
let (uu___is_Fatal_MissingDataConstructor : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingDataConstructor -> true
    | uu____759 -> false
let (uu___is_Fatal_MissingExposeInterfacesOption : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingExposeInterfacesOption -> true
    | uu____765 -> false
let (uu___is_Fatal_MissingFieldInRecord : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingFieldInRecord -> true
    | uu____771 -> false
let (uu___is_Fatal_MissingImplementation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingImplementation -> true
    | uu____777 -> false
let (uu___is_Fatal_MissingImplicitArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingImplicitArguments -> true
    | uu____783 -> false
let (uu___is_Fatal_MissingInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingInterface -> true
    | uu____789 -> false
let (uu___is_Fatal_MissingNameInBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingNameInBinder -> true
    | uu____795 -> false
let (uu___is_Fatal_MissingPrimsModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingPrimsModule -> true
    | uu____801 -> false
let (uu___is_Fatal_MissingQuantifierBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MissingQuantifierBinder -> true
    | uu____807 -> false
let (uu___is_Fatal_ModuleExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ModuleExpected -> true | uu____813 -> false
let (uu___is_Fatal_ModuleFileNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleFileNotFound -> true
    | uu____819 -> false
let (uu___is_Fatal_ModuleFirstStatement : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleFirstStatement -> true
    | uu____825 -> false
let (uu___is_Fatal_ModuleNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ModuleNotFound -> true | uu____831 -> false
let (uu___is_Fatal_ModuleOrFileNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ModuleOrFileNotFound -> true
    | uu____837 -> false
let (uu___is_Fatal_MonadAlreadyDefined : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MonadAlreadyDefined -> true
    | uu____843 -> false
let (uu___is_Fatal_MoreThanOneDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MoreThanOneDeclaration -> true
    | uu____849 -> false
let (uu___is_Fatal_MultipleLetBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_MultipleLetBinding -> true
    | uu____855 -> false
let (uu___is_Fatal_NameNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NameNotFound -> true | uu____861 -> false
let (uu___is_Fatal_NameSpaceNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NameSpaceNotFound -> true
    | uu____867 -> false
let (uu___is_Fatal_NegativeUniverseConstFatal_NotSupported :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NegativeUniverseConstFatal_NotSupported -> true
    | uu____873 -> false
let (uu___is_Fatal_NoFileProvided : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NoFileProvided -> true | uu____879 -> false
let (uu___is_Fatal_NonInductiveInMutuallyDefinedType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonInductiveInMutuallyDefinedType -> true
    | uu____885 -> false
let (uu___is_Fatal_NonLinearPatternNotPermitted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonLinearPatternNotPermitted -> true
    | uu____891 -> false
let (uu___is_Fatal_NonLinearPatternVars : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonLinearPatternVars -> true
    | uu____897 -> false
let (uu___is_Fatal_NonSingletonTopLevel : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonSingletonTopLevel -> true
    | uu____903 -> false
let (uu___is_Fatal_NonSingletonTopLevelModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonSingletonTopLevelModule -> true
    | uu____909 -> false
let (uu___is_Error_NonTopRecFunctionNotFullyEncoded :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_NonTopRecFunctionNotFullyEncoded -> true
    | uu____915 -> false
let (uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonTrivialPreConditionInPrims -> true
    | uu____921 -> false
let (uu___is_Fatal_NonVariableInductiveTypeParameter :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NonVariableInductiveTypeParameter -> true
    | uu____927 -> false
let (uu___is_Fatal_NotApplicationOrFv : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotApplicationOrFv -> true
    | uu____933 -> false
let (uu___is_Fatal_NotEnoughArgsToEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotEnoughArgsToEffect -> true
    | uu____939 -> false
let (uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotEnoughArgumentsForEffect -> true
    | uu____945 -> false
let (uu___is_Fatal_NotFunctionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NotFunctionType -> true | uu____951 -> false
let (uu___is_Fatal_NotSupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_NotSupported -> true | uu____957 -> false
let (uu___is_Fatal_NotTopLevelModule : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotTopLevelModule -> true
    | uu____963 -> false
let (uu___is_Fatal_NotValidFStarFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotValidFStarFile -> true
    | uu____969 -> false
let (uu___is_Fatal_NotValidIncludeDirectory : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_NotValidIncludeDirectory -> true
    | uu____975 -> false
let (uu___is_Fatal_OneModulePerFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OneModulePerFile -> true
    | uu____981 -> false
let (uu___is_Fatal_OpenGoalsInSynthesis : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OpenGoalsInSynthesis -> true
    | uu____987 -> false
let (uu___is_Fatal_OptionsNotCompatible : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_OptionsNotCompatible -> true
    | uu____993 -> false
let (uu___is_Fatal_OutOfOrder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_OutOfOrder -> true | uu____999 -> false
let (uu___is_Fatal_ParseErrors : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ParseErrors -> true | uu____1005 -> false
let (uu___is_Fatal_ParseItError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ParseItError -> true | uu____1011 -> false
let (uu___is_Fatal_PolyTypeExpected : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PolyTypeExpected -> true
    | uu____1017 -> false
let (uu___is_Fatal_PossibleInfiniteTyp : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PossibleInfiniteTyp -> true
    | uu____1023 -> false
let (uu___is_Fatal_PreModuleMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_PreModuleMismatch -> true
    | uu____1029 -> false
let (uu___is_Fatal_QulifierListNotPermitted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_QulifierListNotPermitted -> true
    | uu____1035 -> false
let (uu___is_Fatal_RecursiveFunctionLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_RecursiveFunctionLiteral -> true
    | uu____1041 -> false
let (uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ReflectOnlySupportedOnEffects -> true
    | uu____1047 -> false
let (uu___is_Fatal_ReservedPrefix : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_ReservedPrefix -> true | uu____1053 -> false
let (uu___is_Fatal_SMTOutputParseError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SMTOutputParseError -> true
    | uu____1059 -> false
let (uu___is_Fatal_SMTSolverError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SMTSolverError -> true | uu____1065 -> false
let (uu___is_Fatal_SyntaxError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SyntaxError -> true | uu____1071 -> false
let (uu___is_Fatal_SynthByTacticError : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SynthByTacticError -> true
    | uu____1077 -> false
let (uu___is_Fatal_TacticGotStuck : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_TacticGotStuck -> true | uu____1083 -> false
let (uu___is_Fatal_TcOneFragmentFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TcOneFragmentFailed -> true
    | uu____1089 -> false
let (uu___is_Fatal_TermOutsideOfDefLanguage : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TermOutsideOfDefLanguage -> true
    | uu____1095 -> false
let (uu___is_Fatal_ToManyArgumentToFunction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ToManyArgumentToFunction -> true
    | uu____1101 -> false
let (uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyOrTooFewFileMatch -> true
    | uu____1107 -> false
let (uu___is_Fatal_TooManyPatternArguments : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyPatternArguments -> true
    | uu____1113 -> false
let (uu___is_Fatal_TooManyUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TooManyUniverse -> true
    | uu____1119 -> false
let (uu___is_Fatal_TypeMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_TypeMismatch -> true | uu____1125 -> false
let (uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TypeWithinPatternsAllowedOnVariablesOnly -> true
    | uu____1131 -> false
let (uu___is_Fatal_UnableToReadFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnableToReadFile -> true
    | uu____1137 -> false
let (uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnepxectedOrUnboundOperator -> true
    | uu____1143 -> false
let (uu___is_Fatal_UnexpectedBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedBinder -> true
    | uu____1149 -> false
let (uu___is_Fatal_UnexpectedBindShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedBindShape -> true
    | uu____1155 -> false
let (uu___is_Fatal_UnexpectedChar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_UnexpectedChar -> true | uu____1161 -> false
let (uu___is_Fatal_UnexpectedComputationTypeForLetRec :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedComputationTypeForLetRec -> true
    | uu____1167 -> false
let (uu___is_Fatal_UnexpectedConstructorType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedConstructorType -> true
    | uu____1173 -> false
let (uu___is_Fatal_UnexpectedDataConstructor : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedDataConstructor -> true
    | uu____1179 -> false
let (uu___is_Fatal_UnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedEffect -> true
    | uu____1185 -> false
let (uu___is_Fatal_UnexpectedEmptyRecord : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedEmptyRecord -> true
    | uu____1191 -> false
let (uu___is_Fatal_UnexpectedExpressionType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedExpressionType -> true
    | uu____1197 -> false
let (uu___is_Fatal_UnexpectedFunctionParameterType : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedFunctionParameterType -> true
    | uu____1203 -> false
let (uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGeneralizedUniverse -> true
    | uu____1209 -> false
let (uu___is_Fatal_UnexpectedGTotForLetRec : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGTotForLetRec -> true
    | uu____1215 -> false
let (uu___is_Fatal_UnexpectedGuard : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedGuard -> true
    | uu____1221 -> false
let (uu___is_Fatal_UnexpectedIdentifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedIdentifier -> true
    | uu____1227 -> false
let (uu___is_Fatal_UnexpectedImplicitArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedImplicitArgument -> true
    | uu____1233 -> false
let (uu___is_Fatal_UnexpectedImplictArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedImplictArgument -> true
    | uu____1239 -> false
let (uu___is_Fatal_UnexpectedInductivetype : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedInductivetype -> true
    | uu____1245 -> false
let (uu___is_Fatal_UnexpectedLetBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedLetBinding -> true
    | uu____1251 -> false
let (uu___is_Fatal_UnexpectedModuleDeclaration : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedModuleDeclaration -> true
    | uu____1257 -> false
let (uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedNumberOfUniverse -> true
    | uu____1263 -> false
let (uu___is_Fatal_UnexpectedNumericLiteral : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedNumericLiteral -> true
    | uu____1269 -> false
let (uu___is_Fatal_UnexpectedOperatorSymbol : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedOperatorSymbol -> true
    | uu____1275 -> false
let (uu___is_Fatal_UnexpectedPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedPattern -> true
    | uu____1281 -> false
let (uu___is_Fatal_UnexpectedPosition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedPosition -> true
    | uu____1287 -> false
let (uu___is_Fatal_UnExpectedPreCondition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnExpectedPreCondition -> true
    | uu____1293 -> false
let (uu___is_Fatal_UnexpectedReturnShape : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedReturnShape -> true
    | uu____1299 -> false
let (uu___is_Fatal_UnexpectedSignatureForMonad : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedSignatureForMonad -> true
    | uu____1305 -> false
let (uu___is_Fatal_UnexpectedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_UnexpectedTerm -> true | uu____1311 -> false
let (uu___is_Fatal_UnexpectedTermInUniverse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermInUniverse -> true
    | uu____1317 -> false
let (uu___is_Fatal_UnexpectedTermType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermType -> true
    | uu____1323 -> false
let (uu___is_Fatal_UnexpectedTermVQuote : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedTermVQuote -> true
    | uu____1329 -> false
let (uu___is_Fatal_UnexpectedUniversePolymorphicReturn :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedUniversePolymorphicReturn -> true
    | uu____1335 -> false
let (uu___is_Fatal_UnexpectedUniverseVariable : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedUniverseVariable -> true
    | uu____1341 -> false
let (uu___is_Fatal_UnfoldableDeprecated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnfoldableDeprecated -> true
    | uu____1347 -> false
let (uu___is_Fatal_UnificationNotWellFormed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnificationNotWellFormed -> true
    | uu____1353 -> false
let (uu___is_Fatal_Uninstantiated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_Uninstantiated -> true | uu____1359 -> false
let (uu___is_Error_UninstantiatedUnificationVarInTactic :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UninstantiatedUnificationVarInTactic -> true
    | uu____1365 -> false
let (uu___is_Fatal_UninstantiatedVarInTactic : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UninstantiatedVarInTactic -> true
    | uu____1371 -> false
let (uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UniverseMightContainSumOfTwoUnivVars -> true
    | uu____1377 -> false
let (uu___is_Fatal_UniversePolymorphicInnerLetBound :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UniversePolymorphicInnerLetBound -> true
    | uu____1383 -> false
let (uu___is_Fatal_UnknownAttribute : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnknownAttribute -> true
    | uu____1389 -> false
let (uu___is_Fatal_UnknownToolForDep : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnknownToolForDep -> true
    | uu____1395 -> false
let (uu___is_Fatal_UnrecognizedExtension : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnrecognizedExtension -> true
    | uu____1401 -> false
let (uu___is_Fatal_UnresolvedPatternVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnresolvedPatternVar -> true
    | uu____1407 -> false
let (uu___is_Fatal_UnsupportedConstant : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedConstant -> true
    | uu____1413 -> false
let (uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedDisjuctivePatterns -> true
    | uu____1419 -> false
let (uu___is_Fatal_UnsupportedQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnsupportedQualifier -> true
    | uu____1425 -> false
let (uu___is_Fatal_UserTacticFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UserTacticFailure -> true
    | uu____1431 -> false
let (uu___is_Fatal_ValueRestriction : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ValueRestriction -> true
    | uu____1437 -> false
let (uu___is_Fatal_VariableNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_VariableNotFound -> true
    | uu____1443 -> false
let (uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongBodyTypeForReturnWP -> true
    | uu____1449 -> false
let (uu___is_Fatal_WrongDataAppHeadFormat : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongDataAppHeadFormat -> true
    | uu____1455 -> false
let (uu___is_Fatal_WrongDefinitionOrder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WrongDefinitionOrder -> true
    | uu____1461 -> false
let (uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Fatal_WrongResultTypeAfterConstrutor -> true
    | uu____1467 -> false
let (uu___is_Fatal_WrongTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_WrongTerm -> true | uu____1473 -> false
let (uu___is_Fatal_WhenClauseNotSupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_WhenClauseNotSupported -> true
    | uu____1479 -> false
let (uu___is_Unused01 : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Unused01 -> true | uu____1485 -> false
let (uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Warning_AddImplicitAssumeNewQualifier -> true
    | uu____1491 -> false
let (uu___is_Warning_AdmitWithoutDefinition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_AdmitWithoutDefinition -> true
    | uu____1497 -> false
let (uu___is_Warning_CachedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_CachedFile -> true | uu____1503 -> false
let (uu___is_Warning_DefinitionNotTranslated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DefinitionNotTranslated -> true
    | uu____1509 -> false
let (uu___is_Warning_DependencyFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DependencyFound -> true
    | uu____1515 -> false
let (uu___is_Warning_DeprecatedEqualityOnBinder : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedEqualityOnBinder -> true
    | uu____1521 -> false
let (uu___is_Warning_DeprecatedOpaqueQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedOpaqueQualifier -> true
    | uu____1527 -> false
let (uu___is_Warning_DocOverwrite : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_DocOverwrite -> true | uu____1533 -> false
let (uu___is_Warning_FileNotWritten : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_FileNotWritten -> true
    | uu____1539 -> false
let (uu___is_Warning_Filtered : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_Filtered -> true | uu____1545 -> false
let (uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | Warning_FunctionLiteralPrecisionLoss -> true
    | uu____1551 -> false
let (uu___is_Warning_FunctionNotExtacted : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_FunctionNotExtacted -> true
    | uu____1557 -> false
let (uu___is_Warning_HintFailedToReplayProof : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_HintFailedToReplayProof -> true
    | uu____1563 -> false
let (uu___is_Warning_HitReplayFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_HitReplayFailed -> true
    | uu____1569 -> false
let (uu___is_Warning_IDEIgnoreCodeGen : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IDEIgnoreCodeGen -> true
    | uu____1575 -> false
let (uu___is_Warning_IllFormedGoal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IllFormedGoal -> true
    | uu____1581 -> false
let (uu___is_Warning_InaccessibleArgument : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_InaccessibleArgument -> true
    | uu____1587 -> false
let (uu___is_Warning_IncoherentImplicitQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IncoherentImplicitQualifier -> true
    | uu____1593 -> false
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReflect :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReflect -> true
    | uu____1599 -> false
let (uu___is_Warning_IrrelevantQualifierOnArgumentToReify :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IrrelevantQualifierOnArgumentToReify -> true
    | uu____1605 -> false
let (uu___is_Warning_MalformedWarnErrorList : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MalformedWarnErrorList -> true
    | uu____1611 -> false
let (uu___is_Warning_MetaAlienNotATmUnknown : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MetaAlienNotATmUnknown -> true
    | uu____1617 -> false
let (uu___is_Warning_MultipleAscriptions : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MultipleAscriptions -> true
    | uu____1623 -> false
let (uu___is_Warning_NondependentUserDefinedDataType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NondependentUserDefinedDataType -> true
    | uu____1629 -> false
let (uu___is_Warning_NonListLiteralSMTPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NonListLiteralSMTPattern -> true
    | uu____1635 -> false
let (uu___is_Warning_NormalizationFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NormalizationFailure -> true
    | uu____1641 -> false
let (uu___is_Warning_NotDependentArrow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NotDependentArrow -> true
    | uu____1647 -> false
let (uu___is_Warning_NotEmbedded : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_NotEmbedded -> true | uu____1653 -> false
let (uu___is_Warning_PatternMissingBoundVar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_PatternMissingBoundVar -> true
    | uu____1659 -> false
let (uu___is_Warning_RecursiveDependency : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_RecursiveDependency -> true
    | uu____1665 -> false
let (uu___is_Warning_RedundantExplicitCurrying : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_RedundantExplicitCurrying -> true
    | uu____1671 -> false
let (uu___is_Warning_SMTPatTDeprecated : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTPatTDeprecated -> true
    | uu____1677 -> false
let (uu___is_Warning_SMTPatternIllFormed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTPatternIllFormed -> true
    | uu____1683 -> false
let (uu___is_Warning_TopLevelEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_TopLevelEffect -> true
    | uu____1689 -> false
let (uu___is_Warning_UnboundModuleReference : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnboundModuleReference -> true
    | uu____1695 -> false
let (uu___is_Warning_UnexpectedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedFile -> true
    | uu____1701 -> false
let (uu___is_Warning_UnexpectedFsTypApp : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedFsTypApp -> true
    | uu____1707 -> false
let (uu___is_Warning_UnexpectedZ3Output : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedZ3Output -> true
    | uu____1713 -> false
let (uu___is_Warning_UnprotectedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnprotectedTerm -> true
    | uu____1719 -> false
let (uu___is_Warning_UnrecognizedAttribute : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnrecognizedAttribute -> true
    | uu____1725 -> false
let (uu___is_Warning_UpperBoundCandidateAlreadyVisited :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UpperBoundCandidateAlreadyVisited -> true
    | uu____1731 -> false
let (uu___is_Warning_UseDefaultEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UseDefaultEffect -> true
    | uu____1737 -> false
let (uu___is_Warning_WrongErrorLocation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_WrongErrorLocation -> true
    | uu____1743 -> false
let (uu___is_Warning_Z3InvocationWarning : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_Z3InvocationWarning -> true
    | uu____1749 -> false
let (uu___is_Warning_PluginNotImplemented : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_PluginNotImplemented -> true
    | uu____1755 -> false
let (uu___is_Warning_MissingInterfaceOrImplementation :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_MissingInterfaceOrImplementation -> true
    | uu____1761 -> false
let (uu___is_Warning_ConstructorBuildsUnexpectedType :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ConstructorBuildsUnexpectedType -> true
    | uu____1767 -> false
let (uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ModuleOrFileNotFoundWarning -> true
    | uu____1773 -> false
let (uu___is_Error_NoLetMutable : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_NoLetMutable -> true | uu____1779 -> false
let (uu___is_Error_BadImplicit : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadImplicit -> true | uu____1785 -> false
let (uu___is_Warning_DeprecatedDefinition : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedDefinition -> true
    | uu____1791 -> false
let (uu___is_Fatal_SMTEncodingArityMismatch : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SMTEncodingArityMismatch -> true
    | uu____1797 -> false
let (uu___is_Warning_Defensive : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_Defensive -> true | uu____1803 -> false
let (uu___is_Warning_CantInspect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_CantInspect -> true | uu____1809 -> false
let (uu___is_Warning_NilGivenExplicitArgs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_NilGivenExplicitArgs -> true
    | uu____1815 -> false
let (uu___is_Warning_ConsAppliedExplicitArgs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ConsAppliedExplicitArgs -> true
    | uu____1821 -> false
let (uu___is_Warning_UnembedBinderKnot : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnembedBinderKnot -> true
    | uu____1827 -> false
let (uu___is_Fatal_TacticProofRelevantGoal : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_TacticProofRelevantGoal -> true
    | uu____1833 -> false
let (uu___is_Warning_TacAdmit : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_TacAdmit -> true | uu____1839 -> false
let (uu___is_Fatal_IncoherentPatterns : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_IncoherentPatterns -> true
    | uu____1845 -> false
let (uu___is_Error_NoSMTButNeeded : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_NoSMTButNeeded -> true | uu____1851 -> false
let (uu___is_Fatal_UnexpectedAntiquotation : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_UnexpectedAntiquotation -> true
    | uu____1857 -> false
let (uu___is_Fatal_SplicedUndef : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_SplicedUndef -> true | uu____1863 -> false
let (uu___is_Fatal_SpliceUnembedFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_SpliceUnembedFail -> true
    | uu____1869 -> false
let (uu___is_Warning_ExtractionUnexpectedEffect : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_ExtractionUnexpectedEffect -> true
    | uu____1875 -> false
let (uu___is_Error_DidNotFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_DidNotFail -> true | uu____1881 -> false
let (uu___is_Warning_UnappliedFail : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnappliedFail -> true
    | uu____1887 -> false
let (uu___is_Warning_QuantifierWithoutPattern : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_QuantifierWithoutPattern -> true
    | uu____1893 -> false
let (uu___is_Error_EmptyFailErrs : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_EmptyFailErrs -> true | uu____1899 -> false
let (uu___is_Warning_logicqualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_logicqualifier -> true
    | uu____1905 -> false
let (uu___is_Fatal_CyclicDependence : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_CyclicDependence -> true
    | uu____1911 -> false
let (uu___is_Error_InductiveAnnotNotAType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_InductiveAnnotNotAType -> true
    | uu____1917 -> false
let (uu___is_Fatal_FriendInterface : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_FriendInterface -> true
    | uu____1923 -> false
let (uu___is_Error_CannotRedefineConst : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_CannotRedefineConst -> true
    | uu____1929 -> false
let (uu___is_Error_BadClassDecl : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_BadClassDecl -> true | uu____1935 -> false
let (uu___is_Error_BadInductiveParam : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_BadInductiveParam -> true
    | uu____1941 -> false
let (uu___is_Error_FieldShadow : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_FieldShadow -> true | uu____1947 -> false
let (uu___is_Error_UnexpectedDM4FType : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_UnexpectedDM4FType -> true
    | uu____1953 -> false
let (uu___is_Fatal_EffectAbbreviationResultTypeMismatch :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EffectAbbreviationResultTypeMismatch -> true
    | uu____1959 -> false
let (uu___is_Error_AlreadyCachedAssertionFailure : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_AlreadyCachedAssertionFailure -> true
    | uu____1965 -> false
let (uu___is_Error_MustEraseMissing : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Error_MustEraseMissing -> true
    | uu____1971 -> false
let (uu___is_Warning_EffectfulArgumentToErasedFunction :
  raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_EffectfulArgumentToErasedFunction -> true
    | uu____1977 -> false
let (uu___is_Fatal_EmptySurfaceLet : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_EmptySurfaceLet -> true
    | uu____1983 -> false
let (uu___is_Warning_UnexpectedCheckedFile : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_UnexpectedCheckedFile -> true
    | uu____1989 -> false
let (uu___is_Fatal_ExtractionUnsupported : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_ExtractionUnsupported -> true
    | uu____1995 -> false
let (uu___is_Warning_SMTErrorReason : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_SMTErrorReason -> true
    | uu____2001 -> false
let (uu___is_Warning_CoercionNotFound : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_CoercionNotFound -> true
    | uu____2007 -> false
let (uu___is_Error_QuakeFailed : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_QuakeFailed -> true | uu____2013 -> false
let (uu___is_Error_IllSMTPat : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IllSMTPat -> true | uu____2019 -> false
let (uu___is_Error_IllScopedTerm : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Error_IllScopedTerm -> true | uu____2025 -> false
let (uu___is_Warning_UnusedLetRec : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_UnusedLetRec -> true | uu____2031 -> false
let (uu___is_Fatal_Effects_Ordering_Coherence : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Fatal_Effects_Ordering_Coherence -> true
    | uu____2037 -> false
let (uu___is_Warning_BleedingEdge_Feature : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_BleedingEdge_Feature -> true
    | uu____2043 -> false
let (uu___is_Warning_IgnoredBinding : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_IgnoredBinding -> true
    | uu____2049 -> false
let (uu___is_Warning_AbstractQualifier : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_AbstractQualifier -> true
    | uu____2055 -> false
let (uu___is_Warning_CouldNotReadHints : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_CouldNotReadHints -> true
    | uu____2061 -> false
let (uu___is_Fatal_BadUvar : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Fatal_BadUvar -> true | uu____2067 -> false
let (uu___is_Warning_WarnOnUse : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning_WarnOnUse -> true | uu____2073 -> false
let (uu___is_Warning_DeprecatedAttributeSyntax : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedAttributeSyntax -> true
    | uu____2079 -> false
let (uu___is_Warning_DeprecatedGeneric : raw_error -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Warning_DeprecatedGeneric -> true
    | uu____2085 -> false
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
  (Warning_AbstractQualifier, CWarning, (Prims.of_int (332)));
  (Warning_CouldNotReadHints, CWarning, (Prims.of_int (333)));
  (Fatal_BadUvar, CFatal, (Prims.of_int (334)));
  (Warning_WarnOnUse, CSilent, (Prims.of_int (335)));
  (Warning_DeprecatedAttributeSyntax, CSilent, (Prims.of_int (336)));
  (Warning_DeprecatedGeneric, CWarning, (Prims.of_int (337)))]
let lookup_error :
  'uuuuuu2104 'uuuuuu2105 'uuuuuu2106 .
    ('uuuuuu2104 * 'uuuuuu2105 * 'uuuuuu2106) Prims.list ->
      'uuuuuu2104 -> ('uuuuuu2104 * 'uuuuuu2105 * 'uuuuuu2106)
  =
  fun settings ->
    fun e ->
      let uu____2139 =
        FStar_Util.try_find
          (fun uu____2158 ->
             match uu____2158 with | (v, uu____2166, i) -> e = v) settings in
      match uu____2139 with
      | FStar_Pervasives_Native.Some i -> i
      | FStar_Pervasives_Native.None ->
          failwith "Impossible: unrecognized error"
let lookup_error_range :
  'uuuuuu2207 'uuuuuu2208 .
    ('uuuuuu2207 * 'uuuuuu2208 * Prims.int) Prims.list ->
      (Prims.int * Prims.int) ->
        ('uuuuuu2207 * 'uuuuuu2208 * Prims.int) Prims.list
  =
  fun settings ->
    fun uu____2238 ->
      match uu____2238 with
      | (l, h) ->
          let uu____2253 =
            FStar_List.partition
              (fun uu____2284 ->
                 match uu____2284 with
                 | (uu____2291, uu____2292, i) -> (l <= i) && (i <= h))
              settings in
          (match uu____2253 with | (matches, uu____2303) -> matches)
let error_number :
  'uuuuuu2344 'uuuuuu2345 'uuuuuu2346 .
    ('uuuuuu2344 * 'uuuuuu2345 * 'uuuuuu2346) -> 'uuuuuu2346
  =
  fun uu____2357 -> match uu____2357 with | (uu____2364, uu____2365, i) -> i
let (warn_on_use_errno : Prims.int) =
  let uu____2367 = lookup_error default_settings Warning_WarnOnUse in
  error_number uu____2367
let (defensive_errno : Prims.int) =
  let uu____2374 = lookup_error default_settings Warning_Defensive in
  error_number uu____2374
let (update_flags :
  (error_flag * Prims.string) Prims.list -> error_setting Prims.list) =
  fun l ->
    let set_one_flag i flag1 default_flag =
      match (flag1, default_flag) with
      | (CWarning, CAlwaysError) ->
          let uu____2418 =
            let uu____2419 =
              let uu____2420 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot turn error %s into warning"
                uu____2420 in
            Invalid_warn_error_setting uu____2419 in
          FStar_Exn.raise uu____2418
      | (CError, CAlwaysError) ->
          let uu____2421 =
            let uu____2422 =
              let uu____2423 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot turn error %s into warning"
                uu____2423 in
            Invalid_warn_error_setting uu____2422 in
          FStar_Exn.raise uu____2421
      | (CSilent, CAlwaysError) ->
          let uu____2424 =
            let uu____2425 =
              let uu____2426 = FStar_Util.string_of_int i in
              FStar_Util.format1 "cannot silence error %s" uu____2426 in
            Invalid_warn_error_setting uu____2425 in
          FStar_Exn.raise uu____2424
      | (uu____2427, CFatal) ->
          let uu____2428 =
            let uu____2429 =
              let uu____2430 = FStar_Util.string_of_int i in
              FStar_Util.format1
                "cannot change the error level of fatal error %s" uu____2430 in
            Invalid_warn_error_setting uu____2429 in
          FStar_Exn.raise uu____2428
      | uu____2431 -> flag1 in
    let set_flag_for_range uu____2457 =
      match uu____2457 with
      | (flag1, range) ->
          let errs = lookup_error_range default_settings range in
          FStar_List.map
            (fun uu____2510 ->
               match uu____2510 with
               | (v, default_flag, i) ->
                   let uu____2526 = set_one_flag i flag1 default_flag in
                   (v, uu____2526, i)) errs in
    let compute_range uu____2544 =
      match uu____2544 with
      | (flag1, s) ->
          let r = FStar_Util.split s ".." in
          let uu____2562 =
            match r with
            | r1::r2::[] ->
                let uu____2573 = FStar_Util.int_of_string r1 in
                let uu____2574 = FStar_Util.int_of_string r2 in
                (uu____2573, uu____2574)
            | uu____2575 ->
                let uu____2578 =
                  let uu____2579 =
                    FStar_Util.format1 "Malformed warn-error range %s" s in
                  Invalid_warn_error_setting uu____2579 in
                FStar_Exn.raise uu____2578 in
          (match uu____2562 with | (l1, h) -> (flag1, (l1, h))) in
    let error_range_settings = FStar_List.map compute_range l in
    let uu____2621 =
      FStar_List.collect set_flag_for_range error_range_settings in
    FStar_List.append uu____2621 default_settings
type error = (raw_error * Prims.string * FStar_Range.range)
exception Err of (raw_error * Prims.string) 
let (uu___is_Err : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Err uu____2669 -> true | uu____2674 -> false
let (__proj__Err__item__uu___ : Prims.exn -> (raw_error * Prims.string)) =
  fun projectee -> match projectee with | Err uu____2688 -> uu____2688
exception Error of error 
let (uu___is_Error : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Error uu____2702 -> true | uu____2703 -> false
let (__proj__Error__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Error uu____2709 -> uu____2709
exception Warning of error 
let (uu___is_Warning : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Warning uu____2719 -> true | uu____2720 -> false
let (__proj__Warning__item__uu___ : Prims.exn -> error) =
  fun projectee -> match projectee with | Warning uu____2726 -> uu____2726
exception Stop 
let (uu___is_Stop : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Stop -> true | uu____2732 -> false
exception Empty_frag 
let (uu___is_Empty_frag : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Empty_frag -> true | uu____2738 -> false
type issue_level =
  | ENotImplemented 
  | EInfo 
  | EWarning 
  | EError 
let (uu___is_ENotImplemented : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | ENotImplemented -> true | uu____2744 -> false
let (uu___is_EInfo : issue_level -> Prims.bool) =
  fun projectee -> match projectee with | EInfo -> true | uu____2750 -> false
let (uu___is_EWarning : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | EWarning -> true | uu____2756 -> false
let (uu___is_EError : issue_level -> Prims.bool) =
  fun projectee ->
    match projectee with | EError -> true | uu____2762 -> false
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
    let uu____3019 =
      match issue1.issue_range with
      | FStar_Pervasives_Native.None -> ("", "")
      | FStar_Pervasives_Native.Some r when r = FStar_Range.dummyRange ->
          let uu____3029 =
            let uu____3030 =
              let uu____3031 = FStar_Range.def_range r in
              let uu____3032 = FStar_Range.def_range FStar_Range.dummyRange in
              uu____3031 = uu____3032 in
            if uu____3030
            then ""
            else
              (let uu____3034 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____3034) in
          ("", uu____3029)
      | FStar_Pervasives_Native.Some r ->
          let uu____3036 =
            let uu____3037 = FStar_Range.string_of_use_range r in
            FStar_Util.format1 "%s: " uu____3037 in
          let uu____3038 =
            let uu____3039 =
              (let uu____3044 = FStar_Range.use_range r in
               let uu____3045 = FStar_Range.def_range r in
               uu____3044 = uu____3045) ||
                (let uu____3048 = FStar_Range.def_range r in
                 let uu____3049 =
                   FStar_Range.def_range FStar_Range.dummyRange in
                 uu____3048 = uu____3049) in
            if uu____3039
            then ""
            else
              (let uu____3051 = FStar_Range.string_of_range r in
               FStar_Util.format1 " (see also %s)" uu____3051) in
          (uu____3036, uu____3038) in
    match uu____3019 with
    | (range_str, see_also_str) ->
        let issue_number =
          match issue1.issue_number with
          | FStar_Pervasives_Native.None -> ""
          | FStar_Pervasives_Native.Some n ->
              let uu____3056 = FStar_Util.string_of_int n in
              FStar_Util.format1 " %s" uu____3056 in
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
    let uu____3070 = format_issue issue1 in printer uu____3070
let (compare_issues : issue -> issue -> Prims.int) =
  fun i1 ->
    fun i2 ->
      match ((i1.issue_range), (i2.issue_range)) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          Prims.int_zero
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some
         uu____3089) -> ~- Prims.int_one
      | (FStar_Pervasives_Native.Some uu____3094,
         FStar_Pervasives_Native.None) -> Prims.int_one
      | (FStar_Pervasives_Native.Some r1, FStar_Pervasives_Native.Some r2) ->
          FStar_Range.compare_use_range r1 r2
let (mk_default_handler : Prims.bool -> error_handler) =
  fun print ->
    let issues = FStar_Util.mk_ref [] in
    let add_one e =
      (let uu____3124 =
         (FStar_Options.defensive_abort ()) &&
           (e.issue_number = (FStar_Pervasives_Native.Some defensive_errno)) in
       if uu____3124
       then failwith "Aborting due to --defensive abort"
       else ());
      (match e.issue_level with
       | EInfo -> print_issue e
       | uu____3128 ->
           let uu____3129 =
             let uu____3132 = FStar_ST.op_Bang issues in e :: uu____3132 in
           FStar_ST.op_Colon_Equals issues uu____3129) in
    let count_errors uu____3160 =
      let uu____3161 = FStar_ST.op_Bang issues in
      FStar_List.fold_left
        (fun n ->
           fun i ->
             match i.issue_level with
             | EError -> n + Prims.int_one
             | uu____3178 -> n) Prims.int_zero uu____3161 in
    let report uu____3186 =
      let unique_issues =
        let uu____3190 = FStar_ST.op_Bang issues in
        FStar_Util.remove_dups (fun i0 -> fun i1 -> i0 = i1) uu____3190 in
      let sorted_unique_issues =
        FStar_List.sortWith compare_issues unique_issues in
      if print then FStar_List.iter print_issue sorted_unique_issues else ();
      sorted_unique_issues in
    let clear uu____3217 = FStar_ST.op_Colon_Equals issues [] in
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
  fun uu____3262 ->
    let uu____3263 =
      let uu____3268 = FStar_ST.op_Bang current_handler in
      uu____3268.eh_count_errors in
    uu____3263 ()
let (wrapped_eh_add_one : error_handler -> issue -> unit) =
  fun h ->
    fun issue1 ->
      h.eh_add_one issue1;
      if issue1.issue_level <> EInfo
      then
        ((let uu____3287 =
            let uu____3288 = FStar_ST.op_Bang FStar_Options.abort_counter in
            uu____3288 - Prims.int_one in
          FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____3287);
         (let uu____3301 =
            let uu____3302 = FStar_ST.op_Bang FStar_Options.abort_counter in
            uu____3302 = Prims.int_zero in
          if uu____3301 then failwith "Aborting due to --abort_on" else ()))
      else ()
let (add_one : issue -> unit) =
  fun issue1 ->
    FStar_Util.atomically
      (fun uu____3318 ->
         let uu____3319 = FStar_ST.op_Bang current_handler in
         wrapped_eh_add_one uu____3319 issue1)
let (add_many : issue Prims.list -> unit) =
  fun issues ->
    FStar_Util.atomically
      (fun uu____3337 ->
         let uu____3338 =
           let uu____3343 = FStar_ST.op_Bang current_handler in
           wrapped_eh_add_one uu____3343 in
         FStar_List.iter uu____3338 issues)
let (report_all : unit -> issue Prims.list) =
  fun uu____3356 ->
    let uu____3357 =
      let uu____3364 = FStar_ST.op_Bang current_handler in
      uu____3364.eh_report in
    uu____3357 ()
let (clear : unit -> unit) =
  fun uu____3375 ->
    let uu____3376 =
      let uu____3381 = FStar_ST.op_Bang current_handler in
      uu____3381.eh_clear in
    uu____3376 ()
let (set_handler : error_handler -> unit) =
  fun handler ->
    let issues = report_all () in
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
  fun projectee ->
    match projectee with
    | { set_prefix; append_prefix; clear_prefix;_} -> set_prefix
let (__proj__Mkerror_message_prefix__item__append_prefix :
  error_message_prefix -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { set_prefix; append_prefix; clear_prefix;_} -> append_prefix
let (__proj__Mkerror_message_prefix__item__clear_prefix :
  error_message_prefix -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { set_prefix; append_prefix; clear_prefix;_} -> clear_prefix
let (message_prefix : error_message_prefix) =
  let pfx = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_prefix s =
    FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some s) in
  let clear_prefix uu____3534 =
    FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None in
  let append_prefix s =
    let uu____3551 = FStar_ST.op_Bang pfx in
    match uu____3551 with
    | FStar_Pervasives_Native.None -> s
    | FStar_Pervasives_Native.Some p ->
        let uu____3565 = FStar_String.op_Hat ": " s in
        FStar_String.op_Hat p uu____3565 in
  { set_prefix; append_prefix; clear_prefix }
let (diag : FStar_Range.range -> Prims.string -> unit) =
  fun r ->
    fun msg ->
      let uu____3576 = FStar_Options.debug_any () in
      if uu____3576
      then
        add_one
          (mk_issue EInfo (FStar_Pervasives_Native.Some r) msg
             FStar_Pervasives_Native.None)
      else ()
let (warn_unsafe_options :
  FStar_Range.range FStar_Pervasives_Native.option -> Prims.string -> unit) =
  fun rng_opt ->
    fun msg ->
      let uu____3592 = FStar_Options.report_assumes () in
      match uu____3592 with
      | FStar_Pervasives_Native.Some "warn" ->
          let uu____3595 =
            let uu____3596 =
              FStar_String.op_Hat
                "Every use of this option triggers a warning: " msg in
            mk_issue EWarning rng_opt uu____3596
              (FStar_Pervasives_Native.Some warn_on_use_errno) in
          add_one uu____3595
      | FStar_Pervasives_Native.Some "error" ->
          let uu____3597 =
            let uu____3598 =
              FStar_String.op_Hat
                "Every use of this option triggers an error: " msg in
            mk_issue EError rng_opt uu____3598
              (FStar_Pervasives_Native.Some warn_on_use_errno) in
          add_one uu____3597
      | uu____3599 -> ()
let (set_option_warning_callback_range :
  FStar_Range.range FStar_Pervasives_Native.option -> unit) =
  fun ropt ->
    FStar_Options.set_option_warning_callback (warn_unsafe_options ropt)
let (uu___213 :
  (((Prims.string -> error_setting Prims.list) -> unit) *
    (unit -> error_setting Prims.list)))
  =
  let parser_callback = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let error_flags = FStar_Util.smap_create (Prims.of_int (10)) in
  let set_error_flags uu____3666 =
    let parse s =
      let uu____3675 = FStar_ST.op_Bang parser_callback in
      match uu____3675 with
      | FStar_Pervasives_Native.None ->
          failwith "Callback for parsing warn_error strings is not set"
      | FStar_Pervasives_Native.Some f -> f s in
    let we = FStar_Options.warn_error () in
    try
      (fun uu___225_3727 ->
         match () with
         | () ->
             let r = parse we in
             (FStar_Util.smap_add error_flags we
                (FStar_Pervasives_Native.Some r);
              FStar_Getopt.Success)) ()
    with
    | Invalid_warn_error_setting msg ->
        (FStar_Util.smap_add error_flags we FStar_Pervasives_Native.None;
         (let uu____3751 =
            FStar_String.op_Hat "Invalid --warn_error setting: " msg in
          FStar_Getopt.Error uu____3751)) in
  let get_error_flags uu____3759 =
    let we = FStar_Options.warn_error () in
    let uu____3761 = FStar_Util.smap_try_find error_flags we in
    match uu____3761 with
    | FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some w) -> w
    | uu____3783 -> default_settings in
  let set_callbacks f =
    FStar_ST.op_Colon_Equals parser_callback (FStar_Pervasives_Native.Some f);
    FStar_Options.set_error_flags_callback set_error_flags;
    FStar_Options.set_option_warning_callback
      (warn_unsafe_options FStar_Pervasives_Native.None) in
  (set_callbacks, get_error_flags)
let (set_parse_warn_error :
  (Prims.string -> error_setting Prims.list) -> unit) =
  match uu___213 with
  | (set_parse_warn_error, error_flags) -> set_parse_warn_error
let (error_flags : unit -> error_setting Prims.list) =
  match uu___213 with | (set_parse_warn_error1, error_flags) -> error_flags
let (lookup : raw_error -> (raw_error * error_flag * Prims.int)) =
  fun err ->
    let flags = error_flags () in
    let uu____3943 = lookup_error flags err in
    match uu____3943 with
    | (v, level, i) ->
        let with_level level1 = (v, level1, i) in
        (match v with
         | Warning_Defensive when
             (FStar_Options.defensive_error ()) ||
               (FStar_Options.defensive_abort ())
             -> with_level CAlwaysError
         | Warning_WarnOnUse ->
             let level' =
               let uu____3978 = FStar_Options.report_assumes () in
               match uu____3978 with
               | FStar_Pervasives_Native.None -> level
               | FStar_Pervasives_Native.Some "warn" ->
                   (match level with
                    | CSilent -> CWarning
                    | uu____3981 -> level)
               | FStar_Pervasives_Native.Some "error" ->
                   (match level with
                    | CWarning -> CError
                    | CSilent -> CError
                    | uu____3982 -> level)
               | FStar_Pervasives_Native.Some uu____3983 -> level in
             with_level level'
         | uu____3984 -> with_level level)
let (log_issue : FStar_Range.range -> (raw_error * Prims.string) -> unit) =
  fun r ->
    fun uu____3998 ->
      match uu____3998 with
      | (e, msg) ->
          let uu____4005 = lookup e in
          (match uu____4005 with
           | (uu____4012, CAlwaysError, errno) ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | (uu____4014, CError, errno) ->
               add_one
                 (mk_issue EError (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | (uu____4016, CWarning, errno) ->
               add_one
                 (mk_issue EWarning (FStar_Pervasives_Native.Some r) msg
                    (FStar_Pervasives_Native.Some errno))
           | (uu____4018, CSilent, uu____4019) -> ()
           | (uu____4020, CFatal, errno) ->
               let i =
                 mk_issue EError (FStar_Pervasives_Native.Some r) msg
                   (FStar_Pervasives_Native.Some errno) in
               let uu____4023 = FStar_Options.ide () in
               if uu____4023
               then add_one i
               else
                 (let uu____4025 =
                    let uu____4026 = format_issue i in
                    FStar_String.op_Hat
                      "don't use log_issue to report fatal error, should use raise_error: "
                      uu____4026 in
                  failwith uu____4025))
let (add_errors :
  (raw_error * Prims.string * FStar_Range.range) Prims.list -> unit) =
  fun errs ->
    FStar_Util.atomically
      (fun uu____4049 ->
         FStar_List.iter
           (fun uu____4061 ->
              match uu____4061 with
              | (e, msg, r) ->
                  let uu____4071 =
                    let uu____4076 = message_prefix.append_prefix msg in
                    (e, uu____4076) in
                  log_issue r uu____4071) errs)
let (issue_of_exn : Prims.exn -> issue FStar_Pervasives_Native.option) =
  fun uu___0_4083 ->
    match uu___0_4083 with
    | Error (e, msg, r) ->
        let errno = let uu____4090 = lookup e in error_number uu____4090 in
        let uu____4097 =
          let uu____4098 = message_prefix.append_prefix msg in
          mk_issue EError (FStar_Pervasives_Native.Some r) uu____4098
            (FStar_Pervasives_Native.Some errno) in
        FStar_Pervasives_Native.Some uu____4097
    | Err (e, msg) ->
        let errno = let uu____4102 = lookup e in error_number uu____4102 in
        let uu____4109 =
          let uu____4110 = message_prefix.append_prefix msg in
          mk_issue EError FStar_Pervasives_Native.None uu____4110
            (FStar_Pervasives_Native.Some errno) in
        FStar_Pervasives_Native.Some uu____4109
    | uu____4111 -> FStar_Pervasives_Native.None
let (err_exn : Prims.exn -> unit) =
  fun exn ->
    if exn = Stop
    then ()
    else
      (let uu____4118 = issue_of_exn exn in
       match uu____4118 with
       | FStar_Pervasives_Native.Some issue1 -> add_one issue1
       | FStar_Pervasives_Native.None -> FStar_Exn.raise exn)
let (handleable : Prims.exn -> Prims.bool) =
  fun uu___1_4126 ->
    match uu___1_4126 with
    | Error uu____4127 -> true
    | Stop -> true
    | Err uu____4128 -> true
    | uu____4133 -> false
let (stop_if_err : unit -> unit) =
  fun uu____4138 ->
    let uu____4139 =
      let uu____4140 = get_err_count () in uu____4140 > Prims.int_zero in
    if uu____4139 then FStar_Exn.raise Stop else ()
let raise_error :
  'uuuuuu4148 .
    (raw_error * Prims.string) -> FStar_Range.range -> 'uuuuuu4148
  =
  fun uu____4161 ->
    fun r ->
      match uu____4161 with | (e, msg) -> FStar_Exn.raise (Error (e, msg, r))
let raise_err : 'uuuuuu4173 . (raw_error * Prims.string) -> 'uuuuuu4173 =
  fun uu____4182 ->
    match uu____4182 with | (e, msg) -> FStar_Exn.raise (Err (e, msg))
let catch_errors :
  'a . (unit -> 'a) -> (issue Prims.list * 'a FStar_Pervasives_Native.option)
  =
  fun f ->
    let newh = mk_default_handler false in
    let old = FStar_ST.op_Bang current_handler in
    FStar_ST.op_Colon_Equals current_handler newh;
    (let r =
       try
         (fun uu___346_4234 ->
            match () with
            | () -> let r = f () in FStar_Pervasives_Native.Some r) ()
       with
       | uu___345_4240 ->
           (err_exn uu___345_4240; FStar_Pervasives_Native.None) in
     let all_issues = newh.eh_report () in
     FStar_ST.op_Colon_Equals current_handler old;
     (let uu____4254 =
        FStar_List.partition (fun i -> i.issue_level = EError) all_issues in
      match uu____4254 with
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
            let uu____4364 = collect tl in
            (match uu____4364 with
             | [] -> [(hd, Prims.int_one)]
             | (h, n)::t ->
                 if h = hd
                 then (h, (n + Prims.int_one)) :: t
                 else (hd, Prims.int_one) :: (h, n) :: t) in
      let summ l = collect l in
      let l11 = let uu____4444 = sort l1 in summ uu____4444 in
      let l21 = let uu____4454 = sort l2 in summ uu____4454 in
      let rec aux l12 l22 =
        match (l12, l22) with
        | ([], []) -> FStar_Pervasives_Native.None
        | ((e, n)::uu____4548, []) ->
            FStar_Pervasives_Native.Some (e, n, Prims.int_zero)
        | ([], (e, n)::uu____4583) ->
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