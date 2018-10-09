
open Prims
open FStar_Pervasives
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


let uu___is_Error_DependencyAnalysisFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_DependencyAnalysisFailed -> begin
true
end
| uu____6 -> begin
false
end))


let uu___is_Error_IDETooManyPops : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDETooManyPops -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Error_IDEUnrecognized : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDEUnrecognized -> begin
true
end
| uu____18 -> begin
false
end))


let uu___is_Error_InductiveTypeNotSatisfyPositivityCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InductiveTypeNotSatisfyPositivityCondition -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Error_InvalidUniverseVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InvalidUniverseVar -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_Error_MissingFileName : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_MissingFileName -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_Error_ModuleFileNameMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_ModuleFileNameMismatch -> begin
true
end
| uu____42 -> begin
false
end))


let uu___is_Error_OpPlusInUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_OpPlusInUniverse -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_Error_OutOfRange : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_OutOfRange -> begin
true
end
| uu____54 -> begin
false
end))


let uu___is_Error_ProofObligationFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_ProofObligationFailed -> begin
true
end
| uu____60 -> begin
false
end))


let uu___is_Error_TooManyFiles : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TooManyFiles -> begin
true
end
| uu____66 -> begin
false
end))


let uu___is_Error_TypeCheckerFailToProve : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TypeCheckerFailToProve -> begin
true
end
| uu____72 -> begin
false
end))


let uu___is_Error_TypeError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TypeError -> begin
true
end
| uu____78 -> begin
false
end))


let uu___is_Error_UncontrainedUnificationVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UncontrainedUnificationVar -> begin
true
end
| uu____84 -> begin
false
end))


let uu___is_Error_UnexpectedGTotComputation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedGTotComputation -> begin
true
end
| uu____90 -> begin
false
end))


let uu___is_Error_UnexpectedInstance : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedInstance -> begin
true
end
| uu____96 -> begin
false
end))


let uu___is_Error_UnknownFatal_AssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnknownFatal_AssertionFailure -> begin
true
end
| uu____102 -> begin
false
end))


let uu___is_Error_Z3InvocationError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_Z3InvocationError -> begin
true
end
| uu____108 -> begin
false
end))


let uu___is_Error_IDEAssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDEAssertionFailure -> begin
true
end
| uu____114 -> begin
false
end))


let uu___is_Error_Z3SolverError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_Z3SolverError -> begin
true
end
| uu____120 -> begin
false
end))


let uu___is_Fatal_AbstractTypeDeclarationInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AbstractTypeDeclarationInInterface -> begin
true
end
| uu____126 -> begin
false
end))


let uu___is_Fatal_ActionMustHaveFunctionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ActionMustHaveFunctionType -> begin
true
end
| uu____132 -> begin
false
end))


let uu___is_Fatal_AlreadyDefinedTopLevelDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AlreadyDefinedTopLevelDeclaration -> begin
true
end
| uu____138 -> begin
false
end))


let uu___is_Fatal_ArgumentLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ArgumentLengthMismatch -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_Fatal_AssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssertionFailure -> begin
true
end
| uu____150 -> begin
false
end))


let uu___is_Fatal_AssignToImmutableValues : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssignToImmutableValues -> begin
true
end
| uu____156 -> begin
false
end))


let uu___is_Fatal_AssumeValInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssumeValInInterface -> begin
true
end
| uu____162 -> begin
false
end))


let uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BadlyInstantiatedSynthByTactic -> begin
true
end
| uu____168 -> begin
false
end))


let uu___is_Fatal_BadSignatureShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BadSignatureShape -> begin
true
end
| uu____174 -> begin
false
end))


let uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BinderAndArgsLengthMismatch -> begin
true
end
| uu____180 -> begin
false
end))


let uu___is_Fatal_BothValAndLetInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BothValAndLetInInterface -> begin
true
end
| uu____186 -> begin
false
end))


let uu___is_Fatal_CardinalityConstraintViolated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CardinalityConstraintViolated -> begin
true
end
| uu____192 -> begin
false
end))


let uu___is_Fatal_ComputationNotTotal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputationNotTotal -> begin
true
end
| uu____198 -> begin
false
end))


let uu___is_Fatal_ComputationTypeNotAllowed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputationTypeNotAllowed -> begin
true
end
| uu____204 -> begin
false
end))


let uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputedTypeNotMatchAnnotation -> begin
true
end
| uu____210 -> begin
false
end))


let uu___is_Fatal_ConstructorArgLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorArgLengthMismatch -> begin
true
end
| uu____216 -> begin
false
end))


let uu___is_Fatal_ConstructorFailedCheck : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorFailedCheck -> begin
true
end
| uu____222 -> begin
false
end))


let uu___is_Fatal_ConstructorNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorNotFound -> begin
true
end
| uu____228 -> begin
false
end))


let uu___is_Fatal_ConstsructorBuildWrongType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstsructorBuildWrongType -> begin
true
end
| uu____234 -> begin
false
end))


let uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CycleInRecTypeAbbreviation -> begin
true
end
| uu____240 -> begin
false
end))


let uu___is_Fatal_DataContructorNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DataContructorNotFound -> begin
true
end
| uu____246 -> begin
false
end))


let uu___is_Fatal_DefaultQualifierNotAllowedOnEffects : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DefaultQualifierNotAllowedOnEffects -> begin
true
end
| uu____252 -> begin
false
end))


let uu___is_Fatal_DefinitionNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DefinitionNotFound -> begin
true
end
| uu____258 -> begin
false
end))


let uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DisjuctivePatternVarsMismatch -> begin
true
end
| uu____264 -> begin
false
end))


let uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DivergentComputationCannotBeIncludedInTotal -> begin
true
end
| uu____270 -> begin
false
end))


let uu___is_Fatal_DuplicateInImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateInImplementation -> begin
true
end
| uu____276 -> begin
false
end))


let uu___is_Fatal_DuplicateModuleOrInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateModuleOrInterface -> begin
true
end
| uu____282 -> begin
false
end))


let uu___is_Fatal_DuplicateTopLevelNames : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateTopLevelNames -> begin
true
end
| uu____288 -> begin
false
end))


let uu___is_Fatal_DuplicateTypeAnnotationAndValDecl : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateTypeAnnotationAndValDecl -> begin
true
end
| uu____294 -> begin
false
end))


let uu___is_Fatal_EffectCannotBeReified : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectCannotBeReified -> begin
true
end
| uu____300 -> begin
false
end))


let uu___is_Fatal_EffectConstructorNotFullyApplied : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectConstructorNotFullyApplied -> begin
true
end
| uu____306 -> begin
false
end))


let uu___is_Fatal_EffectfulAndPureComputationMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectfulAndPureComputationMismatch -> begin
true
end
| uu____312 -> begin
false
end))


let uu___is_Fatal_EffectNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectNotFound -> begin
true
end
| uu____318 -> begin
false
end))


let uu___is_Fatal_EffectsCannotBeComposed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectsCannotBeComposed -> begin
true
end
| uu____324 -> begin
false
end))


let uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ErrorInSolveDeferredConstraints -> begin
true
end
| uu____330 -> begin
false
end))


let uu___is_Fatal_ErrorsReported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ErrorsReported -> begin
true
end
| uu____336 -> begin
false
end))


let uu___is_Fatal_EscapedBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EscapedBoundVar -> begin
true
end
| uu____342 -> begin
false
end))


let uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedArrowAnnotatedType -> begin
true
end
| uu____348 -> begin
false
end))


let uu___is_Fatal_ExpectedGhostExpression : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedGhostExpression -> begin
true
end
| uu____354 -> begin
false
end))


let uu___is_Fatal_ExpectedPureExpression : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedPureExpression -> begin
true
end
| uu____360 -> begin
false
end))


let uu___is_Fatal_ExpectNormalizedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectNormalizedEffect -> begin
true
end
| uu____366 -> begin
false
end))


let uu___is_Fatal_ExpectTermGotFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectTermGotFunction -> begin
true
end
| uu____372 -> begin
false
end))


let uu___is_Fatal_ExpectTrivialPreCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectTrivialPreCondition -> begin
true
end
| uu____378 -> begin
false
end))


let uu___is_Fatal_FailToCompileNativeTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToCompileNativeTactic -> begin
true
end
| uu____384 -> begin
false
end))


let uu___is_Fatal_FailToExtractNativeTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToExtractNativeTactic -> begin
true
end
| uu____390 -> begin
false
end))


let uu___is_Fatal_FailToProcessPragma : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToProcessPragma -> begin
true
end
| uu____396 -> begin
false
end))


let uu___is_Fatal_FailToResolveImplicitArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToResolveImplicitArgument -> begin
true
end
| uu____402 -> begin
false
end))


let uu___is_Fatal_FailToSolveUniverseInEquality : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToSolveUniverseInEquality -> begin
true
end
| uu____408 -> begin
false
end))


let uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FieldsNotBelongToSameRecordType -> begin
true
end
| uu____414 -> begin
false
end))


let uu___is_Fatal_ForbiddenReferenceToCurrentModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ForbiddenReferenceToCurrentModule -> begin
true
end
| uu____420 -> begin
false
end))


let uu___is_Fatal_FreeVariables : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FreeVariables -> begin
true
end
| uu____426 -> begin
false
end))


let uu___is_Fatal_FunctionTypeExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FunctionTypeExpected -> begin
true
end
| uu____432 -> begin
false
end))


let uu___is_Fatal_IdentifierNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IdentifierNotFound -> begin
true
end
| uu____438 -> begin
false
end))


let uu___is_Fatal_IllAppliedConstant : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllAppliedConstant -> begin
true
end
| uu____444 -> begin
false
end))


let uu___is_Fatal_IllegalCharInByteArray : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllegalCharInByteArray -> begin
true
end
| uu____450 -> begin
false
end))


let uu___is_Fatal_IllegalCharInOperatorName : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllegalCharInOperatorName -> begin
true
end
| uu____456 -> begin
false
end))


let uu___is_Fatal_IllTyped : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllTyped -> begin
true
end
| uu____462 -> begin
false
end))


let uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleAbbrevLidBundle -> begin
true
end
| uu____468 -> begin
false
end))


let uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleAbbrevRenameBundle -> begin
true
end
| uu____474 -> begin
false
end))


let uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleInductiveWithAbbrev -> begin
true
end
| uu____480 -> begin
false
end))


let uu___is_Fatal_ImpossiblePrePostAbs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossiblePrePostAbs -> begin
true
end
| uu____486 -> begin
false
end))


let uu___is_Fatal_ImpossiblePrePostArrow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossiblePrePostArrow -> begin
true
end
| uu____492 -> begin
false
end))


let uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleToGenerateDMEffect -> begin
true
end
| uu____498 -> begin
false
end))


let uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleTypeAbbrevBundle -> begin
true
end
| uu____504 -> begin
false
end))


let uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleTypeAbbrevSigeltBundle -> begin
true
end
| uu____510 -> begin
false
end))


let uu___is_Fatal_IncludeModuleNotPrepared : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncludeModuleNotPrepared -> begin
true
end
| uu____516 -> begin
false
end))


let uu___is_Fatal_IncoherentInlineUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncoherentInlineUniverse -> begin
true
end
| uu____522 -> begin
false
end))


let uu___is_Fatal_IncompatibleKinds : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleKinds -> begin
true
end
| uu____528 -> begin
false
end))


let uu___is_Fatal_IncompatibleNumberOfTypes : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleNumberOfTypes -> begin
true
end
| uu____534 -> begin
false
end))


let uu___is_Fatal_IncompatibleSetOfUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleSetOfUniverse -> begin
true
end
| uu____540 -> begin
false
end))


let uu___is_Fatal_IncompatibleUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleUniverse -> begin
true
end
| uu____546 -> begin
false
end))


let uu___is_Fatal_InconsistentImplicitArgumentAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentImplicitArgumentAnnotation -> begin
true
end
| uu____552 -> begin
false
end))


let uu___is_Fatal_InconsistentImplicitQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentImplicitQualifier -> begin
true
end
| uu____558 -> begin
false
end))


let uu___is_Fatal_InconsistentQualifierAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentQualifierAnnotation -> begin
true
end
| uu____564 -> begin
false
end))


let uu___is_Fatal_InferredTypeCauseVarEscape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InferredTypeCauseVarEscape -> begin
true
end
| uu____570 -> begin
false
end))


let uu___is_Fatal_InlineRenamedAsUnfold : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InlineRenamedAsUnfold -> begin
true
end
| uu____576 -> begin
false
end))


let uu___is_Fatal_InsufficientPatternArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InsufficientPatternArguments -> begin
true
end
| uu____582 -> begin
false
end))


let uu___is_Fatal_InterfaceAlreadyProcessed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceAlreadyProcessed -> begin
true
end
| uu____588 -> begin
false
end))


let uu___is_Fatal_InterfaceNotImplementedByModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceNotImplementedByModule -> begin
true
end
| uu____594 -> begin
false
end))


let uu___is_Fatal_InterfaceWithTypeImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceWithTypeImplementation -> begin
true
end
| uu____600 -> begin
false
end))


let uu___is_Fatal_InvalidFloatingPointNumber : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidFloatingPointNumber -> begin
true
end
| uu____606 -> begin
false
end))


let uu___is_Fatal_InvalidFSDocKeyword : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidFSDocKeyword -> begin
true
end
| uu____612 -> begin
false
end))


let uu___is_Fatal_InvalidIdentifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidIdentifier -> begin
true
end
| uu____618 -> begin
false
end))


let uu___is_Fatal_InvalidLemmaArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidLemmaArgument -> begin
true
end
| uu____624 -> begin
false
end))


let uu___is_Fatal_InvalidNumericLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidNumericLiteral -> begin
true
end
| uu____630 -> begin
false
end))


let uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidRedefinitionOfLexT -> begin
true
end
| uu____636 -> begin
false
end))


let uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidUnicodeInStringLiteral -> begin
true
end
| uu____642 -> begin
false
end))


let uu___is_Fatal_InvalidUTF8Encoding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidUTF8Encoding -> begin
true
end
| uu____648 -> begin
false
end))


let uu___is_Fatal_InvalidWarnErrorSetting : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidWarnErrorSetting -> begin
true
end
| uu____654 -> begin
false
end))


let uu___is_Fatal_LetBoundMonadicMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetBoundMonadicMismatch -> begin
true
end
| uu____660 -> begin
false
end))


let uu___is_Fatal_LetMutableForVariablesOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetMutableForVariablesOnly -> begin
true
end
| uu____666 -> begin
false
end))


let uu___is_Fatal_LetOpenModuleOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetOpenModuleOnly -> begin
true
end
| uu____672 -> begin
false
end))


let uu___is_Fatal_LetRecArgumentMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetRecArgumentMismatch -> begin
true
end
| uu____678 -> begin
false
end))


let uu___is_Fatal_MalformedActionDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MalformedActionDeclaration -> begin
true
end
| uu____684 -> begin
false
end))


let uu___is_Fatal_MismatchedPatternType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MismatchedPatternType -> begin
true
end
| uu____690 -> begin
false
end))


let uu___is_Fatal_MismatchUniversePolymorphic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MismatchUniversePolymorphic -> begin
true
end
| uu____696 -> begin
false
end))


let uu___is_Fatal_MissingDataConstructor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingDataConstructor -> begin
true
end
| uu____702 -> begin
false
end))


let uu___is_Fatal_MissingExposeInterfacesOption : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingExposeInterfacesOption -> begin
true
end
| uu____708 -> begin
false
end))


let uu___is_Fatal_MissingFieldInRecord : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingFieldInRecord -> begin
true
end
| uu____714 -> begin
false
end))


let uu___is_Fatal_MissingImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingImplementation -> begin
true
end
| uu____720 -> begin
false
end))


let uu___is_Fatal_MissingImplicitArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingImplicitArguments -> begin
true
end
| uu____726 -> begin
false
end))


let uu___is_Fatal_MissingInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingInterface -> begin
true
end
| uu____732 -> begin
false
end))


let uu___is_Fatal_MissingNameInBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingNameInBinder -> begin
true
end
| uu____738 -> begin
false
end))


let uu___is_Fatal_MissingPrimsModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingPrimsModule -> begin
true
end
| uu____744 -> begin
false
end))


let uu___is_Fatal_MissingQuantifierBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingQuantifierBinder -> begin
true
end
| uu____750 -> begin
false
end))


let uu___is_Fatal_ModuleExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleExpected -> begin
true
end
| uu____756 -> begin
false
end))


let uu___is_Fatal_ModuleFileNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleFileNotFound -> begin
true
end
| uu____762 -> begin
false
end))


let uu___is_Fatal_ModuleFirstStatement : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleFirstStatement -> begin
true
end
| uu____768 -> begin
false
end))


let uu___is_Fatal_ModuleNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleNotFound -> begin
true
end
| uu____774 -> begin
false
end))


let uu___is_Fatal_ModuleOrFileNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleOrFileNotFound -> begin
true
end
| uu____780 -> begin
false
end))


let uu___is_Fatal_MonadAlreadyDefined : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MonadAlreadyDefined -> begin
true
end
| uu____786 -> begin
false
end))


let uu___is_Fatal_MoreThanOneDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MoreThanOneDeclaration -> begin
true
end
| uu____792 -> begin
false
end))


let uu___is_Fatal_MultipleLetBinding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MultipleLetBinding -> begin
true
end
| uu____798 -> begin
false
end))


let uu___is_Fatal_NameNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NameNotFound -> begin
true
end
| uu____804 -> begin
false
end))


let uu___is_Fatal_NameSpaceNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NameSpaceNotFound -> begin
true
end
| uu____810 -> begin
false
end))


let uu___is_Fatal_NegativeUniverseConstFatal_NotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NegativeUniverseConstFatal_NotSupported -> begin
true
end
| uu____816 -> begin
false
end))


let uu___is_Fatal_NoFileProvided : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NoFileProvided -> begin
true
end
| uu____822 -> begin
false
end))


let uu___is_Fatal_NonInductiveInMutuallyDefinedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonInductiveInMutuallyDefinedType -> begin
true
end
| uu____828 -> begin
false
end))


let uu___is_Fatal_NonLinearPatternNotPermitted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonLinearPatternNotPermitted -> begin
true
end
| uu____834 -> begin
false
end))


let uu___is_Fatal_NonLinearPatternVars : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonLinearPatternVars -> begin
true
end
| uu____840 -> begin
false
end))


let uu___is_Fatal_NonSingletonTopLevel : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonSingletonTopLevel -> begin
true
end
| uu____846 -> begin
false
end))


let uu___is_Fatal_NonSingletonTopLevelModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonSingletonTopLevelModule -> begin
true
end
| uu____852 -> begin
false
end))


let uu___is_Fatal_NonTopRecFunctionNotFullyEncoded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonTopRecFunctionNotFullyEncoded -> begin
true
end
| uu____858 -> begin
false
end))


let uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonTrivialPreConditionInPrims -> begin
true
end
| uu____864 -> begin
false
end))


let uu___is_Fatal_NonVariableInductiveTypeParameter : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonVariableInductiveTypeParameter -> begin
true
end
| uu____870 -> begin
false
end))


let uu___is_Fatal_NotApplicationOrFv : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotApplicationOrFv -> begin
true
end
| uu____876 -> begin
false
end))


let uu___is_Fatal_NotEnoughArgsToEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotEnoughArgsToEffect -> begin
true
end
| uu____882 -> begin
false
end))


let uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotEnoughArgumentsForEffect -> begin
true
end
| uu____888 -> begin
false
end))


let uu___is_Fatal_NotFunctionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotFunctionType -> begin
true
end
| uu____894 -> begin
false
end))


let uu___is_Fatal_NotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotSupported -> begin
true
end
| uu____900 -> begin
false
end))


let uu___is_Fatal_NotTopLevelModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotTopLevelModule -> begin
true
end
| uu____906 -> begin
false
end))


let uu___is_Fatal_NotValidFStarFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotValidFStarFile -> begin
true
end
| uu____912 -> begin
false
end))


let uu___is_Fatal_NotValidIncludeDirectory : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotValidIncludeDirectory -> begin
true
end
| uu____918 -> begin
false
end))


let uu___is_Fatal_OneModulePerFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OneModulePerFile -> begin
true
end
| uu____924 -> begin
false
end))


let uu___is_Fatal_OpenGoalsInSynthesis : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OpenGoalsInSynthesis -> begin
true
end
| uu____930 -> begin
false
end))


let uu___is_Fatal_OptionsNotCompatible : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OptionsNotCompatible -> begin
true
end
| uu____936 -> begin
false
end))


let uu___is_Fatal_OutOfOrder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OutOfOrder -> begin
true
end
| uu____942 -> begin
false
end))


let uu___is_Fatal_ParseErrors : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ParseErrors -> begin
true
end
| uu____948 -> begin
false
end))


let uu___is_Fatal_ParseItError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ParseItError -> begin
true
end
| uu____954 -> begin
false
end))


let uu___is_Fatal_PolyTypeExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PolyTypeExpected -> begin
true
end
| uu____960 -> begin
false
end))


let uu___is_Fatal_PossibleInfiniteTyp : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PossibleInfiniteTyp -> begin
true
end
| uu____966 -> begin
false
end))


let uu___is_Fatal_PreModuleMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PreModuleMismatch -> begin
true
end
| uu____972 -> begin
false
end))


let uu___is_Fatal_QulifierListNotPermitted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_QulifierListNotPermitted -> begin
true
end
| uu____978 -> begin
false
end))


let uu___is_Fatal_RecursiveFunctionLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_RecursiveFunctionLiteral -> begin
true
end
| uu____984 -> begin
false
end))


let uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ReflectOnlySupportedOnEffects -> begin
true
end
| uu____990 -> begin
false
end))


let uu___is_Fatal_ReservedPrefix : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ReservedPrefix -> begin
true
end
| uu____996 -> begin
false
end))


let uu___is_Fatal_SMTOutputParseError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTOutputParseError -> begin
true
end
| uu____1002 -> begin
false
end))


let uu___is_Fatal_SMTSolverError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTSolverError -> begin
true
end
| uu____1008 -> begin
false
end))


let uu___is_Fatal_SyntaxError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SyntaxError -> begin
true
end
| uu____1014 -> begin
false
end))


let uu___is_Fatal_SynthByTacticError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SynthByTacticError -> begin
true
end
| uu____1020 -> begin
false
end))


let uu___is_Fatal_TacticGotStuck : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TacticGotStuck -> begin
true
end
| uu____1026 -> begin
false
end))


let uu___is_Fatal_TcOneFragmentFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TcOneFragmentFailed -> begin
true
end
| uu____1032 -> begin
false
end))


let uu___is_Fatal_TermOutsideOfDefLanguage : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TermOutsideOfDefLanguage -> begin
true
end
| uu____1038 -> begin
false
end))


let uu___is_Fatal_ToManyArgumentToFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ToManyArgumentToFunction -> begin
true
end
| uu____1044 -> begin
false
end))


let uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyOrTooFewFileMatch -> begin
true
end
| uu____1050 -> begin
false
end))


let uu___is_Fatal_TooManyPatternArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyPatternArguments -> begin
true
end
| uu____1056 -> begin
false
end))


let uu___is_Fatal_TooManyUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyUniverse -> begin
true
end
| uu____1062 -> begin
false
end))


let uu___is_Fatal_TypeMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TypeMismatch -> begin
true
end
| uu____1068 -> begin
false
end))


let uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TypeWithinPatternsAllowedOnVariablesOnly -> begin
true
end
| uu____1074 -> begin
false
end))


let uu___is_Fatal_UnableToReadFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnableToReadFile -> begin
true
end
| uu____1080 -> begin
false
end))


let uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnepxectedOrUnboundOperator -> begin
true
end
| uu____1086 -> begin
false
end))


let uu___is_Fatal_UnexpectedBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedBinder -> begin
true
end
| uu____1092 -> begin
false
end))


let uu___is_Fatal_UnexpectedBindShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedBindShape -> begin
true
end
| uu____1098 -> begin
false
end))


let uu___is_Fatal_UnexpectedChar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedChar -> begin
true
end
| uu____1104 -> begin
false
end))


let uu___is_Fatal_UnexpectedComputationTypeForLetRec : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedComputationTypeForLetRec -> begin
true
end
| uu____1110 -> begin
false
end))


let uu___is_Fatal_UnexpectedConstructorType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedConstructorType -> begin
true
end
| uu____1116 -> begin
false
end))


let uu___is_Fatal_UnexpectedDataConstructor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedDataConstructor -> begin
true
end
| uu____1122 -> begin
false
end))


let uu___is_Fatal_UnexpectedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedEffect -> begin
true
end
| uu____1128 -> begin
false
end))


let uu___is_Fatal_UnexpectedEmptyRecord : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedEmptyRecord -> begin
true
end
| uu____1134 -> begin
false
end))


let uu___is_Fatal_UnexpectedExpressionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedExpressionType -> begin
true
end
| uu____1140 -> begin
false
end))


let uu___is_Fatal_UnexpectedFunctionParameterType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedFunctionParameterType -> begin
true
end
| uu____1146 -> begin
false
end))


let uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGeneralizedUniverse -> begin
true
end
| uu____1152 -> begin
false
end))


let uu___is_Fatal_UnexpectedGTotForLetRec : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGTotForLetRec -> begin
true
end
| uu____1158 -> begin
false
end))


let uu___is_Fatal_UnexpectedGuard : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGuard -> begin
true
end
| uu____1164 -> begin
false
end))


let uu___is_Fatal_UnexpectedIdentifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedIdentifier -> begin
true
end
| uu____1170 -> begin
false
end))


let uu___is_Fatal_UnexpectedImplicitArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedImplicitArgument -> begin
true
end
| uu____1176 -> begin
false
end))


let uu___is_Fatal_UnexpectedImplictArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedImplictArgument -> begin
true
end
| uu____1182 -> begin
false
end))


let uu___is_Fatal_UnexpectedInductivetype : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedInductivetype -> begin
true
end
| uu____1188 -> begin
false
end))


let uu___is_Fatal_UnexpectedLetBinding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedLetBinding -> begin
true
end
| uu____1194 -> begin
false
end))


let uu___is_Fatal_UnexpectedModuleDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedModuleDeclaration -> begin
true
end
| uu____1200 -> begin
false
end))


let uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedNumberOfUniverse -> begin
true
end
| uu____1206 -> begin
false
end))


let uu___is_Fatal_UnexpectedNumericLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedNumericLiteral -> begin
true
end
| uu____1212 -> begin
false
end))


let uu___is_Fatal_UnexpectedOperatorSymbol : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedOperatorSymbol -> begin
true
end
| uu____1218 -> begin
false
end))


let uu___is_Fatal_UnexpectedPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedPattern -> begin
true
end
| uu____1224 -> begin
false
end))


let uu___is_Fatal_UnexpectedPosition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedPosition -> begin
true
end
| uu____1230 -> begin
false
end))


let uu___is_Fatal_UnExpectedPreCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnExpectedPreCondition -> begin
true
end
| uu____1236 -> begin
false
end))


let uu___is_Fatal_UnexpectedReturnShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedReturnShape -> begin
true
end
| uu____1242 -> begin
false
end))


let uu___is_Fatal_UnexpectedSignatureForMonad : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedSignatureForMonad -> begin
true
end
| uu____1248 -> begin
false
end))


let uu___is_Fatal_UnexpectedTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTerm -> begin
true
end
| uu____1254 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermInUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermInUniverse -> begin
true
end
| uu____1260 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermType -> begin
true
end
| uu____1266 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermVQuote : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermVQuote -> begin
true
end
| uu____1272 -> begin
false
end))


let uu___is_Fatal_UnexpectedUniversePolymorphicReturn : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedUniversePolymorphicReturn -> begin
true
end
| uu____1278 -> begin
false
end))


let uu___is_Fatal_UnexpectedUniverseVariable : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedUniverseVariable -> begin
true
end
| uu____1284 -> begin
false
end))


let uu___is_Fatal_UnfoldableDeprecated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnfoldableDeprecated -> begin
true
end
| uu____1290 -> begin
false
end))


let uu___is_Fatal_UnificationNotWellFormed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnificationNotWellFormed -> begin
true
end
| uu____1296 -> begin
false
end))


let uu___is_Fatal_Uninstantiated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_Uninstantiated -> begin
true
end
| uu____1302 -> begin
false
end))


let uu___is_Error_UninstantiatedUnificationVarInTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UninstantiatedUnificationVarInTactic -> begin
true
end
| uu____1308 -> begin
false
end))


let uu___is_Fatal_UninstantiatedVarInTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UninstantiatedVarInTactic -> begin
true
end
| uu____1314 -> begin
false
end))


let uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UniverseMightContainSumOfTwoUnivVars -> begin
true
end
| uu____1320 -> begin
false
end))


let uu___is_Fatal_UniversePolymorphicInnerLetBound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UniversePolymorphicInnerLetBound -> begin
true
end
| uu____1326 -> begin
false
end))


let uu___is_Fatal_UnknownAttribute : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnknownAttribute -> begin
true
end
| uu____1332 -> begin
false
end))


let uu___is_Fatal_UnknownToolForDep : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnknownToolForDep -> begin
true
end
| uu____1338 -> begin
false
end))


let uu___is_Fatal_UnrecognizedExtension : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnrecognizedExtension -> begin
true
end
| uu____1344 -> begin
false
end))


let uu___is_Fatal_UnresolvedPatternVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnresolvedPatternVar -> begin
true
end
| uu____1350 -> begin
false
end))


let uu___is_Fatal_UnsupportedConstant : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedConstant -> begin
true
end
| uu____1356 -> begin
false
end))


let uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedDisjuctivePatterns -> begin
true
end
| uu____1362 -> begin
false
end))


let uu___is_Fatal_UnsupportedQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedQualifier -> begin
true
end
| uu____1368 -> begin
false
end))


let uu___is_Fatal_UserTacticFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UserTacticFailure -> begin
true
end
| uu____1374 -> begin
false
end))


let uu___is_Fatal_ValueRestriction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ValueRestriction -> begin
true
end
| uu____1380 -> begin
false
end))


let uu___is_Fatal_VariableNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_VariableNotFound -> begin
true
end
| uu____1386 -> begin
false
end))


let uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongBodyTypeForReturnWP -> begin
true
end
| uu____1392 -> begin
false
end))


let uu___is_Fatal_WrongDataAppHeadFormat : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongDataAppHeadFormat -> begin
true
end
| uu____1398 -> begin
false
end))


let uu___is_Fatal_WrongDefinitionOrder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongDefinitionOrder -> begin
true
end
| uu____1404 -> begin
false
end))


let uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongResultTypeAfterConstrutor -> begin
true
end
| uu____1410 -> begin
false
end))


let uu___is_Fatal_WrongTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongTerm -> begin
true
end
| uu____1416 -> begin
false
end))


let uu___is_Fatal_WhenClauseNotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WhenClauseNotSupported -> begin
true
end
| uu____1422 -> begin
false
end))


let uu___is_Unused01 : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unused01 -> begin
true
end
| uu____1428 -> begin
false
end))


let uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_AddImplicitAssumeNewQualifier -> begin
true
end
| uu____1434 -> begin
false
end))


let uu___is_Warning_AdmitWithoutDefinition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_AdmitWithoutDefinition -> begin
true
end
| uu____1440 -> begin
false
end))


let uu___is_Warning_CachedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CachedFile -> begin
true
end
| uu____1446 -> begin
false
end))


let uu___is_Warning_DefinitionNotTranslated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DefinitionNotTranslated -> begin
true
end
| uu____1452 -> begin
false
end))


let uu___is_Warning_DependencyFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DependencyFound -> begin
true
end
| uu____1458 -> begin
false
end))


let uu___is_Warning_DeprecatedEqualityOnBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedEqualityOnBinder -> begin
true
end
| uu____1464 -> begin
false
end))


let uu___is_Warning_DeprecatedOpaqueQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedOpaqueQualifier -> begin
true
end
| uu____1470 -> begin
false
end))


let uu___is_Warning_DocOverwrite : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DocOverwrite -> begin
true
end
| uu____1476 -> begin
false
end))


let uu___is_Warning_FileNotWritten : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FileNotWritten -> begin
true
end
| uu____1482 -> begin
false
end))


let uu___is_Warning_Filtered : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Filtered -> begin
true
end
| uu____1488 -> begin
false
end))


let uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FunctionLiteralPrecisionLoss -> begin
true
end
| uu____1494 -> begin
false
end))


let uu___is_Warning_FunctionNotExtacted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FunctionNotExtacted -> begin
true
end
| uu____1500 -> begin
false
end))


let uu___is_Warning_HintFailedToReplayProof : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_HintFailedToReplayProof -> begin
true
end
| uu____1506 -> begin
false
end))


let uu___is_Warning_HitReplayFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_HitReplayFailed -> begin
true
end
| uu____1512 -> begin
false
end))


let uu___is_Warning_IDEIgnoreCodeGen : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IDEIgnoreCodeGen -> begin
true
end
| uu____1518 -> begin
false
end))


let uu___is_Warning_IllFormedGoal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IllFormedGoal -> begin
true
end
| uu____1524 -> begin
false
end))


let uu___is_Warning_InaccessibleArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_InaccessibleArgument -> begin
true
end
| uu____1530 -> begin
false
end))


let uu___is_Warning_IncoherentImplicitQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IncoherentImplicitQualifier -> begin
true
end
| uu____1536 -> begin
false
end))


let uu___is_Warning_IrrelevantQualifierOnArgumentToReflect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IrrelevantQualifierOnArgumentToReflect -> begin
true
end
| uu____1542 -> begin
false
end))


let uu___is_Warning_IrrelevantQualifierOnArgumentToReify : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IrrelevantQualifierOnArgumentToReify -> begin
true
end
| uu____1548 -> begin
false
end))


let uu___is_Warning_MalformedWarnErrorList : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MalformedWarnErrorList -> begin
true
end
| uu____1554 -> begin
false
end))


let uu___is_Warning_MetaAlienNotATmUnknown : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MetaAlienNotATmUnknown -> begin
true
end
| uu____1560 -> begin
false
end))


let uu___is_Warning_MultipleAscriptions : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MultipleAscriptions -> begin
true
end
| uu____1566 -> begin
false
end))


let uu___is_Warning_NondependentUserDefinedDataType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NondependentUserDefinedDataType -> begin
true
end
| uu____1572 -> begin
false
end))


let uu___is_Warning_NonListLiteralSMTPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NonListLiteralSMTPattern -> begin
true
end
| uu____1578 -> begin
false
end))


let uu___is_Warning_NormalizationFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NormalizationFailure -> begin
true
end
| uu____1584 -> begin
false
end))


let uu___is_Warning_NotDependentArrow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NotDependentArrow -> begin
true
end
| uu____1590 -> begin
false
end))


let uu___is_Warning_NotEmbedded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NotEmbedded -> begin
true
end
| uu____1596 -> begin
false
end))


let uu___is_Warning_PatternMissingBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_PatternMissingBoundVar -> begin
true
end
| uu____1602 -> begin
false
end))


let uu___is_Warning_RecursiveDependency : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_RecursiveDependency -> begin
true
end
| uu____1608 -> begin
false
end))


let uu___is_Warning_RedundantExplicitCurrying : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_RedundantExplicitCurrying -> begin
true
end
| uu____1614 -> begin
false
end))


let uu___is_Warning_SMTPatTDeprecated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_SMTPatTDeprecated -> begin
true
end
| uu____1620 -> begin
false
end))


let uu___is_Warning_SMTPatternMissingBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_SMTPatternMissingBoundVar -> begin
true
end
| uu____1626 -> begin
false
end))


let uu___is_Warning_TopLevelEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_TopLevelEffect -> begin
true
end
| uu____1632 -> begin
false
end))


let uu___is_Warning_UnboundModuleReference : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnboundModuleReference -> begin
true
end
| uu____1638 -> begin
false
end))


let uu___is_Warning_UnexpectedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedFile -> begin
true
end
| uu____1644 -> begin
false
end))


let uu___is_Warning_UnexpectedFsTypApp : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedFsTypApp -> begin
true
end
| uu____1650 -> begin
false
end))


let uu___is_Warning_UnexpectedZ3Output : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedZ3Output -> begin
true
end
| uu____1656 -> begin
false
end))


let uu___is_Warning_UnprotectedTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnprotectedTerm -> begin
true
end
| uu____1662 -> begin
false
end))


let uu___is_Warning_UnrecognizedAttribute : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnrecognizedAttribute -> begin
true
end
| uu____1668 -> begin
false
end))


let uu___is_Warning_UpperBoundCandidateAlreadyVisited : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UpperBoundCandidateAlreadyVisited -> begin
true
end
| uu____1674 -> begin
false
end))


let uu___is_Warning_UseDefaultEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UseDefaultEffect -> begin
true
end
| uu____1680 -> begin
false
end))


let uu___is_Warning_WrongErrorLocation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_WrongErrorLocation -> begin
true
end
| uu____1686 -> begin
false
end))


let uu___is_Warning_Z3InvocationWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Z3InvocationWarning -> begin
true
end
| uu____1692 -> begin
false
end))


let uu___is_Warning_CallNotImplementedAsWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CallNotImplementedAsWarning -> begin
true
end
| uu____1698 -> begin
false
end))


let uu___is_Warning_MissingInterfaceOrImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MissingInterfaceOrImplementation -> begin
true
end
| uu____1704 -> begin
false
end))


let uu___is_Warning_ConstructorBuildsUnexpectedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ConstructorBuildsUnexpectedType -> begin
true
end
| uu____1710 -> begin
false
end))


let uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ModuleOrFileNotFoundWarning -> begin
true
end
| uu____1716 -> begin
false
end))


let uu___is_Error_NoLetMutable : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_NoLetMutable -> begin
true
end
| uu____1722 -> begin
false
end))


let uu___is_Error_BadImplicit : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadImplicit -> begin
true
end
| uu____1728 -> begin
false
end))


let uu___is_Warning_DeprecatedDefinition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedDefinition -> begin
true
end
| uu____1734 -> begin
false
end))


let uu___is_Fatal_SMTEncodingArityMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTEncodingArityMismatch -> begin
true
end
| uu____1740 -> begin
false
end))


let uu___is_Warning_Defensive : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Defensive -> begin
true
end
| uu____1746 -> begin
false
end))


let uu___is_Warning_CantInspect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CantInspect -> begin
true
end
| uu____1752 -> begin
false
end))


let uu___is_Warning_NilGivenExplicitArgs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NilGivenExplicitArgs -> begin
true
end
| uu____1758 -> begin
false
end))


let uu___is_Warning_ConsAppliedExplicitArgs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ConsAppliedExplicitArgs -> begin
true
end
| uu____1764 -> begin
false
end))


let uu___is_Warning_UnembedBinderKnot : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnembedBinderKnot -> begin
true
end
| uu____1770 -> begin
false
end))


let uu___is_Fatal_TacticProofRelevantGoal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TacticProofRelevantGoal -> begin
true
end
| uu____1776 -> begin
false
end))


let uu___is_Warning_TacAdmit : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_TacAdmit -> begin
true
end
| uu____1782 -> begin
false
end))


let uu___is_Fatal_IncoherentPatterns : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncoherentPatterns -> begin
true
end
| uu____1788 -> begin
false
end))


let uu___is_Error_NoSMTButNeeded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_NoSMTButNeeded -> begin
true
end
| uu____1794 -> begin
false
end))


let uu___is_Fatal_UnexpectedAntiquotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedAntiquotation -> begin
true
end
| uu____1800 -> begin
false
end))


let uu___is_Fatal_SplicedUndef : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SplicedUndef -> begin
true
end
| uu____1806 -> begin
false
end))


let uu___is_Fatal_SpliceUnembedFail : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SpliceUnembedFail -> begin
true
end
| uu____1812 -> begin
false
end))


let uu___is_Warning_ExtractionUnexpectedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ExtractionUnexpectedEffect -> begin
true
end
| uu____1818 -> begin
false
end))


let uu___is_Error_DidNotFail : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_DidNotFail -> begin
true
end
| uu____1824 -> begin
false
end))


let uu___is_Warning_UnappliedFail : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnappliedFail -> begin
true
end
| uu____1830 -> begin
false
end))


let uu___is_Warning_QuantifierWithoutPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_QuantifierWithoutPattern -> begin
true
end
| uu____1836 -> begin
false
end))


let uu___is_Error_EmptyFailErrs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_EmptyFailErrs -> begin
true
end
| uu____1842 -> begin
false
end))


let uu___is_Warning_logicqualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_logicqualifier -> begin
true
end
| uu____1848 -> begin
false
end))


let uu___is_Fatal_CyclicDependence : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CyclicDependence -> begin
true
end
| uu____1854 -> begin
false
end))


let uu___is_Error_InductiveAnnotNotAType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InductiveAnnotNotAType -> begin
true
end
| uu____1860 -> begin
false
end))


let uu___is_Fatal_FriendInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FriendInterface -> begin
true
end
| uu____1866 -> begin
false
end))


let uu___is_Error_CannotRedefineConst : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_CannotRedefineConst -> begin
true
end
| uu____1872 -> begin
false
end))


let uu___is_Error_BadClassDecl : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadClassDecl -> begin
true
end
| uu____1878 -> begin
false
end))


let uu___is_Error_BadInductiveParam : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadInductiveParam -> begin
true
end
| uu____1884 -> begin
false
end))


let uu___is_Error_FieldShadow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_FieldShadow -> begin
true
end
| uu____1890 -> begin
false
end))


let uu___is_Error_UnexpectedDM4FType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedDM4FType -> begin
true
end
| uu____1896 -> begin
false
end))


let uu___is_Fatal_EffectAbbreviationResultTypeMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectAbbreviationResultTypeMismatch -> begin
true
end
| uu____1902 -> begin
false
end))

type flag =
| CFatal
| CAlwaysError
| CError
| CWarning
| CSilent


let uu___is_CFatal : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CFatal -> begin
true
end
| uu____1908 -> begin
false
end))


let uu___is_CAlwaysError : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CAlwaysError -> begin
true
end
| uu____1914 -> begin
false
end))


let uu___is_CError : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CError -> begin
true
end
| uu____1920 -> begin
false
end))


let uu___is_CWarning : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CWarning -> begin
true
end
| uu____1926 -> begin
false
end))


let uu___is_CSilent : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CSilent -> begin
true
end
| uu____1932 -> begin
false
end))


let default_flags : (raw_error * flag) Prims.list = (((Error_DependencyAnalysisFailed), (CAlwaysError)))::(((Error_IDETooManyPops), (CAlwaysError)))::(((Error_IDEUnrecognized), (CAlwaysError)))::(((Error_InductiveTypeNotSatisfyPositivityCondition), (CAlwaysError)))::(((Error_InvalidUniverseVar), (CAlwaysError)))::(((Error_MissingFileName), (CAlwaysError)))::(((Error_ModuleFileNameMismatch), (CAlwaysError)))::(((Error_OpPlusInUniverse), (CAlwaysError)))::(((Error_OutOfRange), (CAlwaysError)))::(((Error_ProofObligationFailed), (CAlwaysError)))::(((Error_TooManyFiles), (CAlwaysError)))::(((Error_TypeCheckerFailToProve), (CAlwaysError)))::(((Error_TypeError), (CAlwaysError)))::(((Error_UncontrainedUnificationVar), (CAlwaysError)))::(((Error_UnexpectedGTotComputation), (CAlwaysError)))::(((Error_UnexpectedInstance), (CAlwaysError)))::(((Error_UnknownFatal_AssertionFailure), (CAlwaysError)))::(((Error_Z3InvocationError), (CAlwaysError)))::(((Error_IDEAssertionFailure), (CAlwaysError)))::(((Error_Z3SolverError), (CAlwaysError)))::(((Fatal_AbstractTypeDeclarationInInterface), (CFatal)))::(((Fatal_ActionMustHaveFunctionType), (CFatal)))::(((Fatal_AlreadyDefinedTopLevelDeclaration), (CFatal)))::(((Fatal_ArgumentLengthMismatch), (CFatal)))::(((Fatal_AssertionFailure), (CFatal)))::(((Fatal_AssignToImmutableValues), (CFatal)))::(((Fatal_AssumeValInInterface), (CFatal)))::(((Fatal_BadlyInstantiatedSynthByTactic), (CFatal)))::(((Fatal_BadSignatureShape), (CFatal)))::(((Fatal_BinderAndArgsLengthMismatch), (CFatal)))::(((Fatal_BothValAndLetInInterface), (CFatal)))::(((Fatal_CardinalityConstraintViolated), (CFatal)))::(((Fatal_ComputationNotTotal), (CFatal)))::(((Fatal_ComputationTypeNotAllowed), (CFatal)))::(((Fatal_ComputedTypeNotMatchAnnotation), (CFatal)))::(((Fatal_ConstructorArgLengthMismatch), (CFatal)))::(((Fatal_ConstructorFailedCheck), (CFatal)))::(((Fatal_ConstructorNotFound), (CFatal)))::(((Fatal_ConstsructorBuildWrongType), (CFatal)))::(((Fatal_CycleInRecTypeAbbreviation), (CFatal)))::(((Fatal_DataContructorNotFound), (CFatal)))::(((Fatal_DefaultQualifierNotAllowedOnEffects), (CFatal)))::(((Fatal_DefinitionNotFound), (CFatal)))::(((Fatal_DisjuctivePatternVarsMismatch), (CFatal)))::(((Fatal_DivergentComputationCannotBeIncludedInTotal), (CFatal)))::(((Fatal_DuplicateInImplementation), (CFatal)))::(((Fatal_DuplicateModuleOrInterface), (CFatal)))::(((Fatal_DuplicateTopLevelNames), (CFatal)))::(((Fatal_DuplicateTypeAnnotationAndValDecl), (CFatal)))::(((Fatal_EffectCannotBeReified), (CFatal)))::(((Fatal_EffectConstructorNotFullyApplied), (CFatal)))::(((Fatal_EffectfulAndPureComputationMismatch), (CFatal)))::(((Fatal_EffectNotFound), (CFatal)))::(((Fatal_EffectsCannotBeComposed), (CFatal)))::(((Fatal_ErrorInSolveDeferredConstraints), (CFatal)))::(((Fatal_ErrorsReported), (CFatal)))::(((Fatal_EscapedBoundVar), (CFatal)))::(((Fatal_ExpectedArrowAnnotatedType), (CFatal)))::(((Fatal_ExpectedGhostExpression), (CFatal)))::(((Fatal_ExpectedPureExpression), (CFatal)))::(((Fatal_ExpectNormalizedEffect), (CFatal)))::(((Fatal_ExpectTermGotFunction), (CFatal)))::(((Fatal_ExpectTrivialPreCondition), (CFatal)))::(((Fatal_FailToExtractNativeTactic), (CFatal)))::(((Fatal_FailToCompileNativeTactic), (CFatal)))::(((Fatal_FailToProcessPragma), (CFatal)))::(((Fatal_FailToResolveImplicitArgument), (CFatal)))::(((Fatal_FailToSolveUniverseInEquality), (CFatal)))::(((Fatal_FieldsNotBelongToSameRecordType), (CFatal)))::(((Fatal_ForbiddenReferenceToCurrentModule), (CFatal)))::(((Fatal_FreeVariables), (CFatal)))::(((Fatal_FunctionTypeExpected), (CFatal)))::(((Fatal_IdentifierNotFound), (CFatal)))::(((Fatal_IllAppliedConstant), (CFatal)))::(((Fatal_IllegalCharInByteArray), (CFatal)))::(((Fatal_IllegalCharInOperatorName), (CFatal)))::(((Fatal_IllTyped), (CFatal)))::(((Fatal_ImpossibleAbbrevLidBundle), (CFatal)))::(((Fatal_ImpossibleAbbrevRenameBundle), (CFatal)))::(((Fatal_ImpossibleInductiveWithAbbrev), (CFatal)))::(((Fatal_ImpossiblePrePostAbs), (CFatal)))::(((Fatal_ImpossiblePrePostArrow), (CFatal)))::(((Fatal_ImpossibleToGenerateDMEffect), (CFatal)))::(((Fatal_ImpossibleTypeAbbrevBundle), (CFatal)))::(((Fatal_ImpossibleTypeAbbrevSigeltBundle), (CFatal)))::(((Fatal_IncludeModuleNotPrepared), (CFatal)))::(((Fatal_IncoherentInlineUniverse), (CFatal)))::(((Fatal_IncompatibleKinds), (CFatal)))::(((Fatal_IncompatibleNumberOfTypes), (CFatal)))::(((Fatal_IncompatibleSetOfUniverse), (CFatal)))::(((Fatal_IncompatibleUniverse), (CFatal)))::(((Fatal_InconsistentImplicitArgumentAnnotation), (CFatal)))::(((Fatal_InconsistentImplicitQualifier), (CFatal)))::(((Fatal_InconsistentQualifierAnnotation), (CFatal)))::(((Fatal_InferredTypeCauseVarEscape), (CFatal)))::(((Fatal_InlineRenamedAsUnfold), (CFatal)))::(((Fatal_InsufficientPatternArguments), (CFatal)))::(((Fatal_InterfaceAlreadyProcessed), (CFatal)))::(((Fatal_InterfaceNotImplementedByModule), (CFatal)))::(((Fatal_InterfaceWithTypeImplementation), (CFatal)))::(((Fatal_InvalidFloatingPointNumber), (CFatal)))::(((Fatal_InvalidFSDocKeyword), (CFatal)))::(((Fatal_InvalidIdentifier), (CFatal)))::(((Fatal_InvalidLemmaArgument), (CFatal)))::(((Fatal_InvalidNumericLiteral), (CFatal)))::(((Fatal_InvalidRedefinitionOfLexT), (CFatal)))::(((Fatal_InvalidUnicodeInStringLiteral), (CFatal)))::(((Fatal_InvalidUTF8Encoding), (CFatal)))::(((Fatal_InvalidWarnErrorSetting), (CFatal)))::(((Fatal_LetBoundMonadicMismatch), (CFatal)))::(((Fatal_LetMutableForVariablesOnly), (CFatal)))::(((Fatal_LetOpenModuleOnly), (CFatal)))::(((Fatal_LetRecArgumentMismatch), (CFatal)))::(((Fatal_MalformedActionDeclaration), (CFatal)))::(((Fatal_MismatchedPatternType), (CFatal)))::(((Fatal_MismatchUniversePolymorphic), (CFatal)))::(((Fatal_MissingDataConstructor), (CFatal)))::(((Fatal_MissingExposeInterfacesOption), (CFatal)))::(((Fatal_MissingFieldInRecord), (CFatal)))::(((Fatal_MissingImplementation), (CFatal)))::(((Fatal_MissingImplicitArguments), (CFatal)))::(((Fatal_MissingInterface), (CFatal)))::(((Fatal_MissingNameInBinder), (CFatal)))::(((Fatal_MissingPrimsModule), (CFatal)))::(((Fatal_MissingQuantifierBinder), (CFatal)))::(((Fatal_ModuleExpected), (CFatal)))::(((Fatal_ModuleFileNotFound), (CFatal)))::(((Fatal_ModuleFirstStatement), (CFatal)))::(((Fatal_ModuleNotFound), (CFatal)))::(((Fatal_ModuleOrFileNotFound), (CFatal)))::(((Fatal_MonadAlreadyDefined), (CFatal)))::(((Fatal_MoreThanOneDeclaration), (CFatal)))::(((Fatal_MultipleLetBinding), (CFatal)))::(((Fatal_NameNotFound), (CFatal)))::(((Fatal_NameSpaceNotFound), (CFatal)))::(((Fatal_NegativeUniverseConstFatal_NotSupported), (CFatal)))::(((Fatal_NoFileProvided), (CFatal)))::(((Fatal_NonInductiveInMutuallyDefinedType), (CFatal)))::(((Fatal_NonLinearPatternNotPermitted), (CFatal)))::(((Fatal_NonLinearPatternVars), (CFatal)))::(((Fatal_NonSingletonTopLevel), (CFatal)))::(((Fatal_NonSingletonTopLevelModule), (CFatal)))::(((Fatal_NonTopRecFunctionNotFullyEncoded), (CFatal)))::(((Fatal_NonTrivialPreConditionInPrims), (CFatal)))::(((Fatal_NonVariableInductiveTypeParameter), (CFatal)))::(((Fatal_NotApplicationOrFv), (CFatal)))::(((Fatal_NotEnoughArgsToEffect), (CFatal)))::(((Fatal_NotEnoughArgumentsForEffect), (CFatal)))::(((Fatal_NotFunctionType), (CFatal)))::(((Fatal_NotSupported), (CFatal)))::(((Fatal_NotTopLevelModule), (CFatal)))::(((Fatal_NotValidFStarFile), (CFatal)))::(((Fatal_NotValidIncludeDirectory), (CFatal)))::(((Fatal_OneModulePerFile), (CFatal)))::(((Fatal_OpenGoalsInSynthesis), (CFatal)))::(((Fatal_OptionsNotCompatible), (CFatal)))::(((Fatal_OutOfOrder), (CFatal)))::(((Fatal_ParseErrors), (CFatal)))::(((Fatal_ParseItError), (CFatal)))::(((Fatal_PolyTypeExpected), (CFatal)))::(((Fatal_PossibleInfiniteTyp), (CFatal)))::(((Fatal_PreModuleMismatch), (CFatal)))::(((Fatal_QulifierListNotPermitted), (CFatal)))::(((Fatal_RecursiveFunctionLiteral), (CFatal)))::(((Fatal_ReflectOnlySupportedOnEffects), (CFatal)))::(((Fatal_ReservedPrefix), (CFatal)))::(((Fatal_SMTOutputParseError), (CFatal)))::(((Fatal_SMTSolverError), (CFatal)))::(((Fatal_SyntaxError), (CFatal)))::(((Fatal_SynthByTacticError), (CFatal)))::(((Fatal_TacticGotStuck), (CFatal)))::(((Fatal_TcOneFragmentFailed), (CFatal)))::(((Fatal_TermOutsideOfDefLanguage), (CFatal)))::(((Fatal_ToManyArgumentToFunction), (CFatal)))::(((Fatal_TooManyOrTooFewFileMatch), (CFatal)))::(((Fatal_TooManyPatternArguments), (CFatal)))::(((Fatal_TooManyUniverse), (CFatal)))::(((Fatal_TypeMismatch), (CFatal)))::(((Fatal_TypeWithinPatternsAllowedOnVariablesOnly), (CFatal)))::(((Fatal_UnableToReadFile), (CFatal)))::(((Fatal_UnepxectedOrUnboundOperator), (CFatal)))::(((Fatal_UnexpectedBinder), (CFatal)))::(((Fatal_UnexpectedBindShape), (CFatal)))::(((Fatal_UnexpectedChar), (CFatal)))::(((Fatal_UnexpectedComputationTypeForLetRec), (CFatal)))::(((Fatal_UnexpectedConstructorType), (CFatal)))::(((Fatal_UnexpectedDataConstructor), (CFatal)))::(((Fatal_UnexpectedEffect), (CFatal)))::(((Fatal_UnexpectedEmptyRecord), (CFatal)))::(((Fatal_UnexpectedExpressionType), (CFatal)))::(((Fatal_UnexpectedFunctionParameterType), (CFatal)))::(((Fatal_UnexpectedGeneralizedUniverse), (CFatal)))::(((Fatal_UnexpectedGTotForLetRec), (CFatal)))::(((Fatal_UnexpectedGuard), (CFatal)))::(((Fatal_UnexpectedIdentifier), (CFatal)))::(((Fatal_UnexpectedImplicitArgument), (CFatal)))::(((Fatal_UnexpectedImplictArgument), (CFatal)))::(((Fatal_UnexpectedInductivetype), (CFatal)))::(((Fatal_UnexpectedLetBinding), (CFatal)))::(((Fatal_UnexpectedModuleDeclaration), (CFatal)))::(((Fatal_UnexpectedNumberOfUniverse), (CFatal)))::(((Fatal_UnexpectedNumericLiteral), (CFatal)))::(((Fatal_UnexpectedOperatorSymbol), (CFatal)))::(((Fatal_UnexpectedPattern), (CFatal)))::(((Fatal_UnexpectedPosition), (CFatal)))::(((Fatal_UnExpectedPreCondition), (CFatal)))::(((Fatal_UnexpectedReturnShape), (CFatal)))::(((Fatal_UnexpectedSignatureForMonad), (CFatal)))::(((Fatal_UnexpectedTerm), (CFatal)))::(((Fatal_UnexpectedTermInUniverse), (CFatal)))::(((Fatal_UnexpectedTermType), (CFatal)))::(((Fatal_UnexpectedTermVQuote), (CFatal)))::(((Fatal_UnexpectedUniversePolymorphicReturn), (CFatal)))::(((Fatal_UnexpectedUniverseVariable), (CFatal)))::(((Fatal_UnfoldableDeprecated), (CFatal)))::(((Fatal_UnificationNotWellFormed), (CFatal)))::(((Fatal_Uninstantiated), (CFatal)))::(((Error_UninstantiatedUnificationVarInTactic), (CError)))::(((Fatal_UninstantiatedVarInTactic), (CFatal)))::(((Fatal_UniverseMightContainSumOfTwoUnivVars), (CFatal)))::(((Fatal_UniversePolymorphicInnerLetBound), (CFatal)))::(((Fatal_UnknownAttribute), (CFatal)))::(((Fatal_UnknownToolForDep), (CFatal)))::(((Fatal_UnrecognizedExtension), (CFatal)))::(((Fatal_UnresolvedPatternVar), (CFatal)))::(((Fatal_UnsupportedConstant), (CFatal)))::(((Fatal_UnsupportedDisjuctivePatterns), (CFatal)))::(((Fatal_UnsupportedQualifier), (CFatal)))::(((Fatal_UserTacticFailure), (CFatal)))::(((Fatal_ValueRestriction), (CFatal)))::(((Fatal_VariableNotFound), (CFatal)))::(((Fatal_WrongBodyTypeForReturnWP), (CFatal)))::(((Fatal_WrongDataAppHeadFormat), (CFatal)))::(((Fatal_WrongDefinitionOrder), (CFatal)))::(((Fatal_WrongResultTypeAfterConstrutor), (CFatal)))::(((Fatal_WrongTerm), (CFatal)))::(((Fatal_WhenClauseNotSupported), (CFatal)))::(((Unused01), (CFatal)))::(((Warning_CallNotImplementedAsWarning), (CWarning)))::(((Warning_AddImplicitAssumeNewQualifier), (CWarning)))::(((Warning_AdmitWithoutDefinition), (CWarning)))::(((Warning_CachedFile), (CWarning)))::(((Warning_DefinitionNotTranslated), (CWarning)))::(((Warning_DependencyFound), (CWarning)))::(((Warning_DeprecatedEqualityOnBinder), (CWarning)))::(((Warning_DeprecatedOpaqueQualifier), (CWarning)))::(((Warning_DocOverwrite), (CWarning)))::(((Warning_FileNotWritten), (CWarning)))::(((Warning_Filtered), (CWarning)))::(((Warning_FunctionLiteralPrecisionLoss), (CWarning)))::(((Warning_FunctionNotExtacted), (CWarning)))::(((Warning_HintFailedToReplayProof), (CWarning)))::(((Warning_HitReplayFailed), (CWarning)))::(((Warning_IDEIgnoreCodeGen), (CWarning)))::(((Warning_IllFormedGoal), (CWarning)))::(((Warning_InaccessibleArgument), (CWarning)))::(((Warning_IncoherentImplicitQualifier), (CWarning)))::(((Warning_IrrelevantQualifierOnArgumentToReflect), (CWarning)))::(((Warning_IrrelevantQualifierOnArgumentToReify), (CWarning)))::(((Warning_MalformedWarnErrorList), (CWarning)))::(((Warning_MetaAlienNotATmUnknown), (CWarning)))::(((Warning_MultipleAscriptions), (CWarning)))::(((Warning_NondependentUserDefinedDataType), (CWarning)))::(((Warning_NonListLiteralSMTPattern), (CWarning)))::(((Warning_NormalizationFailure), (CWarning)))::(((Warning_NotDependentArrow), (CWarning)))::(((Warning_NotEmbedded), (CWarning)))::(((Warning_PatternMissingBoundVar), (CWarning)))::(((Warning_RecursiveDependency), (CWarning)))::(((Warning_RedundantExplicitCurrying), (CWarning)))::(((Warning_SMTPatTDeprecated), (CWarning)))::(((Warning_SMTPatternMissingBoundVar), (CWarning)))::(((Warning_TopLevelEffect), (CWarning)))::(((Warning_UnboundModuleReference), (CWarning)))::(((Warning_UnexpectedFile), (CWarning)))::(((Warning_UnexpectedFsTypApp), (CWarning)))::(((Warning_UnexpectedZ3Output), (CError)))::(((Warning_UnprotectedTerm), (CWarning)))::(((Warning_UnrecognizedAttribute), (CWarning)))::(((Warning_UpperBoundCandidateAlreadyVisited), (CWarning)))::(((Warning_UseDefaultEffect), (CWarning)))::(((Warning_WrongErrorLocation), (CWarning)))::(((Warning_Z3InvocationWarning), (CWarning)))::(((Warning_MissingInterfaceOrImplementation), (CWarning)))::(((Warning_ConstructorBuildsUnexpectedType), (CWarning)))::(((Warning_ModuleOrFileNotFoundWarning), (CWarning)))::(((Error_NoLetMutable), (CAlwaysError)))::(((Error_BadImplicit), (CAlwaysError)))::(((Warning_DeprecatedDefinition), (CWarning)))::(((Fatal_SMTEncodingArityMismatch), (CFatal)))::(((Warning_Defensive), (CWarning)))::(((Warning_CantInspect), (CWarning)))::(((Warning_NilGivenExplicitArgs), (CWarning)))::(((Warning_ConsAppliedExplicitArgs), (CWarning)))::(((Warning_UnembedBinderKnot), (CWarning)))::(((Fatal_TacticProofRelevantGoal), (CFatal)))::(((Warning_TacAdmit), (CWarning)))::(((Fatal_IncoherentPatterns), (CFatal)))::(((Error_NoSMTButNeeded), (CAlwaysError)))::(((Fatal_UnexpectedAntiquotation), (CFatal)))::(((Fatal_SplicedUndef), (CFatal)))::(((Fatal_SpliceUnembedFail), (CFatal)))::(((Warning_ExtractionUnexpectedEffect), (CWarning)))::(((Error_DidNotFail), (CAlwaysError)))::(((Warning_UnappliedFail), (CWarning)))::(((Warning_QuantifierWithoutPattern), (CSilent)))::(((Error_EmptyFailErrs), (CAlwaysError)))::(((Warning_logicqualifier), (CWarning)))::(((Fatal_CyclicDependence), (CFatal)))::(((Error_InductiveAnnotNotAType), (CError)))::(((Fatal_FriendInterface), (CFatal)))::(((Error_CannotRedefineConst), (CError)))::(((Error_BadClassDecl), (CError)))::(((Error_BadInductiveParam), (CFatal)))::(((Error_FieldShadow), (CFatal)))::(((Error_UnexpectedDM4FType), (CFatal)))::(((Fatal_EffectAbbreviationResultTypeMismatch), (CFatal)))::[]

exception Err of ((raw_error * Prims.string))


let uu___is_Err : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (uu____3224) -> begin
true
end
| uu____3229 -> begin
false
end))


let __proj__Err__item__uu___ : Prims.exn  ->  (raw_error * Prims.string) = (fun projectee -> (match (projectee) with
| Err (uu____3244) -> begin
uu____3244
end))

exception Error of ((raw_error * Prims.string * FStar_Range.range))


let uu___is_Error : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error (uu____3264) -> begin
true
end
| uu____3271 -> begin
false
end))


let __proj__Error__item__uu___ : Prims.exn  ->  (raw_error * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (uu____3290) -> begin
uu____3290
end))

exception Warning of ((raw_error * Prims.string * FStar_Range.range))


let uu___is_Warning : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning (uu____3312) -> begin
true
end
| uu____3319 -> begin
false
end))


let __proj__Warning__item__uu___ : Prims.exn  ->  (raw_error * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (uu____3338) -> begin
uu____3338
end))

exception Stop


let uu___is_Stop : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stop -> begin
true
end
| uu____3350 -> begin
false
end))

exception Empty_frag


let uu___is_Empty_frag : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty_frag -> begin
true
end
| uu____3356 -> begin
false
end))

type issue_level =
| ENotImplemented
| EInfo
| EWarning
| EError


let uu___is_ENotImplemented : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ENotImplemented -> begin
true
end
| uu____3362 -> begin
false
end))


let uu___is_EInfo : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EInfo -> begin
true
end
| uu____3368 -> begin
false
end))


let uu___is_EWarning : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWarning -> begin
true
end
| uu____3374 -> begin
false
end))


let uu___is_EError : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EError -> begin
true
end
| uu____3380 -> begin
false
end))

type issue =
{issue_message : Prims.string; issue_level : issue_level; issue_range : FStar_Range.range FStar_Pervasives_Native.option; issue_number : Prims.int FStar_Pervasives_Native.option}


let __proj__Mkissue__item__issue_message : issue  ->  Prims.string = (fun projectee -> (match (projectee) with
| {issue_message = issue_message; issue_level = issue_level; issue_range = issue_range; issue_number = issue_number} -> begin
issue_message
end))


let __proj__Mkissue__item__issue_level : issue  ->  issue_level = (fun projectee -> (match (projectee) with
| {issue_message = issue_message; issue_level = issue_level; issue_range = issue_range; issue_number = issue_number} -> begin
issue_level
end))


let __proj__Mkissue__item__issue_range : issue  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {issue_message = issue_message; issue_level = issue_level; issue_range = issue_range; issue_number = issue_number} -> begin
issue_range
end))


let __proj__Mkissue__item__issue_number : issue  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {issue_message = issue_message; issue_level = issue_level; issue_range = issue_range; issue_number = issue_number} -> begin
issue_number
end))

type error_handler =
{eh_add_one : issue  ->  unit; eh_count_errors : unit  ->  Prims.int; eh_report : unit  ->  issue Prims.list; eh_clear : unit  ->  unit}


let __proj__Mkerror_handler__item__eh_add_one : error_handler  ->  issue  ->  unit = (fun projectee -> (match (projectee) with
| {eh_add_one = eh_add_one; eh_count_errors = eh_count_errors; eh_report = eh_report; eh_clear = eh_clear} -> begin
eh_add_one
end))


let __proj__Mkerror_handler__item__eh_count_errors : error_handler  ->  unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {eh_add_one = eh_add_one; eh_count_errors = eh_count_errors; eh_report = eh_report; eh_clear = eh_clear} -> begin
eh_count_errors
end))


let __proj__Mkerror_handler__item__eh_report : error_handler  ->  unit  ->  issue Prims.list = (fun projectee -> (match (projectee) with
| {eh_add_one = eh_add_one; eh_count_errors = eh_count_errors; eh_report = eh_report; eh_clear = eh_clear} -> begin
eh_report
end))


let __proj__Mkerror_handler__item__eh_clear : error_handler  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {eh_add_one = eh_add_one; eh_count_errors = eh_count_errors; eh_report = eh_report; eh_clear = eh_clear} -> begin
eh_clear
end))


let format_issue : issue  ->  Prims.string = (fun issue -> (

let level_header = (match (issue.issue_level) with
| EInfo -> begin
"Info"
end
| EWarning -> begin
"Warning"
end
| EError -> begin
"Error"
end
| ENotImplemented -> begin
"Feature not yet implemented: "
end)
in (

let uu____3637 = (match (issue.issue_range) with
| FStar_Pervasives_Native.None -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) when (Prims.op_Equality r FStar_Range.dummyRange) -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____3648 = (

let uu____3649 = (FStar_Range.string_of_use_range r)
in (FStar_Util.format1 "%s: " uu____3649))
in (

let uu____3650 = (

let uu____3651 = (

let uu____3652 = (FStar_Range.use_range r)
in (

let uu____3653 = (FStar_Range.def_range r)
in (Prims.op_Equality uu____3652 uu____3653)))
in (match (uu____3651) with
| true -> begin
""
end
| uu____3654 -> begin
(

let uu____3655 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 " (see also %s)" uu____3655))
end))
in ((uu____3648), (uu____3650))))
end)
in (match (uu____3637) with
| (range_str, see_also_str) -> begin
(

let issue_number = (match (issue.issue_number) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____3660 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 " %s" uu____3660))
end)
in (FStar_Util.format5 "%s(%s%s) %s%s\n" range_str level_header issue_number issue.issue_message see_also_str))
end))))


let print_issue : issue  ->  unit = (fun issue -> (

let printer = (match (issue.issue_level) with
| EInfo -> begin
FStar_Util.print_string
end
| EWarning -> begin
FStar_Util.print_warning
end
| EError -> begin
FStar_Util.print_error
end
| ENotImplemented -> begin
FStar_Util.print_error
end)
in (

let uu____3674 = (format_issue issue)
in (printer uu____3674))))


let compare_issues : issue  ->  issue  ->  Prims.int = (fun i1 i2 -> (match (((i1.issue_range), (i2.issue_range))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "0")
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____3693)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Pervasives_Native.Some (uu____3698), FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "1")
end
| (FStar_Pervasives_Native.Some (r1), FStar_Pervasives_Native.Some (r2)) -> begin
(FStar_Range.compare_use_range r1 r2)
end))


let mk_default_handler : Prims.bool  ->  error_handler = (fun print7 -> (

let errs = (FStar_Util.mk_ref [])
in (

let add_one = (fun e -> (match (e.issue_level) with
| EError -> begin
(

let uu____3727 = (

let uu____3730 = (FStar_ST.op_Bang errs)
in (e)::uu____3730)
in (FStar_ST.op_Colon_Equals errs uu____3727))
end
| uu____3823 -> begin
(print_issue e)
end))
in (

let count_errors = (fun uu____3829 -> (

let uu____3830 = (FStar_ST.op_Bang errs)
in (FStar_List.length uu____3830)))
in (

let report = (fun uu____3885 -> (

let sorted1 = (

let uu____3889 = (FStar_ST.op_Bang errs)
in (FStar_List.sortWith compare_issues uu____3889))
in ((match (print7) with
| true -> begin
(FStar_List.iter print_issue sorted1)
end
| uu____3938 -> begin
()
end);
sorted1;
)))
in (

let clear1 = (fun uu____3944 -> (FStar_ST.op_Colon_Equals errs []))
in {eh_add_one = add_one; eh_count_errors = count_errors; eh_report = report; eh_clear = clear1}))))))


let default_handler : error_handler = (mk_default_handler true)


let current_handler : error_handler FStar_ST.ref = (FStar_Util.mk_ref default_handler)


let mk_issue : issue_level  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  issue = (fun level range msg n1 -> {issue_message = msg; issue_level = level; issue_range = range; issue_number = n1})


let get_err_count : unit  ->  Prims.int = (fun uu____4039 -> (

let uu____4040 = (

let uu____4045 = (FStar_ST.op_Bang current_handler)
in uu____4045.eh_count_errors)
in (uu____4040 ())))


let wrapped_eh_add_one : error_handler  ->  issue  ->  unit = (fun h issue -> ((h.eh_add_one issue);
(match ((Prims.op_disEquality issue.issue_level EInfo)) with
| true -> begin
((

let uu____4077 = (

let uu____4078 = (FStar_ST.op_Bang FStar_Options.abort_counter)
in (uu____4078 - (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____4077));
(

let uu____4117 = (

let uu____4118 = (FStar_ST.op_Bang FStar_Options.abort_counter)
in (Prims.op_Equality uu____4118 (Prims.parse_int "0")))
in (match (uu____4117) with
| true -> begin
(failwith "Aborting due to --abort_on")
end
| uu____4138 -> begin
()
end));
)
end
| uu____4139 -> begin
()
end);
))


let add_one : issue  ->  unit = (fun issue -> (FStar_Util.atomically (fun uu____4147 -> (

let uu____4148 = (FStar_ST.op_Bang current_handler)
in (wrapped_eh_add_one uu____4148 issue)))))


let add_many : issue Prims.list  ->  unit = (fun issues -> (FStar_Util.atomically (fun uu____4179 -> (

let uu____4180 = (

let uu____4185 = (FStar_ST.op_Bang current_handler)
in (wrapped_eh_add_one uu____4185))
in (FStar_List.iter uu____4180 issues)))))


let report_all : unit  ->  issue Prims.list = (fun uu____4211 -> (

let uu____4212 = (

let uu____4219 = (FStar_ST.op_Bang current_handler)
in uu____4219.eh_report)
in (uu____4212 ())))


let clear : unit  ->  unit = (fun uu____4243 -> (

let uu____4244 = (

let uu____4249 = (FStar_ST.op_Bang current_handler)
in uu____4249.eh_clear)
in (uu____4244 ())))


let set_handler : error_handler  ->  unit = (fun handler -> (

let issues = (report_all ())
in ((clear ());
(FStar_ST.op_Colon_Equals current_handler handler);
(add_many issues);
)))

type error_message_prefix =
{set_prefix : Prims.string  ->  unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : unit  ->  unit}


let __proj__Mkerror_message_prefix__item__set_prefix : error_message_prefix  ->  Prims.string  ->  unit = (fun projectee -> (match (projectee) with
| {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix} -> begin
set_prefix
end))


let __proj__Mkerror_message_prefix__item__append_prefix : error_message_prefix  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix} -> begin
append_prefix
end))


let __proj__Mkerror_message_prefix__item__clear_prefix : error_message_prefix  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix} -> begin
clear_prefix
end))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_prefix = (fun s -> (FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some (s))))
in (

let clear_prefix = (fun uu____4463 -> (FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None))
in (

let append_prefix = (fun s -> (

let uu____4515 = (FStar_ST.op_Bang pfx)
in (match (uu____4515) with
| FStar_Pervasives_Native.None -> begin
s
end
| FStar_Pervasives_Native.Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let findIndex : 'Auu____4572 'Auu____4573 . ('Auu____4572 * 'Auu____4573) Prims.list  ->  'Auu____4572  ->  Prims.int = (fun l v1 -> (FStar_All.pipe_right l (FStar_List.index (fun uu___83_4609 -> (match (uu___83_4609) with
| (e, uu____4615) when (Prims.op_Equality e v1) -> begin
true
end
| uu____4616 -> begin
false
end)))))


let errno_of_error : raw_error  ->  Prims.int = (fun e -> (findIndex default_flags e))


let flags : flag Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_warn_error_flags : unit = (

let rec aux = (fun r l -> (match (l) with
| [] -> begin
r
end
| ((e, f))::tl1 -> begin
(aux (FStar_List.append r ((f)::[])) tl1)
end))
in (

let uu____4691 = (aux [] default_flags)
in (FStar_ST.op_Colon_Equals flags uu____4691)))


let diag : FStar_Range.range  ->  Prims.string  ->  unit = (fun r msg -> (

let uu____4727 = (FStar_Options.debug_any ())
in (match (uu____4727) with
| true -> begin
(add_one (mk_issue EInfo (FStar_Pervasives_Native.Some (r)) msg FStar_Pervasives_Native.None))
end
| uu____4728 -> begin
()
end)))


let defensive_errno : Prims.int = (errno_of_error Warning_Defensive)


let lookup : flag Prims.list  ->  Prims.int  ->  flag = (fun flags1 errno -> (

let uu____4743 = ((Prims.op_Equality errno defensive_errno) && (FStar_Options.defensive_fail ()))
in (match (uu____4743) with
| true -> begin
CAlwaysError
end
| uu____4744 -> begin
(FStar_List.nth flags1 errno)
end)))


let log_issue : FStar_Range.range  ->  (raw_error * Prims.string)  ->  unit = (fun r uu____4758 -> (match (uu____4758) with
| (e, msg) -> begin
(

let errno = (errno_of_error e)
in (

let uu____4766 = (

let uu____4767 = (FStar_ST.op_Bang flags)
in (lookup uu____4767 errno))
in (match (uu____4766) with
| CAlwaysError -> begin
(add_one (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno))))
end
| CError -> begin
(add_one (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno))))
end
| CWarning -> begin
(add_one (mk_issue EWarning (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno))))
end
| CSilent -> begin
()
end
| CFatal -> begin
(

let i = (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno)))
in (

let uu____4794 = (FStar_Options.ide ())
in (match (uu____4794) with
| true -> begin
(add_one i)
end
| uu____4795 -> begin
(

let uu____4796 = (

let uu____4797 = (format_issue i)
in (Prims.strcat "don\'t use log_issue to report fatal error, should use raise_error: " uu____4797))
in (failwith uu____4796))
end)))
end)))
end))


let add_errors : (raw_error * Prims.string * FStar_Range.range) Prims.list  ->  unit = (fun errs -> (FStar_Util.atomically (fun uu____4820 -> (FStar_List.iter (fun uu____4832 -> (match (uu____4832) with
| (e, msg, r) -> begin
(

let uu____4842 = (

let uu____4847 = (message_prefix.append_prefix msg)
in ((e), (uu____4847)))
in (log_issue r uu____4842))
end)) errs))))


let issue_of_exn : Prims.exn  ->  issue FStar_Pervasives_Native.option = (fun uu___84_4854 -> (match (uu___84_4854) with
| Error (e, msg, r) -> begin
(

let errno = (errno_of_error e)
in (

let uu____4861 = (

let uu____4862 = (message_prefix.append_prefix msg)
in (mk_issue EError (FStar_Pervasives_Native.Some (r)) uu____4862 (FStar_Pervasives_Native.Some (errno))))
in FStar_Pervasives_Native.Some (uu____4861)))
end
| FStar_Util.NYI (msg) -> begin
(

let uu____4864 = (

let uu____4865 = (message_prefix.append_prefix msg)
in (mk_issue ENotImplemented FStar_Pervasives_Native.None uu____4865 FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____4864))
end
| Err (e, msg) -> begin
(

let errno = (errno_of_error e)
in (

let uu____4869 = (

let uu____4870 = (message_prefix.append_prefix msg)
in (mk_issue EError FStar_Pervasives_Native.None uu____4870 (FStar_Pervasives_Native.Some (errno))))
in FStar_Pervasives_Native.Some (uu____4869)))
end
| uu____4871 -> begin
FStar_Pervasives_Native.None
end))


let err_exn : Prims.exn  ->  unit = (fun exn -> (match ((Prims.op_Equality exn Stop)) with
| true -> begin
()
end
| uu____4877 -> begin
(

let uu____4878 = (issue_of_exn exn)
in (match (uu____4878) with
| FStar_Pervasives_Native.Some (issue) -> begin
(add_one issue)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise exn)
end))
end))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___85_4886 -> (match (uu___85_4886) with
| Error (uu____4887) -> begin
true
end
| FStar_Util.NYI (uu____4894) -> begin
true
end
| Stop -> begin
true
end
| Err (uu____4895) -> begin
true
end
| uu____4900 -> begin
false
end))


let stop_if_err : unit  ->  unit = (fun uu____4905 -> (

let uu____4906 = (

let uu____4907 = (get_err_count ())
in (uu____4907 > (Prims.parse_int "0")))
in (match (uu____4906) with
| true -> begin
(FStar_Exn.raise Stop)
end
| uu____4908 -> begin
()
end)))


let raise_error : 'Auu____4915 . (raw_error * Prims.string)  ->  FStar_Range.range  ->  'Auu____4915 = (fun uu____4928 r -> (match (uu____4928) with
| (e, msg) -> begin
(FStar_Exn.raise (Error (((e), (msg), (r)))))
end))


let raise_err : 'Auu____4940 . (raw_error * Prims.string)  ->  'Auu____4940 = (fun uu____4949 -> (match (uu____4949) with
| (e, msg) -> begin
(FStar_Exn.raise (Err (((e), (msg)))))
end))


let update_flags : (flag * Prims.string) Prims.list  ->  unit = (fun l -> (

let compare1 = (fun uu____4998 uu____4999 -> (match (((uu____4998), (uu____4999))) with
| ((uu____5032, (a, uu____5034)), (uu____5035, (b, uu____5037))) -> begin
(match ((a > b)) with
| true -> begin
(Prims.parse_int "1")
end
| uu____5062 -> begin
(match ((a < b)) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____5063 -> begin
(Prims.parse_int "0")
end)
end)
end))
in (

let set_one_flag = (fun f d -> (match (((f), (d))) with
| (CWarning, CAlwaysError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot turn an error into warning")))
end
| (CError, CAlwaysError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot turn an error into warning")))
end
| (CSilent, CAlwaysError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot silence an error")))
end
| (uu____5075, CFatal) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot reset the error level of a fatal error")))
end
| uu____5076 -> begin
f
end))
in (

let rec set_flag = (fun i l1 -> (

let d = (

let uu____5113 = (FStar_ST.op_Bang flags)
in (FStar_List.nth uu____5113 i))
in (match (l1) with
| [] -> begin
d
end
| ((f, (l2, h)))::tl1 -> begin
(match (((i >= l2) && (i <= h))) with
| true -> begin
(set_one_flag f d)
end
| uu____5173 -> begin
(match ((i < l2)) with
| true -> begin
d
end
| uu____5174 -> begin
(set_flag i tl1)
end)
end)
end)))
in (

let rec aux = (fun f i l1 sorted1 -> (match (l1) with
| [] -> begin
f
end
| (hd1)::tl1 -> begin
(

let uu____5232 = (

let uu____5235 = (

let uu____5238 = (set_flag i sorted1)
in (uu____5238)::[])
in (FStar_List.append f uu____5235))
in (aux uu____5232 (i + (Prims.parse_int "1")) tl1 sorted1))
end))
in (

let rec compute_range = (fun result l1 -> (match (l1) with
| [] -> begin
result
end
| ((f, s))::tl1 -> begin
(

let r = (FStar_Util.split s "..")
in (

let uu____5322 = (match (r) with
| (r1)::(r2)::[] -> begin
(

let uu____5333 = (FStar_Util.int_of_string r1)
in (

let uu____5334 = (FStar_Util.int_of_string r2)
in ((uu____5333), (uu____5334))))
end
| uu____5335 -> begin
(

let uu____5338 = (

let uu____5343 = (FStar_Util.format1 "Malformed warn-error range %s" s)
in ((Fatal_InvalidWarnErrorSetting), (uu____5343)))
in (raise_err uu____5338))
end)
in (match (uu____5322) with
| (l2, h) -> begin
((match (((l2 < (Prims.parse_int "0")) || (h >= (FStar_List.length default_flags)))) with
| true -> begin
(

let uu____5365 = (

let uu____5370 = (

let uu____5371 = (FStar_Util.string_of_int l2)
in (

let uu____5372 = (FStar_Util.string_of_int h)
in (FStar_Util.format2 "No error for warn_error %s..%s" uu____5371 uu____5372)))
in ((Fatal_InvalidWarnErrorSetting), (uu____5370)))
in (raise_err uu____5365))
end
| uu____5373 -> begin
()
end);
(compute_range (FStar_List.append result ((((f), (((l2), (h)))))::[])) tl1);
)
end)))
end))
in (

let range = (compute_range [] l)
in (

let sorted1 = (FStar_List.sortWith compare1 range)
in (

let uu____5440 = (

let uu____5443 = (FStar_ST.op_Bang flags)
in (aux [] (Prims.parse_int "0") uu____5443 sorted1))
in (FStar_ST.op_Colon_Equals flags uu____5440))))))))))


let catch_errors : 'a . (unit  ->  'a)  ->  (issue Prims.list * 'a FStar_Pervasives_Native.option) = (fun f -> (

let newh = (mk_default_handler false)
in (

let old = (FStar_ST.op_Bang current_handler)
in ((FStar_ST.op_Colon_Equals current_handler newh);
(

let r = (FStar_All.try_with (fun uu___87_5563 -> (match (()) with
| () -> begin
(

let r = (f ())
in FStar_Pervasives_Native.Some (r))
end)) (fun uu___86_5569 -> ((err_exn uu___86_5569);
FStar_Pervasives_Native.None;
)))
in (

let errs = (newh.eh_report ())
in ((FStar_ST.op_Colon_Equals current_handler old);
((errs), (r));
)));
))))




