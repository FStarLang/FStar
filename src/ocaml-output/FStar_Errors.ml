
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
| Warning_UnexpectedCheckedFile
| Fatal_ExtractionUnsupported


let uu___is_Error_DependencyAnalysisFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_DependencyAnalysisFailed -> begin
true
end
| uu____19 -> begin
false
end))


let uu___is_Error_IDETooManyPops : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDETooManyPops -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_Error_IDEUnrecognized : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDEUnrecognized -> begin
true
end
| uu____41 -> begin
false
end))


let uu___is_Error_InductiveTypeNotSatisfyPositivityCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InductiveTypeNotSatisfyPositivityCondition -> begin
true
end
| uu____52 -> begin
false
end))


let uu___is_Error_InvalidUniverseVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InvalidUniverseVar -> begin
true
end
| uu____63 -> begin
false
end))


let uu___is_Error_MissingFileName : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_MissingFileName -> begin
true
end
| uu____74 -> begin
false
end))


let uu___is_Error_ModuleFileNameMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_ModuleFileNameMismatch -> begin
true
end
| uu____85 -> begin
false
end))


let uu___is_Error_OpPlusInUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_OpPlusInUniverse -> begin
true
end
| uu____96 -> begin
false
end))


let uu___is_Error_OutOfRange : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_OutOfRange -> begin
true
end
| uu____107 -> begin
false
end))


let uu___is_Error_ProofObligationFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_ProofObligationFailed -> begin
true
end
| uu____118 -> begin
false
end))


let uu___is_Error_TooManyFiles : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TooManyFiles -> begin
true
end
| uu____129 -> begin
false
end))


let uu___is_Error_TypeCheckerFailToProve : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TypeCheckerFailToProve -> begin
true
end
| uu____140 -> begin
false
end))


let uu___is_Error_TypeError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TypeError -> begin
true
end
| uu____151 -> begin
false
end))


let uu___is_Error_UncontrainedUnificationVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UncontrainedUnificationVar -> begin
true
end
| uu____162 -> begin
false
end))


let uu___is_Error_UnexpectedGTotComputation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedGTotComputation -> begin
true
end
| uu____173 -> begin
false
end))


let uu___is_Error_UnexpectedInstance : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedInstance -> begin
true
end
| uu____184 -> begin
false
end))


let uu___is_Error_UnknownFatal_AssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnknownFatal_AssertionFailure -> begin
true
end
| uu____195 -> begin
false
end))


let uu___is_Error_Z3InvocationError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_Z3InvocationError -> begin
true
end
| uu____206 -> begin
false
end))


let uu___is_Error_IDEAssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDEAssertionFailure -> begin
true
end
| uu____217 -> begin
false
end))


let uu___is_Error_Z3SolverError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_Z3SolverError -> begin
true
end
| uu____228 -> begin
false
end))


let uu___is_Fatal_AbstractTypeDeclarationInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AbstractTypeDeclarationInInterface -> begin
true
end
| uu____239 -> begin
false
end))


let uu___is_Fatal_ActionMustHaveFunctionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ActionMustHaveFunctionType -> begin
true
end
| uu____250 -> begin
false
end))


let uu___is_Fatal_AlreadyDefinedTopLevelDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AlreadyDefinedTopLevelDeclaration -> begin
true
end
| uu____261 -> begin
false
end))


let uu___is_Fatal_ArgumentLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ArgumentLengthMismatch -> begin
true
end
| uu____272 -> begin
false
end))


let uu___is_Fatal_AssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssertionFailure -> begin
true
end
| uu____283 -> begin
false
end))


let uu___is_Fatal_AssignToImmutableValues : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssignToImmutableValues -> begin
true
end
| uu____294 -> begin
false
end))


let uu___is_Fatal_AssumeValInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssumeValInInterface -> begin
true
end
| uu____305 -> begin
false
end))


let uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BadlyInstantiatedSynthByTactic -> begin
true
end
| uu____316 -> begin
false
end))


let uu___is_Fatal_BadSignatureShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BadSignatureShape -> begin
true
end
| uu____327 -> begin
false
end))


let uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BinderAndArgsLengthMismatch -> begin
true
end
| uu____338 -> begin
false
end))


let uu___is_Fatal_BothValAndLetInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BothValAndLetInInterface -> begin
true
end
| uu____349 -> begin
false
end))


let uu___is_Fatal_CardinalityConstraintViolated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CardinalityConstraintViolated -> begin
true
end
| uu____360 -> begin
false
end))


let uu___is_Fatal_ComputationNotTotal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputationNotTotal -> begin
true
end
| uu____371 -> begin
false
end))


let uu___is_Fatal_ComputationTypeNotAllowed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputationTypeNotAllowed -> begin
true
end
| uu____382 -> begin
false
end))


let uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputedTypeNotMatchAnnotation -> begin
true
end
| uu____393 -> begin
false
end))


let uu___is_Fatal_ConstructorArgLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorArgLengthMismatch -> begin
true
end
| uu____404 -> begin
false
end))


let uu___is_Fatal_ConstructorFailedCheck : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorFailedCheck -> begin
true
end
| uu____415 -> begin
false
end))


let uu___is_Fatal_ConstructorNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorNotFound -> begin
true
end
| uu____426 -> begin
false
end))


let uu___is_Fatal_ConstsructorBuildWrongType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstsructorBuildWrongType -> begin
true
end
| uu____437 -> begin
false
end))


let uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CycleInRecTypeAbbreviation -> begin
true
end
| uu____448 -> begin
false
end))


let uu___is_Fatal_DataContructorNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DataContructorNotFound -> begin
true
end
| uu____459 -> begin
false
end))


let uu___is_Fatal_DefaultQualifierNotAllowedOnEffects : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DefaultQualifierNotAllowedOnEffects -> begin
true
end
| uu____470 -> begin
false
end))


let uu___is_Fatal_DefinitionNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DefinitionNotFound -> begin
true
end
| uu____481 -> begin
false
end))


let uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DisjuctivePatternVarsMismatch -> begin
true
end
| uu____492 -> begin
false
end))


let uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DivergentComputationCannotBeIncludedInTotal -> begin
true
end
| uu____503 -> begin
false
end))


let uu___is_Fatal_DuplicateInImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateInImplementation -> begin
true
end
| uu____514 -> begin
false
end))


let uu___is_Fatal_DuplicateModuleOrInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateModuleOrInterface -> begin
true
end
| uu____525 -> begin
false
end))


let uu___is_Fatal_DuplicateTopLevelNames : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateTopLevelNames -> begin
true
end
| uu____536 -> begin
false
end))


let uu___is_Fatal_DuplicateTypeAnnotationAndValDecl : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateTypeAnnotationAndValDecl -> begin
true
end
| uu____547 -> begin
false
end))


let uu___is_Fatal_EffectCannotBeReified : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectCannotBeReified -> begin
true
end
| uu____558 -> begin
false
end))


let uu___is_Fatal_EffectConstructorNotFullyApplied : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectConstructorNotFullyApplied -> begin
true
end
| uu____569 -> begin
false
end))


let uu___is_Fatal_EffectfulAndPureComputationMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectfulAndPureComputationMismatch -> begin
true
end
| uu____580 -> begin
false
end))


let uu___is_Fatal_EffectNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectNotFound -> begin
true
end
| uu____591 -> begin
false
end))


let uu___is_Fatal_EffectsCannotBeComposed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectsCannotBeComposed -> begin
true
end
| uu____602 -> begin
false
end))


let uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ErrorInSolveDeferredConstraints -> begin
true
end
| uu____613 -> begin
false
end))


let uu___is_Fatal_ErrorsReported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ErrorsReported -> begin
true
end
| uu____624 -> begin
false
end))


let uu___is_Fatal_EscapedBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EscapedBoundVar -> begin
true
end
| uu____635 -> begin
false
end))


let uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedArrowAnnotatedType -> begin
true
end
| uu____646 -> begin
false
end))


let uu___is_Fatal_ExpectedGhostExpression : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedGhostExpression -> begin
true
end
| uu____657 -> begin
false
end))


let uu___is_Fatal_ExpectedPureExpression : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedPureExpression -> begin
true
end
| uu____668 -> begin
false
end))


let uu___is_Fatal_ExpectNormalizedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectNormalizedEffect -> begin
true
end
| uu____679 -> begin
false
end))


let uu___is_Fatal_ExpectTermGotFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectTermGotFunction -> begin
true
end
| uu____690 -> begin
false
end))


let uu___is_Fatal_ExpectTrivialPreCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectTrivialPreCondition -> begin
true
end
| uu____701 -> begin
false
end))


let uu___is_Fatal_FailToCompileNativeTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToCompileNativeTactic -> begin
true
end
| uu____712 -> begin
false
end))


let uu___is_Fatal_FailToExtractNativeTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToExtractNativeTactic -> begin
true
end
| uu____723 -> begin
false
end))


let uu___is_Fatal_FailToProcessPragma : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToProcessPragma -> begin
true
end
| uu____734 -> begin
false
end))


let uu___is_Fatal_FailToResolveImplicitArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToResolveImplicitArgument -> begin
true
end
| uu____745 -> begin
false
end))


let uu___is_Fatal_FailToSolveUniverseInEquality : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToSolveUniverseInEquality -> begin
true
end
| uu____756 -> begin
false
end))


let uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FieldsNotBelongToSameRecordType -> begin
true
end
| uu____767 -> begin
false
end))


let uu___is_Fatal_ForbiddenReferenceToCurrentModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ForbiddenReferenceToCurrentModule -> begin
true
end
| uu____778 -> begin
false
end))


let uu___is_Fatal_FreeVariables : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FreeVariables -> begin
true
end
| uu____789 -> begin
false
end))


let uu___is_Fatal_FunctionTypeExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FunctionTypeExpected -> begin
true
end
| uu____800 -> begin
false
end))


let uu___is_Fatal_IdentifierNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IdentifierNotFound -> begin
true
end
| uu____811 -> begin
false
end))


let uu___is_Fatal_IllAppliedConstant : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllAppliedConstant -> begin
true
end
| uu____822 -> begin
false
end))


let uu___is_Fatal_IllegalCharInByteArray : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllegalCharInByteArray -> begin
true
end
| uu____833 -> begin
false
end))


let uu___is_Fatal_IllegalCharInOperatorName : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllegalCharInOperatorName -> begin
true
end
| uu____844 -> begin
false
end))


let uu___is_Fatal_IllTyped : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllTyped -> begin
true
end
| uu____855 -> begin
false
end))


let uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleAbbrevLidBundle -> begin
true
end
| uu____866 -> begin
false
end))


let uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleAbbrevRenameBundle -> begin
true
end
| uu____877 -> begin
false
end))


let uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleInductiveWithAbbrev -> begin
true
end
| uu____888 -> begin
false
end))


let uu___is_Fatal_ImpossiblePrePostAbs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossiblePrePostAbs -> begin
true
end
| uu____899 -> begin
false
end))


let uu___is_Fatal_ImpossiblePrePostArrow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossiblePrePostArrow -> begin
true
end
| uu____910 -> begin
false
end))


let uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleToGenerateDMEffect -> begin
true
end
| uu____921 -> begin
false
end))


let uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleTypeAbbrevBundle -> begin
true
end
| uu____932 -> begin
false
end))


let uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleTypeAbbrevSigeltBundle -> begin
true
end
| uu____943 -> begin
false
end))


let uu___is_Fatal_IncludeModuleNotPrepared : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncludeModuleNotPrepared -> begin
true
end
| uu____954 -> begin
false
end))


let uu___is_Fatal_IncoherentInlineUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncoherentInlineUniverse -> begin
true
end
| uu____965 -> begin
false
end))


let uu___is_Fatal_IncompatibleKinds : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleKinds -> begin
true
end
| uu____976 -> begin
false
end))


let uu___is_Fatal_IncompatibleNumberOfTypes : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleNumberOfTypes -> begin
true
end
| uu____987 -> begin
false
end))


let uu___is_Fatal_IncompatibleSetOfUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleSetOfUniverse -> begin
true
end
| uu____998 -> begin
false
end))


let uu___is_Fatal_IncompatibleUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleUniverse -> begin
true
end
| uu____1009 -> begin
false
end))


let uu___is_Fatal_InconsistentImplicitArgumentAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentImplicitArgumentAnnotation -> begin
true
end
| uu____1020 -> begin
false
end))


let uu___is_Fatal_InconsistentImplicitQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentImplicitQualifier -> begin
true
end
| uu____1031 -> begin
false
end))


let uu___is_Fatal_InconsistentQualifierAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentQualifierAnnotation -> begin
true
end
| uu____1042 -> begin
false
end))


let uu___is_Fatal_InferredTypeCauseVarEscape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InferredTypeCauseVarEscape -> begin
true
end
| uu____1053 -> begin
false
end))


let uu___is_Fatal_InlineRenamedAsUnfold : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InlineRenamedAsUnfold -> begin
true
end
| uu____1064 -> begin
false
end))


let uu___is_Fatal_InsufficientPatternArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InsufficientPatternArguments -> begin
true
end
| uu____1075 -> begin
false
end))


let uu___is_Fatal_InterfaceAlreadyProcessed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceAlreadyProcessed -> begin
true
end
| uu____1086 -> begin
false
end))


let uu___is_Fatal_InterfaceNotImplementedByModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceNotImplementedByModule -> begin
true
end
| uu____1097 -> begin
false
end))


let uu___is_Fatal_InterfaceWithTypeImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceWithTypeImplementation -> begin
true
end
| uu____1108 -> begin
false
end))


let uu___is_Fatal_InvalidFloatingPointNumber : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidFloatingPointNumber -> begin
true
end
| uu____1119 -> begin
false
end))


let uu___is_Fatal_InvalidFSDocKeyword : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidFSDocKeyword -> begin
true
end
| uu____1130 -> begin
false
end))


let uu___is_Fatal_InvalidIdentifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidIdentifier -> begin
true
end
| uu____1141 -> begin
false
end))


let uu___is_Fatal_InvalidLemmaArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidLemmaArgument -> begin
true
end
| uu____1152 -> begin
false
end))


let uu___is_Fatal_InvalidNumericLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidNumericLiteral -> begin
true
end
| uu____1163 -> begin
false
end))


let uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidRedefinitionOfLexT -> begin
true
end
| uu____1174 -> begin
false
end))


let uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidUnicodeInStringLiteral -> begin
true
end
| uu____1185 -> begin
false
end))


let uu___is_Fatal_InvalidUTF8Encoding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidUTF8Encoding -> begin
true
end
| uu____1196 -> begin
false
end))


let uu___is_Fatal_InvalidWarnErrorSetting : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidWarnErrorSetting -> begin
true
end
| uu____1207 -> begin
false
end))


let uu___is_Fatal_LetBoundMonadicMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetBoundMonadicMismatch -> begin
true
end
| uu____1218 -> begin
false
end))


let uu___is_Fatal_LetMutableForVariablesOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetMutableForVariablesOnly -> begin
true
end
| uu____1229 -> begin
false
end))


let uu___is_Fatal_LetOpenModuleOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetOpenModuleOnly -> begin
true
end
| uu____1240 -> begin
false
end))


let uu___is_Fatal_LetRecArgumentMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetRecArgumentMismatch -> begin
true
end
| uu____1251 -> begin
false
end))


let uu___is_Fatal_MalformedActionDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MalformedActionDeclaration -> begin
true
end
| uu____1262 -> begin
false
end))


let uu___is_Fatal_MismatchedPatternType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MismatchedPatternType -> begin
true
end
| uu____1273 -> begin
false
end))


let uu___is_Fatal_MismatchUniversePolymorphic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MismatchUniversePolymorphic -> begin
true
end
| uu____1284 -> begin
false
end))


let uu___is_Fatal_MissingDataConstructor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingDataConstructor -> begin
true
end
| uu____1295 -> begin
false
end))


let uu___is_Fatal_MissingExposeInterfacesOption : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingExposeInterfacesOption -> begin
true
end
| uu____1306 -> begin
false
end))


let uu___is_Fatal_MissingFieldInRecord : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingFieldInRecord -> begin
true
end
| uu____1317 -> begin
false
end))


let uu___is_Fatal_MissingImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingImplementation -> begin
true
end
| uu____1328 -> begin
false
end))


let uu___is_Fatal_MissingImplicitArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingImplicitArguments -> begin
true
end
| uu____1339 -> begin
false
end))


let uu___is_Fatal_MissingInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingInterface -> begin
true
end
| uu____1350 -> begin
false
end))


let uu___is_Fatal_MissingNameInBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingNameInBinder -> begin
true
end
| uu____1361 -> begin
false
end))


let uu___is_Fatal_MissingPrimsModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingPrimsModule -> begin
true
end
| uu____1372 -> begin
false
end))


let uu___is_Fatal_MissingQuantifierBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingQuantifierBinder -> begin
true
end
| uu____1383 -> begin
false
end))


let uu___is_Fatal_ModuleExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleExpected -> begin
true
end
| uu____1394 -> begin
false
end))


let uu___is_Fatal_ModuleFileNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleFileNotFound -> begin
true
end
| uu____1405 -> begin
false
end))


let uu___is_Fatal_ModuleFirstStatement : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleFirstStatement -> begin
true
end
| uu____1416 -> begin
false
end))


let uu___is_Fatal_ModuleNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleNotFound -> begin
true
end
| uu____1427 -> begin
false
end))


let uu___is_Fatal_ModuleOrFileNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleOrFileNotFound -> begin
true
end
| uu____1438 -> begin
false
end))


let uu___is_Fatal_MonadAlreadyDefined : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MonadAlreadyDefined -> begin
true
end
| uu____1449 -> begin
false
end))


let uu___is_Fatal_MoreThanOneDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MoreThanOneDeclaration -> begin
true
end
| uu____1460 -> begin
false
end))


let uu___is_Fatal_MultipleLetBinding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MultipleLetBinding -> begin
true
end
| uu____1471 -> begin
false
end))


let uu___is_Fatal_NameNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NameNotFound -> begin
true
end
| uu____1482 -> begin
false
end))


let uu___is_Fatal_NameSpaceNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NameSpaceNotFound -> begin
true
end
| uu____1493 -> begin
false
end))


let uu___is_Fatal_NegativeUniverseConstFatal_NotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NegativeUniverseConstFatal_NotSupported -> begin
true
end
| uu____1504 -> begin
false
end))


let uu___is_Fatal_NoFileProvided : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NoFileProvided -> begin
true
end
| uu____1515 -> begin
false
end))


let uu___is_Fatal_NonInductiveInMutuallyDefinedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonInductiveInMutuallyDefinedType -> begin
true
end
| uu____1526 -> begin
false
end))


let uu___is_Fatal_NonLinearPatternNotPermitted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonLinearPatternNotPermitted -> begin
true
end
| uu____1537 -> begin
false
end))


let uu___is_Fatal_NonLinearPatternVars : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonLinearPatternVars -> begin
true
end
| uu____1548 -> begin
false
end))


let uu___is_Fatal_NonSingletonTopLevel : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonSingletonTopLevel -> begin
true
end
| uu____1559 -> begin
false
end))


let uu___is_Fatal_NonSingletonTopLevelModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonSingletonTopLevelModule -> begin
true
end
| uu____1570 -> begin
false
end))


let uu___is_Fatal_NonTopRecFunctionNotFullyEncoded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonTopRecFunctionNotFullyEncoded -> begin
true
end
| uu____1581 -> begin
false
end))


let uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonTrivialPreConditionInPrims -> begin
true
end
| uu____1592 -> begin
false
end))


let uu___is_Fatal_NonVariableInductiveTypeParameter : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonVariableInductiveTypeParameter -> begin
true
end
| uu____1603 -> begin
false
end))


let uu___is_Fatal_NotApplicationOrFv : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotApplicationOrFv -> begin
true
end
| uu____1614 -> begin
false
end))


let uu___is_Fatal_NotEnoughArgsToEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotEnoughArgsToEffect -> begin
true
end
| uu____1625 -> begin
false
end))


let uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotEnoughArgumentsForEffect -> begin
true
end
| uu____1636 -> begin
false
end))


let uu___is_Fatal_NotFunctionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotFunctionType -> begin
true
end
| uu____1647 -> begin
false
end))


let uu___is_Fatal_NotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotSupported -> begin
true
end
| uu____1658 -> begin
false
end))


let uu___is_Fatal_NotTopLevelModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotTopLevelModule -> begin
true
end
| uu____1669 -> begin
false
end))


let uu___is_Fatal_NotValidFStarFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotValidFStarFile -> begin
true
end
| uu____1680 -> begin
false
end))


let uu___is_Fatal_NotValidIncludeDirectory : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotValidIncludeDirectory -> begin
true
end
| uu____1691 -> begin
false
end))


let uu___is_Fatal_OneModulePerFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OneModulePerFile -> begin
true
end
| uu____1702 -> begin
false
end))


let uu___is_Fatal_OpenGoalsInSynthesis : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OpenGoalsInSynthesis -> begin
true
end
| uu____1713 -> begin
false
end))


let uu___is_Fatal_OptionsNotCompatible : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OptionsNotCompatible -> begin
true
end
| uu____1724 -> begin
false
end))


let uu___is_Fatal_OutOfOrder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OutOfOrder -> begin
true
end
| uu____1735 -> begin
false
end))


let uu___is_Fatal_ParseErrors : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ParseErrors -> begin
true
end
| uu____1746 -> begin
false
end))


let uu___is_Fatal_ParseItError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ParseItError -> begin
true
end
| uu____1757 -> begin
false
end))


let uu___is_Fatal_PolyTypeExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PolyTypeExpected -> begin
true
end
| uu____1768 -> begin
false
end))


let uu___is_Fatal_PossibleInfiniteTyp : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PossibleInfiniteTyp -> begin
true
end
| uu____1779 -> begin
false
end))


let uu___is_Fatal_PreModuleMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PreModuleMismatch -> begin
true
end
| uu____1790 -> begin
false
end))


let uu___is_Fatal_QulifierListNotPermitted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_QulifierListNotPermitted -> begin
true
end
| uu____1801 -> begin
false
end))


let uu___is_Fatal_RecursiveFunctionLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_RecursiveFunctionLiteral -> begin
true
end
| uu____1812 -> begin
false
end))


let uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ReflectOnlySupportedOnEffects -> begin
true
end
| uu____1823 -> begin
false
end))


let uu___is_Fatal_ReservedPrefix : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ReservedPrefix -> begin
true
end
| uu____1834 -> begin
false
end))


let uu___is_Fatal_SMTOutputParseError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTOutputParseError -> begin
true
end
| uu____1845 -> begin
false
end))


let uu___is_Fatal_SMTSolverError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTSolverError -> begin
true
end
| uu____1856 -> begin
false
end))


let uu___is_Fatal_SyntaxError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SyntaxError -> begin
true
end
| uu____1867 -> begin
false
end))


let uu___is_Fatal_SynthByTacticError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SynthByTacticError -> begin
true
end
| uu____1878 -> begin
false
end))


let uu___is_Fatal_TacticGotStuck : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TacticGotStuck -> begin
true
end
| uu____1889 -> begin
false
end))


let uu___is_Fatal_TcOneFragmentFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TcOneFragmentFailed -> begin
true
end
| uu____1900 -> begin
false
end))


let uu___is_Fatal_TermOutsideOfDefLanguage : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TermOutsideOfDefLanguage -> begin
true
end
| uu____1911 -> begin
false
end))


let uu___is_Fatal_ToManyArgumentToFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ToManyArgumentToFunction -> begin
true
end
| uu____1922 -> begin
false
end))


let uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyOrTooFewFileMatch -> begin
true
end
| uu____1933 -> begin
false
end))


let uu___is_Fatal_TooManyPatternArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyPatternArguments -> begin
true
end
| uu____1944 -> begin
false
end))


let uu___is_Fatal_TooManyUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyUniverse -> begin
true
end
| uu____1955 -> begin
false
end))


let uu___is_Fatal_TypeMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TypeMismatch -> begin
true
end
| uu____1966 -> begin
false
end))


let uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TypeWithinPatternsAllowedOnVariablesOnly -> begin
true
end
| uu____1977 -> begin
false
end))


let uu___is_Fatal_UnableToReadFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnableToReadFile -> begin
true
end
| uu____1988 -> begin
false
end))


let uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnepxectedOrUnboundOperator -> begin
true
end
| uu____1999 -> begin
false
end))


let uu___is_Fatal_UnexpectedBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedBinder -> begin
true
end
| uu____2010 -> begin
false
end))


let uu___is_Fatal_UnexpectedBindShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedBindShape -> begin
true
end
| uu____2021 -> begin
false
end))


let uu___is_Fatal_UnexpectedChar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedChar -> begin
true
end
| uu____2032 -> begin
false
end))


let uu___is_Fatal_UnexpectedComputationTypeForLetRec : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedComputationTypeForLetRec -> begin
true
end
| uu____2043 -> begin
false
end))


let uu___is_Fatal_UnexpectedConstructorType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedConstructorType -> begin
true
end
| uu____2054 -> begin
false
end))


let uu___is_Fatal_UnexpectedDataConstructor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedDataConstructor -> begin
true
end
| uu____2065 -> begin
false
end))


let uu___is_Fatal_UnexpectedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedEffect -> begin
true
end
| uu____2076 -> begin
false
end))


let uu___is_Fatal_UnexpectedEmptyRecord : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedEmptyRecord -> begin
true
end
| uu____2087 -> begin
false
end))


let uu___is_Fatal_UnexpectedExpressionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedExpressionType -> begin
true
end
| uu____2098 -> begin
false
end))


let uu___is_Fatal_UnexpectedFunctionParameterType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedFunctionParameterType -> begin
true
end
| uu____2109 -> begin
false
end))


let uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGeneralizedUniverse -> begin
true
end
| uu____2120 -> begin
false
end))


let uu___is_Fatal_UnexpectedGTotForLetRec : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGTotForLetRec -> begin
true
end
| uu____2131 -> begin
false
end))


let uu___is_Fatal_UnexpectedGuard : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGuard -> begin
true
end
| uu____2142 -> begin
false
end))


let uu___is_Fatal_UnexpectedIdentifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedIdentifier -> begin
true
end
| uu____2153 -> begin
false
end))


let uu___is_Fatal_UnexpectedImplicitArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedImplicitArgument -> begin
true
end
| uu____2164 -> begin
false
end))


let uu___is_Fatal_UnexpectedImplictArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedImplictArgument -> begin
true
end
| uu____2175 -> begin
false
end))


let uu___is_Fatal_UnexpectedInductivetype : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedInductivetype -> begin
true
end
| uu____2186 -> begin
false
end))


let uu___is_Fatal_UnexpectedLetBinding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedLetBinding -> begin
true
end
| uu____2197 -> begin
false
end))


let uu___is_Fatal_UnexpectedModuleDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedModuleDeclaration -> begin
true
end
| uu____2208 -> begin
false
end))


let uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedNumberOfUniverse -> begin
true
end
| uu____2219 -> begin
false
end))


let uu___is_Fatal_UnexpectedNumericLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedNumericLiteral -> begin
true
end
| uu____2230 -> begin
false
end))


let uu___is_Fatal_UnexpectedOperatorSymbol : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedOperatorSymbol -> begin
true
end
| uu____2241 -> begin
false
end))


let uu___is_Fatal_UnexpectedPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedPattern -> begin
true
end
| uu____2252 -> begin
false
end))


let uu___is_Fatal_UnexpectedPosition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedPosition -> begin
true
end
| uu____2263 -> begin
false
end))


let uu___is_Fatal_UnExpectedPreCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnExpectedPreCondition -> begin
true
end
| uu____2274 -> begin
false
end))


let uu___is_Fatal_UnexpectedReturnShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedReturnShape -> begin
true
end
| uu____2285 -> begin
false
end))


let uu___is_Fatal_UnexpectedSignatureForMonad : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedSignatureForMonad -> begin
true
end
| uu____2296 -> begin
false
end))


let uu___is_Fatal_UnexpectedTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTerm -> begin
true
end
| uu____2307 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermInUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermInUniverse -> begin
true
end
| uu____2318 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermType -> begin
true
end
| uu____2329 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermVQuote : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermVQuote -> begin
true
end
| uu____2340 -> begin
false
end))


let uu___is_Fatal_UnexpectedUniversePolymorphicReturn : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedUniversePolymorphicReturn -> begin
true
end
| uu____2351 -> begin
false
end))


let uu___is_Fatal_UnexpectedUniverseVariable : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedUniverseVariable -> begin
true
end
| uu____2362 -> begin
false
end))


let uu___is_Fatal_UnfoldableDeprecated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnfoldableDeprecated -> begin
true
end
| uu____2373 -> begin
false
end))


let uu___is_Fatal_UnificationNotWellFormed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnificationNotWellFormed -> begin
true
end
| uu____2384 -> begin
false
end))


let uu___is_Fatal_Uninstantiated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_Uninstantiated -> begin
true
end
| uu____2395 -> begin
false
end))


let uu___is_Error_UninstantiatedUnificationVarInTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UninstantiatedUnificationVarInTactic -> begin
true
end
| uu____2406 -> begin
false
end))


let uu___is_Fatal_UninstantiatedVarInTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UninstantiatedVarInTactic -> begin
true
end
| uu____2417 -> begin
false
end))


let uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UniverseMightContainSumOfTwoUnivVars -> begin
true
end
| uu____2428 -> begin
false
end))


let uu___is_Fatal_UniversePolymorphicInnerLetBound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UniversePolymorphicInnerLetBound -> begin
true
end
| uu____2439 -> begin
false
end))


let uu___is_Fatal_UnknownAttribute : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnknownAttribute -> begin
true
end
| uu____2450 -> begin
false
end))


let uu___is_Fatal_UnknownToolForDep : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnknownToolForDep -> begin
true
end
| uu____2461 -> begin
false
end))


let uu___is_Fatal_UnrecognizedExtension : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnrecognizedExtension -> begin
true
end
| uu____2472 -> begin
false
end))


let uu___is_Fatal_UnresolvedPatternVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnresolvedPatternVar -> begin
true
end
| uu____2483 -> begin
false
end))


let uu___is_Fatal_UnsupportedConstant : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedConstant -> begin
true
end
| uu____2494 -> begin
false
end))


let uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedDisjuctivePatterns -> begin
true
end
| uu____2505 -> begin
false
end))


let uu___is_Fatal_UnsupportedQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedQualifier -> begin
true
end
| uu____2516 -> begin
false
end))


let uu___is_Fatal_UserTacticFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UserTacticFailure -> begin
true
end
| uu____2527 -> begin
false
end))


let uu___is_Fatal_ValueRestriction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ValueRestriction -> begin
true
end
| uu____2538 -> begin
false
end))


let uu___is_Fatal_VariableNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_VariableNotFound -> begin
true
end
| uu____2549 -> begin
false
end))


let uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongBodyTypeForReturnWP -> begin
true
end
| uu____2560 -> begin
false
end))


let uu___is_Fatal_WrongDataAppHeadFormat : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongDataAppHeadFormat -> begin
true
end
| uu____2571 -> begin
false
end))


let uu___is_Fatal_WrongDefinitionOrder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongDefinitionOrder -> begin
true
end
| uu____2582 -> begin
false
end))


let uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongResultTypeAfterConstrutor -> begin
true
end
| uu____2593 -> begin
false
end))


let uu___is_Fatal_WrongTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongTerm -> begin
true
end
| uu____2604 -> begin
false
end))


let uu___is_Fatal_WhenClauseNotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WhenClauseNotSupported -> begin
true
end
| uu____2615 -> begin
false
end))


let uu___is_Unused01 : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unused01 -> begin
true
end
| uu____2626 -> begin
false
end))


let uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_AddImplicitAssumeNewQualifier -> begin
true
end
| uu____2637 -> begin
false
end))


let uu___is_Warning_AdmitWithoutDefinition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_AdmitWithoutDefinition -> begin
true
end
| uu____2648 -> begin
false
end))


let uu___is_Warning_CachedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CachedFile -> begin
true
end
| uu____2659 -> begin
false
end))


let uu___is_Warning_DefinitionNotTranslated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DefinitionNotTranslated -> begin
true
end
| uu____2670 -> begin
false
end))


let uu___is_Warning_DependencyFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DependencyFound -> begin
true
end
| uu____2681 -> begin
false
end))


let uu___is_Warning_DeprecatedEqualityOnBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedEqualityOnBinder -> begin
true
end
| uu____2692 -> begin
false
end))


let uu___is_Warning_DeprecatedOpaqueQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedOpaqueQualifier -> begin
true
end
| uu____2703 -> begin
false
end))


let uu___is_Warning_DocOverwrite : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DocOverwrite -> begin
true
end
| uu____2714 -> begin
false
end))


let uu___is_Warning_FileNotWritten : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FileNotWritten -> begin
true
end
| uu____2725 -> begin
false
end))


let uu___is_Warning_Filtered : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Filtered -> begin
true
end
| uu____2736 -> begin
false
end))


let uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FunctionLiteralPrecisionLoss -> begin
true
end
| uu____2747 -> begin
false
end))


let uu___is_Warning_FunctionNotExtacted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FunctionNotExtacted -> begin
true
end
| uu____2758 -> begin
false
end))


let uu___is_Warning_HintFailedToReplayProof : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_HintFailedToReplayProof -> begin
true
end
| uu____2769 -> begin
false
end))


let uu___is_Warning_HitReplayFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_HitReplayFailed -> begin
true
end
| uu____2780 -> begin
false
end))


let uu___is_Warning_IDEIgnoreCodeGen : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IDEIgnoreCodeGen -> begin
true
end
| uu____2791 -> begin
false
end))


let uu___is_Warning_IllFormedGoal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IllFormedGoal -> begin
true
end
| uu____2802 -> begin
false
end))


let uu___is_Warning_InaccessibleArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_InaccessibleArgument -> begin
true
end
| uu____2813 -> begin
false
end))


let uu___is_Warning_IncoherentImplicitQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IncoherentImplicitQualifier -> begin
true
end
| uu____2824 -> begin
false
end))


let uu___is_Warning_IrrelevantQualifierOnArgumentToReflect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IrrelevantQualifierOnArgumentToReflect -> begin
true
end
| uu____2835 -> begin
false
end))


let uu___is_Warning_IrrelevantQualifierOnArgumentToReify : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IrrelevantQualifierOnArgumentToReify -> begin
true
end
| uu____2846 -> begin
false
end))


let uu___is_Warning_MalformedWarnErrorList : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MalformedWarnErrorList -> begin
true
end
| uu____2857 -> begin
false
end))


let uu___is_Warning_MetaAlienNotATmUnknown : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MetaAlienNotATmUnknown -> begin
true
end
| uu____2868 -> begin
false
end))


let uu___is_Warning_MultipleAscriptions : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MultipleAscriptions -> begin
true
end
| uu____2879 -> begin
false
end))


let uu___is_Warning_NondependentUserDefinedDataType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NondependentUserDefinedDataType -> begin
true
end
| uu____2890 -> begin
false
end))


let uu___is_Warning_NonListLiteralSMTPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NonListLiteralSMTPattern -> begin
true
end
| uu____2901 -> begin
false
end))


let uu___is_Warning_NormalizationFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NormalizationFailure -> begin
true
end
| uu____2912 -> begin
false
end))


let uu___is_Warning_NotDependentArrow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NotDependentArrow -> begin
true
end
| uu____2923 -> begin
false
end))


let uu___is_Warning_NotEmbedded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NotEmbedded -> begin
true
end
| uu____2934 -> begin
false
end))


let uu___is_Warning_PatternMissingBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_PatternMissingBoundVar -> begin
true
end
| uu____2945 -> begin
false
end))


let uu___is_Warning_RecursiveDependency : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_RecursiveDependency -> begin
true
end
| uu____2956 -> begin
false
end))


let uu___is_Warning_RedundantExplicitCurrying : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_RedundantExplicitCurrying -> begin
true
end
| uu____2967 -> begin
false
end))


let uu___is_Warning_SMTPatTDeprecated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_SMTPatTDeprecated -> begin
true
end
| uu____2978 -> begin
false
end))


let uu___is_Warning_SMTPatternIllFormed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_SMTPatternIllFormed -> begin
true
end
| uu____2989 -> begin
false
end))


let uu___is_Warning_TopLevelEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_TopLevelEffect -> begin
true
end
| uu____3000 -> begin
false
end))


let uu___is_Warning_UnboundModuleReference : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnboundModuleReference -> begin
true
end
| uu____3011 -> begin
false
end))


let uu___is_Warning_UnexpectedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedFile -> begin
true
end
| uu____3022 -> begin
false
end))


let uu___is_Warning_UnexpectedFsTypApp : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedFsTypApp -> begin
true
end
| uu____3033 -> begin
false
end))


let uu___is_Warning_UnexpectedZ3Output : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedZ3Output -> begin
true
end
| uu____3044 -> begin
false
end))


let uu___is_Warning_UnprotectedTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnprotectedTerm -> begin
true
end
| uu____3055 -> begin
false
end))


let uu___is_Warning_UnrecognizedAttribute : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnrecognizedAttribute -> begin
true
end
| uu____3066 -> begin
false
end))


let uu___is_Warning_UpperBoundCandidateAlreadyVisited : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UpperBoundCandidateAlreadyVisited -> begin
true
end
| uu____3077 -> begin
false
end))


let uu___is_Warning_UseDefaultEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UseDefaultEffect -> begin
true
end
| uu____3088 -> begin
false
end))


let uu___is_Warning_WrongErrorLocation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_WrongErrorLocation -> begin
true
end
| uu____3099 -> begin
false
end))


let uu___is_Warning_Z3InvocationWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Z3InvocationWarning -> begin
true
end
| uu____3110 -> begin
false
end))


let uu___is_Warning_CallNotImplementedAsWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CallNotImplementedAsWarning -> begin
true
end
| uu____3121 -> begin
false
end))


let uu___is_Warning_MissingInterfaceOrImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MissingInterfaceOrImplementation -> begin
true
end
| uu____3132 -> begin
false
end))


let uu___is_Warning_ConstructorBuildsUnexpectedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ConstructorBuildsUnexpectedType -> begin
true
end
| uu____3143 -> begin
false
end))


let uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ModuleOrFileNotFoundWarning -> begin
true
end
| uu____3154 -> begin
false
end))


let uu___is_Error_NoLetMutable : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_NoLetMutable -> begin
true
end
| uu____3165 -> begin
false
end))


let uu___is_Error_BadImplicit : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadImplicit -> begin
true
end
| uu____3176 -> begin
false
end))


let uu___is_Warning_DeprecatedDefinition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedDefinition -> begin
true
end
| uu____3187 -> begin
false
end))


let uu___is_Fatal_SMTEncodingArityMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTEncodingArityMismatch -> begin
true
end
| uu____3198 -> begin
false
end))


let uu___is_Warning_Defensive : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Defensive -> begin
true
end
| uu____3209 -> begin
false
end))


let uu___is_Warning_CantInspect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CantInspect -> begin
true
end
| uu____3220 -> begin
false
end))


let uu___is_Warning_NilGivenExplicitArgs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NilGivenExplicitArgs -> begin
true
end
| uu____3231 -> begin
false
end))


let uu___is_Warning_ConsAppliedExplicitArgs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ConsAppliedExplicitArgs -> begin
true
end
| uu____3242 -> begin
false
end))


let uu___is_Warning_UnembedBinderKnot : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnembedBinderKnot -> begin
true
end
| uu____3253 -> begin
false
end))


let uu___is_Fatal_TacticProofRelevantGoal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TacticProofRelevantGoal -> begin
true
end
| uu____3264 -> begin
false
end))


let uu___is_Warning_TacAdmit : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_TacAdmit -> begin
true
end
| uu____3275 -> begin
false
end))


let uu___is_Fatal_IncoherentPatterns : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncoherentPatterns -> begin
true
end
| uu____3286 -> begin
false
end))


let uu___is_Error_NoSMTButNeeded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_NoSMTButNeeded -> begin
true
end
| uu____3297 -> begin
false
end))


let uu___is_Fatal_UnexpectedAntiquotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedAntiquotation -> begin
true
end
| uu____3308 -> begin
false
end))


let uu___is_Fatal_SplicedUndef : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SplicedUndef -> begin
true
end
| uu____3319 -> begin
false
end))


let uu___is_Fatal_SpliceUnembedFail : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SpliceUnembedFail -> begin
true
end
| uu____3330 -> begin
false
end))


let uu___is_Warning_ExtractionUnexpectedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ExtractionUnexpectedEffect -> begin
true
end
| uu____3341 -> begin
false
end))


let uu___is_Error_DidNotFail : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_DidNotFail -> begin
true
end
| uu____3352 -> begin
false
end))


let uu___is_Warning_UnappliedFail : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnappliedFail -> begin
true
end
| uu____3363 -> begin
false
end))


let uu___is_Warning_QuantifierWithoutPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_QuantifierWithoutPattern -> begin
true
end
| uu____3374 -> begin
false
end))


let uu___is_Error_EmptyFailErrs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_EmptyFailErrs -> begin
true
end
| uu____3385 -> begin
false
end))


let uu___is_Warning_logicqualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_logicqualifier -> begin
true
end
| uu____3396 -> begin
false
end))


let uu___is_Fatal_CyclicDependence : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CyclicDependence -> begin
true
end
| uu____3407 -> begin
false
end))


let uu___is_Error_InductiveAnnotNotAType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InductiveAnnotNotAType -> begin
true
end
| uu____3418 -> begin
false
end))


let uu___is_Fatal_FriendInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FriendInterface -> begin
true
end
| uu____3429 -> begin
false
end))


let uu___is_Error_CannotRedefineConst : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_CannotRedefineConst -> begin
true
end
| uu____3440 -> begin
false
end))


let uu___is_Error_BadClassDecl : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadClassDecl -> begin
true
end
| uu____3451 -> begin
false
end))


let uu___is_Error_BadInductiveParam : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadInductiveParam -> begin
true
end
| uu____3462 -> begin
false
end))


let uu___is_Error_FieldShadow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_FieldShadow -> begin
true
end
| uu____3473 -> begin
false
end))


let uu___is_Error_UnexpectedDM4FType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedDM4FType -> begin
true
end
| uu____3484 -> begin
false
end))


let uu___is_Fatal_EffectAbbreviationResultTypeMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectAbbreviationResultTypeMismatch -> begin
true
end
| uu____3495 -> begin
false
end))


let uu___is_Error_AlreadyCachedAssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_AlreadyCachedAssertionFailure -> begin
true
end
| uu____3506 -> begin
false
end))


let uu___is_Error_MustEraseMissing : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_MustEraseMissing -> begin
true
end
| uu____3517 -> begin
false
end))


let uu___is_Warning_EffectfulArgumentToErasedFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_EffectfulArgumentToErasedFunction -> begin
true
end
| uu____3528 -> begin
false
end))


let uu___is_Fatal_EmptySurfaceLet : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EmptySurfaceLet -> begin
true
end
| uu____3539 -> begin
false
end))


let uu___is_Warning_UnexpectedCheckedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedCheckedFile -> begin
true
end
| uu____3550 -> begin
false
end))


let uu___is_Fatal_ExtractionUnsupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExtractionUnsupported -> begin
true
end
| uu____3561 -> begin
false
end))


type flag =
FStar_Options.error_flag


let default_flags : (raw_error * FStar_Options.error_flag) Prims.list = (((Error_DependencyAnalysisFailed), (FStar_Options.CAlwaysError)))::(((Error_IDETooManyPops), (FStar_Options.CAlwaysError)))::(((Error_IDEUnrecognized), (FStar_Options.CAlwaysError)))::(((Error_InductiveTypeNotSatisfyPositivityCondition), (FStar_Options.CAlwaysError)))::(((Error_InvalidUniverseVar), (FStar_Options.CAlwaysError)))::(((Error_MissingFileName), (FStar_Options.CAlwaysError)))::(((Error_ModuleFileNameMismatch), (FStar_Options.CAlwaysError)))::(((Error_OpPlusInUniverse), (FStar_Options.CAlwaysError)))::(((Error_OutOfRange), (FStar_Options.CAlwaysError)))::(((Error_ProofObligationFailed), (FStar_Options.CError)))::(((Error_TooManyFiles), (FStar_Options.CAlwaysError)))::(((Error_TypeCheckerFailToProve), (FStar_Options.CAlwaysError)))::(((Error_TypeError), (FStar_Options.CAlwaysError)))::(((Error_UncontrainedUnificationVar), (FStar_Options.CAlwaysError)))::(((Error_UnexpectedGTotComputation), (FStar_Options.CAlwaysError)))::(((Error_UnexpectedInstance), (FStar_Options.CAlwaysError)))::(((Error_UnknownFatal_AssertionFailure), (FStar_Options.CError)))::(((Error_Z3InvocationError), (FStar_Options.CAlwaysError)))::(((Error_IDEAssertionFailure), (FStar_Options.CAlwaysError)))::(((Error_Z3SolverError), (FStar_Options.CError)))::(((Fatal_AbstractTypeDeclarationInInterface), (FStar_Options.CFatal)))::(((Fatal_ActionMustHaveFunctionType), (FStar_Options.CFatal)))::(((Fatal_AlreadyDefinedTopLevelDeclaration), (FStar_Options.CFatal)))::(((Fatal_ArgumentLengthMismatch), (FStar_Options.CFatal)))::(((Fatal_AssertionFailure), (FStar_Options.CFatal)))::(((Fatal_AssignToImmutableValues), (FStar_Options.CFatal)))::(((Fatal_AssumeValInInterface), (FStar_Options.CFatal)))::(((Fatal_BadlyInstantiatedSynthByTactic), (FStar_Options.CFatal)))::(((Fatal_BadSignatureShape), (FStar_Options.CFatal)))::(((Fatal_BinderAndArgsLengthMismatch), (FStar_Options.CFatal)))::(((Fatal_BothValAndLetInInterface), (FStar_Options.CFatal)))::(((Fatal_CardinalityConstraintViolated), (FStar_Options.CFatal)))::(((Fatal_ComputationNotTotal), (FStar_Options.CFatal)))::(((Fatal_ComputationTypeNotAllowed), (FStar_Options.CFatal)))::(((Fatal_ComputedTypeNotMatchAnnotation), (FStar_Options.CFatal)))::(((Fatal_ConstructorArgLengthMismatch), (FStar_Options.CFatal)))::(((Fatal_ConstructorFailedCheck), (FStar_Options.CFatal)))::(((Fatal_ConstructorNotFound), (FStar_Options.CFatal)))::(((Fatal_ConstsructorBuildWrongType), (FStar_Options.CFatal)))::(((Fatal_CycleInRecTypeAbbreviation), (FStar_Options.CFatal)))::(((Fatal_DataContructorNotFound), (FStar_Options.CFatal)))::(((Fatal_DefaultQualifierNotAllowedOnEffects), (FStar_Options.CFatal)))::(((Fatal_DefinitionNotFound), (FStar_Options.CFatal)))::(((Fatal_DisjuctivePatternVarsMismatch), (FStar_Options.CFatal)))::(((Fatal_DivergentComputationCannotBeIncludedInTotal), (FStar_Options.CFatal)))::(((Fatal_DuplicateInImplementation), (FStar_Options.CFatal)))::(((Fatal_DuplicateModuleOrInterface), (FStar_Options.CFatal)))::(((Fatal_DuplicateTopLevelNames), (FStar_Options.CFatal)))::(((Fatal_DuplicateTypeAnnotationAndValDecl), (FStar_Options.CFatal)))::(((Fatal_EffectCannotBeReified), (FStar_Options.CFatal)))::(((Fatal_EffectConstructorNotFullyApplied), (FStar_Options.CFatal)))::(((Fatal_EffectfulAndPureComputationMismatch), (FStar_Options.CFatal)))::(((Fatal_EffectNotFound), (FStar_Options.CFatal)))::(((Fatal_EffectsCannotBeComposed), (FStar_Options.CFatal)))::(((Fatal_ErrorInSolveDeferredConstraints), (FStar_Options.CFatal)))::(((Fatal_ErrorsReported), (FStar_Options.CFatal)))::(((Fatal_EscapedBoundVar), (FStar_Options.CFatal)))::(((Fatal_ExpectedArrowAnnotatedType), (FStar_Options.CFatal)))::(((Fatal_ExpectedGhostExpression), (FStar_Options.CFatal)))::(((Fatal_ExpectedPureExpression), (FStar_Options.CFatal)))::(((Fatal_ExpectNormalizedEffect), (FStar_Options.CFatal)))::(((Fatal_ExpectTermGotFunction), (FStar_Options.CFatal)))::(((Fatal_ExpectTrivialPreCondition), (FStar_Options.CFatal)))::(((Fatal_FailToExtractNativeTactic), (FStar_Options.CFatal)))::(((Fatal_FailToCompileNativeTactic), (FStar_Options.CFatal)))::(((Fatal_FailToProcessPragma), (FStar_Options.CFatal)))::(((Fatal_FailToResolveImplicitArgument), (FStar_Options.CFatal)))::(((Fatal_FailToSolveUniverseInEquality), (FStar_Options.CFatal)))::(((Fatal_FieldsNotBelongToSameRecordType), (FStar_Options.CFatal)))::(((Fatal_ForbiddenReferenceToCurrentModule), (FStar_Options.CFatal)))::(((Fatal_FreeVariables), (FStar_Options.CFatal)))::(((Fatal_FunctionTypeExpected), (FStar_Options.CFatal)))::(((Fatal_IdentifierNotFound), (FStar_Options.CFatal)))::(((Fatal_IllAppliedConstant), (FStar_Options.CFatal)))::(((Fatal_IllegalCharInByteArray), (FStar_Options.CFatal)))::(((Fatal_IllegalCharInOperatorName), (FStar_Options.CFatal)))::(((Fatal_IllTyped), (FStar_Options.CFatal)))::(((Fatal_ImpossibleAbbrevLidBundle), (FStar_Options.CFatal)))::(((Fatal_ImpossibleAbbrevRenameBundle), (FStar_Options.CFatal)))::(((Fatal_ImpossibleInductiveWithAbbrev), (FStar_Options.CFatal)))::(((Fatal_ImpossiblePrePostAbs), (FStar_Options.CFatal)))::(((Fatal_ImpossiblePrePostArrow), (FStar_Options.CFatal)))::(((Fatal_ImpossibleToGenerateDMEffect), (FStar_Options.CFatal)))::(((Fatal_ImpossibleTypeAbbrevBundle), (FStar_Options.CFatal)))::(((Fatal_ImpossibleTypeAbbrevSigeltBundle), (FStar_Options.CFatal)))::(((Fatal_IncludeModuleNotPrepared), (FStar_Options.CFatal)))::(((Fatal_IncoherentInlineUniverse), (FStar_Options.CFatal)))::(((Fatal_IncompatibleKinds), (FStar_Options.CFatal)))::(((Fatal_IncompatibleNumberOfTypes), (FStar_Options.CFatal)))::(((Fatal_IncompatibleSetOfUniverse), (FStar_Options.CFatal)))::(((Fatal_IncompatibleUniverse), (FStar_Options.CFatal)))::(((Fatal_InconsistentImplicitArgumentAnnotation), (FStar_Options.CFatal)))::(((Fatal_InconsistentImplicitQualifier), (FStar_Options.CFatal)))::(((Fatal_InconsistentQualifierAnnotation), (FStar_Options.CFatal)))::(((Fatal_InferredTypeCauseVarEscape), (FStar_Options.CFatal)))::(((Fatal_InlineRenamedAsUnfold), (FStar_Options.CFatal)))::(((Fatal_InsufficientPatternArguments), (FStar_Options.CFatal)))::(((Fatal_InterfaceAlreadyProcessed), (FStar_Options.CFatal)))::(((Fatal_InterfaceNotImplementedByModule), (FStar_Options.CFatal)))::(((Fatal_InterfaceWithTypeImplementation), (FStar_Options.CFatal)))::(((Fatal_InvalidFloatingPointNumber), (FStar_Options.CFatal)))::(((Fatal_InvalidFSDocKeyword), (FStar_Options.CFatal)))::(((Fatal_InvalidIdentifier), (FStar_Options.CFatal)))::(((Fatal_InvalidLemmaArgument), (FStar_Options.CFatal)))::(((Fatal_InvalidNumericLiteral), (FStar_Options.CFatal)))::(((Fatal_InvalidRedefinitionOfLexT), (FStar_Options.CFatal)))::(((Fatal_InvalidUnicodeInStringLiteral), (FStar_Options.CFatal)))::(((Fatal_InvalidUTF8Encoding), (FStar_Options.CFatal)))::(((Fatal_InvalidWarnErrorSetting), (FStar_Options.CFatal)))::(((Fatal_LetBoundMonadicMismatch), (FStar_Options.CFatal)))::(((Fatal_LetMutableForVariablesOnly), (FStar_Options.CFatal)))::(((Fatal_LetOpenModuleOnly), (FStar_Options.CFatal)))::(((Fatal_LetRecArgumentMismatch), (FStar_Options.CFatal)))::(((Fatal_MalformedActionDeclaration), (FStar_Options.CFatal)))::(((Fatal_MismatchedPatternType), (FStar_Options.CFatal)))::(((Fatal_MismatchUniversePolymorphic), (FStar_Options.CFatal)))::(((Fatal_MissingDataConstructor), (FStar_Options.CFatal)))::(((Fatal_MissingExposeInterfacesOption), (FStar_Options.CFatal)))::(((Fatal_MissingFieldInRecord), (FStar_Options.CFatal)))::(((Fatal_MissingImplementation), (FStar_Options.CFatal)))::(((Fatal_MissingImplicitArguments), (FStar_Options.CFatal)))::(((Fatal_MissingInterface), (FStar_Options.CFatal)))::(((Fatal_MissingNameInBinder), (FStar_Options.CFatal)))::(((Fatal_MissingPrimsModule), (FStar_Options.CFatal)))::(((Fatal_MissingQuantifierBinder), (FStar_Options.CFatal)))::(((Fatal_ModuleExpected), (FStar_Options.CFatal)))::(((Fatal_ModuleFileNotFound), (FStar_Options.CFatal)))::(((Fatal_ModuleFirstStatement), (FStar_Options.CFatal)))::(((Fatal_ModuleNotFound), (FStar_Options.CFatal)))::(((Fatal_ModuleOrFileNotFound), (FStar_Options.CFatal)))::(((Fatal_MonadAlreadyDefined), (FStar_Options.CFatal)))::(((Fatal_MoreThanOneDeclaration), (FStar_Options.CFatal)))::(((Fatal_MultipleLetBinding), (FStar_Options.CFatal)))::(((Fatal_NameNotFound), (FStar_Options.CFatal)))::(((Fatal_NameSpaceNotFound), (FStar_Options.CFatal)))::(((Fatal_NegativeUniverseConstFatal_NotSupported), (FStar_Options.CFatal)))::(((Fatal_NoFileProvided), (FStar_Options.CFatal)))::(((Fatal_NonInductiveInMutuallyDefinedType), (FStar_Options.CFatal)))::(((Fatal_NonLinearPatternNotPermitted), (FStar_Options.CFatal)))::(((Fatal_NonLinearPatternVars), (FStar_Options.CFatal)))::(((Fatal_NonSingletonTopLevel), (FStar_Options.CFatal)))::(((Fatal_NonSingletonTopLevelModule), (FStar_Options.CFatal)))::(((Fatal_NonTopRecFunctionNotFullyEncoded), (FStar_Options.CFatal)))::(((Fatal_NonTrivialPreConditionInPrims), (FStar_Options.CFatal)))::(((Fatal_NonVariableInductiveTypeParameter), (FStar_Options.CFatal)))::(((Fatal_NotApplicationOrFv), (FStar_Options.CFatal)))::(((Fatal_NotEnoughArgsToEffect), (FStar_Options.CFatal)))::(((Fatal_NotEnoughArgumentsForEffect), (FStar_Options.CFatal)))::(((Fatal_NotFunctionType), (FStar_Options.CFatal)))::(((Fatal_NotSupported), (FStar_Options.CFatal)))::(((Fatal_NotTopLevelModule), (FStar_Options.CFatal)))::(((Fatal_NotValidFStarFile), (FStar_Options.CFatal)))::(((Fatal_NotValidIncludeDirectory), (FStar_Options.CFatal)))::(((Fatal_OneModulePerFile), (FStar_Options.CFatal)))::(((Fatal_OpenGoalsInSynthesis), (FStar_Options.CFatal)))::(((Fatal_OptionsNotCompatible), (FStar_Options.CFatal)))::(((Fatal_OutOfOrder), (FStar_Options.CFatal)))::(((Fatal_ParseErrors), (FStar_Options.CFatal)))::(((Fatal_ParseItError), (FStar_Options.CFatal)))::(((Fatal_PolyTypeExpected), (FStar_Options.CFatal)))::(((Fatal_PossibleInfiniteTyp), (FStar_Options.CFatal)))::(((Fatal_PreModuleMismatch), (FStar_Options.CFatal)))::(((Fatal_QulifierListNotPermitted), (FStar_Options.CFatal)))::(((Fatal_RecursiveFunctionLiteral), (FStar_Options.CFatal)))::(((Fatal_ReflectOnlySupportedOnEffects), (FStar_Options.CFatal)))::(((Fatal_ReservedPrefix), (FStar_Options.CFatal)))::(((Fatal_SMTOutputParseError), (FStar_Options.CFatal)))::(((Fatal_SMTSolverError), (FStar_Options.CFatal)))::(((Fatal_SyntaxError), (FStar_Options.CFatal)))::(((Fatal_SynthByTacticError), (FStar_Options.CFatal)))::(((Fatal_TacticGotStuck), (FStar_Options.CFatal)))::(((Fatal_TcOneFragmentFailed), (FStar_Options.CFatal)))::(((Fatal_TermOutsideOfDefLanguage), (FStar_Options.CFatal)))::(((Fatal_ToManyArgumentToFunction), (FStar_Options.CFatal)))::(((Fatal_TooManyOrTooFewFileMatch), (FStar_Options.CFatal)))::(((Fatal_TooManyPatternArguments), (FStar_Options.CFatal)))::(((Fatal_TooManyUniverse), (FStar_Options.CFatal)))::(((Fatal_TypeMismatch), (FStar_Options.CFatal)))::(((Fatal_TypeWithinPatternsAllowedOnVariablesOnly), (FStar_Options.CFatal)))::(((Fatal_UnableToReadFile), (FStar_Options.CFatal)))::(((Fatal_UnepxectedOrUnboundOperator), (FStar_Options.CFatal)))::(((Fatal_UnexpectedBinder), (FStar_Options.CFatal)))::(((Fatal_UnexpectedBindShape), (FStar_Options.CFatal)))::(((Fatal_UnexpectedChar), (FStar_Options.CFatal)))::(((Fatal_UnexpectedComputationTypeForLetRec), (FStar_Options.CFatal)))::(((Fatal_UnexpectedConstructorType), (FStar_Options.CFatal)))::(((Fatal_UnexpectedDataConstructor), (FStar_Options.CFatal)))::(((Fatal_UnexpectedEffect), (FStar_Options.CFatal)))::(((Fatal_UnexpectedEmptyRecord), (FStar_Options.CFatal)))::(((Fatal_UnexpectedExpressionType), (FStar_Options.CFatal)))::(((Fatal_UnexpectedFunctionParameterType), (FStar_Options.CFatal)))::(((Fatal_UnexpectedGeneralizedUniverse), (FStar_Options.CFatal)))::(((Fatal_UnexpectedGTotForLetRec), (FStar_Options.CFatal)))::(((Fatal_UnexpectedGuard), (FStar_Options.CFatal)))::(((Fatal_UnexpectedIdentifier), (FStar_Options.CFatal)))::(((Fatal_UnexpectedImplicitArgument), (FStar_Options.CFatal)))::(((Fatal_UnexpectedImplictArgument), (FStar_Options.CFatal)))::(((Fatal_UnexpectedInductivetype), (FStar_Options.CFatal)))::(((Fatal_UnexpectedLetBinding), (FStar_Options.CFatal)))::(((Fatal_UnexpectedModuleDeclaration), (FStar_Options.CFatal)))::(((Fatal_UnexpectedNumberOfUniverse), (FStar_Options.CFatal)))::(((Fatal_UnexpectedNumericLiteral), (FStar_Options.CFatal)))::(((Fatal_UnexpectedOperatorSymbol), (FStar_Options.CFatal)))::(((Fatal_UnexpectedPattern), (FStar_Options.CFatal)))::(((Fatal_UnexpectedPosition), (FStar_Options.CFatal)))::(((Fatal_UnExpectedPreCondition), (FStar_Options.CFatal)))::(((Fatal_UnexpectedReturnShape), (FStar_Options.CFatal)))::(((Fatal_UnexpectedSignatureForMonad), (FStar_Options.CFatal)))::(((Fatal_UnexpectedTerm), (FStar_Options.CFatal)))::(((Fatal_UnexpectedTermInUniverse), (FStar_Options.CFatal)))::(((Fatal_UnexpectedTermType), (FStar_Options.CFatal)))::(((Fatal_UnexpectedTermVQuote), (FStar_Options.CFatal)))::(((Fatal_UnexpectedUniversePolymorphicReturn), (FStar_Options.CFatal)))::(((Fatal_UnexpectedUniverseVariable), (FStar_Options.CFatal)))::(((Fatal_UnfoldableDeprecated), (FStar_Options.CFatal)))::(((Fatal_UnificationNotWellFormed), (FStar_Options.CFatal)))::(((Fatal_Uninstantiated), (FStar_Options.CFatal)))::(((Error_UninstantiatedUnificationVarInTactic), (FStar_Options.CError)))::(((Fatal_UninstantiatedVarInTactic), (FStar_Options.CFatal)))::(((Fatal_UniverseMightContainSumOfTwoUnivVars), (FStar_Options.CFatal)))::(((Fatal_UniversePolymorphicInnerLetBound), (FStar_Options.CFatal)))::(((Fatal_UnknownAttribute), (FStar_Options.CFatal)))::(((Fatal_UnknownToolForDep), (FStar_Options.CFatal)))::(((Fatal_UnrecognizedExtension), (FStar_Options.CFatal)))::(((Fatal_UnresolvedPatternVar), (FStar_Options.CFatal)))::(((Fatal_UnsupportedConstant), (FStar_Options.CFatal)))::(((Fatal_UnsupportedDisjuctivePatterns), (FStar_Options.CFatal)))::(((Fatal_UnsupportedQualifier), (FStar_Options.CFatal)))::(((Fatal_UserTacticFailure), (FStar_Options.CFatal)))::(((Fatal_ValueRestriction), (FStar_Options.CFatal)))::(((Fatal_VariableNotFound), (FStar_Options.CFatal)))::(((Fatal_WrongBodyTypeForReturnWP), (FStar_Options.CFatal)))::(((Fatal_WrongDataAppHeadFormat), (FStar_Options.CFatal)))::(((Fatal_WrongDefinitionOrder), (FStar_Options.CFatal)))::(((Fatal_WrongResultTypeAfterConstrutor), (FStar_Options.CFatal)))::(((Fatal_WrongTerm), (FStar_Options.CFatal)))::(((Fatal_WhenClauseNotSupported), (FStar_Options.CFatal)))::(((Unused01), (FStar_Options.CFatal)))::(((Warning_CallNotImplementedAsWarning), (FStar_Options.CWarning)))::(((Warning_AddImplicitAssumeNewQualifier), (FStar_Options.CWarning)))::(((Warning_AdmitWithoutDefinition), (FStar_Options.CWarning)))::(((Warning_CachedFile), (FStar_Options.CWarning)))::(((Warning_DefinitionNotTranslated), (FStar_Options.CWarning)))::(((Warning_DependencyFound), (FStar_Options.CWarning)))::(((Warning_DeprecatedEqualityOnBinder), (FStar_Options.CWarning)))::(((Warning_DeprecatedOpaqueQualifier), (FStar_Options.CWarning)))::(((Warning_DocOverwrite), (FStar_Options.CWarning)))::(((Warning_FileNotWritten), (FStar_Options.CWarning)))::(((Warning_Filtered), (FStar_Options.CWarning)))::(((Warning_FunctionLiteralPrecisionLoss), (FStar_Options.CWarning)))::(((Warning_FunctionNotExtacted), (FStar_Options.CWarning)))::(((Warning_HintFailedToReplayProof), (FStar_Options.CWarning)))::(((Warning_HitReplayFailed), (FStar_Options.CWarning)))::(((Warning_IDEIgnoreCodeGen), (FStar_Options.CWarning)))::(((Warning_IllFormedGoal), (FStar_Options.CWarning)))::(((Warning_InaccessibleArgument), (FStar_Options.CWarning)))::(((Warning_IncoherentImplicitQualifier), (FStar_Options.CWarning)))::(((Warning_IrrelevantQualifierOnArgumentToReflect), (FStar_Options.CWarning)))::(((Warning_IrrelevantQualifierOnArgumentToReify), (FStar_Options.CWarning)))::(((Warning_MalformedWarnErrorList), (FStar_Options.CWarning)))::(((Warning_MetaAlienNotATmUnknown), (FStar_Options.CWarning)))::(((Warning_MultipleAscriptions), (FStar_Options.CWarning)))::(((Warning_NondependentUserDefinedDataType), (FStar_Options.CWarning)))::(((Warning_NonListLiteralSMTPattern), (FStar_Options.CWarning)))::(((Warning_NormalizationFailure), (FStar_Options.CWarning)))::(((Warning_NotDependentArrow), (FStar_Options.CWarning)))::(((Warning_NotEmbedded), (FStar_Options.CWarning)))::(((Warning_PatternMissingBoundVar), (FStar_Options.CWarning)))::(((Warning_RecursiveDependency), (FStar_Options.CWarning)))::(((Warning_RedundantExplicitCurrying), (FStar_Options.CWarning)))::(((Warning_SMTPatTDeprecated), (FStar_Options.CWarning)))::(((Warning_SMTPatternIllFormed), (FStar_Options.CWarning)))::(((Warning_TopLevelEffect), (FStar_Options.CWarning)))::(((Warning_UnboundModuleReference), (FStar_Options.CWarning)))::(((Warning_UnexpectedFile), (FStar_Options.CWarning)))::(((Warning_UnexpectedFsTypApp), (FStar_Options.CWarning)))::(((Warning_UnexpectedZ3Output), (FStar_Options.CError)))::(((Warning_UnprotectedTerm), (FStar_Options.CWarning)))::(((Warning_UnrecognizedAttribute), (FStar_Options.CWarning)))::(((Warning_UpperBoundCandidateAlreadyVisited), (FStar_Options.CWarning)))::(((Warning_UseDefaultEffect), (FStar_Options.CWarning)))::(((Warning_WrongErrorLocation), (FStar_Options.CWarning)))::(((Warning_Z3InvocationWarning), (FStar_Options.CWarning)))::(((Warning_MissingInterfaceOrImplementation), (FStar_Options.CWarning)))::(((Warning_ConstructorBuildsUnexpectedType), (FStar_Options.CWarning)))::(((Warning_ModuleOrFileNotFoundWarning), (FStar_Options.CWarning)))::(((Error_NoLetMutable), (FStar_Options.CAlwaysError)))::(((Error_BadImplicit), (FStar_Options.CAlwaysError)))::(((Warning_DeprecatedDefinition), (FStar_Options.CWarning)))::(((Fatal_SMTEncodingArityMismatch), (FStar_Options.CFatal)))::(((Warning_Defensive), (FStar_Options.CWarning)))::(((Warning_CantInspect), (FStar_Options.CWarning)))::(((Warning_NilGivenExplicitArgs), (FStar_Options.CWarning)))::(((Warning_ConsAppliedExplicitArgs), (FStar_Options.CWarning)))::(((Warning_UnembedBinderKnot), (FStar_Options.CWarning)))::(((Fatal_TacticProofRelevantGoal), (FStar_Options.CFatal)))::(((Warning_TacAdmit), (FStar_Options.CWarning)))::(((Fatal_IncoherentPatterns), (FStar_Options.CFatal)))::(((Error_NoSMTButNeeded), (FStar_Options.CAlwaysError)))::(((Fatal_UnexpectedAntiquotation), (FStar_Options.CFatal)))::(((Fatal_SplicedUndef), (FStar_Options.CFatal)))::(((Fatal_SpliceUnembedFail), (FStar_Options.CFatal)))::(((Warning_ExtractionUnexpectedEffect), (FStar_Options.CWarning)))::(((Error_DidNotFail), (FStar_Options.CAlwaysError)))::(((Warning_UnappliedFail), (FStar_Options.CWarning)))::(((Warning_QuantifierWithoutPattern), (FStar_Options.CSilent)))::(((Error_EmptyFailErrs), (FStar_Options.CAlwaysError)))::(((Warning_logicqualifier), (FStar_Options.CWarning)))::(((Fatal_CyclicDependence), (FStar_Options.CFatal)))::(((Error_InductiveAnnotNotAType), (FStar_Options.CError)))::(((Fatal_FriendInterface), (FStar_Options.CFatal)))::(((Error_CannotRedefineConst), (FStar_Options.CError)))::(((Error_BadClassDecl), (FStar_Options.CError)))::(((Error_BadInductiveParam), (FStar_Options.CFatal)))::(((Error_FieldShadow), (FStar_Options.CFatal)))::(((Error_UnexpectedDM4FType), (FStar_Options.CFatal)))::(((Fatal_EffectAbbreviationResultTypeMismatch), (FStar_Options.CFatal)))::(((Error_AlreadyCachedAssertionFailure), (FStar_Options.CFatal)))::(((Error_MustEraseMissing), (FStar_Options.CWarning)))::(((Warning_EffectfulArgumentToErasedFunction), (FStar_Options.CWarning)))::(((Fatal_EmptySurfaceLet), (FStar_Options.CFatal)))::(((Warning_UnexpectedCheckedFile), (FStar_Options.CWarning)))::(((Fatal_ExtractionUnsupported), (FStar_Options.CFatal)))::[]

exception Err of ((raw_error * Prims.string))


let uu___is_Err : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (uu____4883) -> begin
true
end
| uu____4890 -> begin
false
end))


let __proj__Err__item__uu___ : Prims.exn  ->  (raw_error * Prims.string) = (fun projectee -> (match (projectee) with
| Err (uu____4908) -> begin
uu____4908
end))

exception Error of ((raw_error * Prims.string * FStar_Range.range))


let uu___is_Error : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error (uu____4933) -> begin
true
end
| uu____4942 -> begin
false
end))


let __proj__Error__item__uu___ : Prims.exn  ->  (raw_error * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (uu____4964) -> begin
uu____4964
end))

exception Warning of ((raw_error * Prims.string * FStar_Range.range))


let uu___is_Warning : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning (uu____4991) -> begin
true
end
| uu____5000 -> begin
false
end))


let __proj__Warning__item__uu___ : Prims.exn  ->  (raw_error * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (uu____5022) -> begin
uu____5022
end))

exception Stop


let uu___is_Stop : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stop -> begin
true
end
| uu____5039 -> begin
false
end))

exception Empty_frag


let uu___is_Empty_frag : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty_frag -> begin
true
end
| uu____5050 -> begin
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
| uu____5061 -> begin
false
end))


let uu___is_EInfo : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EInfo -> begin
true
end
| uu____5072 -> begin
false
end))


let uu___is_EWarning : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWarning -> begin
true
end
| uu____5083 -> begin
false
end))


let uu___is_EError : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EError -> begin
true
end
| uu____5094 -> begin
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

let uu____5389 = (match (issue.issue_range) with
| FStar_Pervasives_Native.None -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) when (Prims.op_Equality r FStar_Range.dummyRange) -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____5412 = (

let uu____5414 = (FStar_Range.string_of_use_range r)
in (FStar_Util.format1 "%s: " uu____5414))
in (

let uu____5417 = (

let uu____5419 = (

let uu____5421 = (FStar_Range.use_range r)
in (

let uu____5422 = (FStar_Range.def_range r)
in (Prims.op_Equality uu____5421 uu____5422)))
in (match (uu____5419) with
| true -> begin
""
end
| uu____5426 -> begin
(

let uu____5428 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 " (see also %s)" uu____5428))
end))
in ((uu____5412), (uu____5417))))
end)
in (match (uu____5389) with
| (range_str, see_also_str) -> begin
(

let issue_number = (match (issue.issue_number) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____5448 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 " %s" uu____5448))
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

let uu____5468 = (format_issue issue)
in (printer uu____5468))))


let compare_issues : issue  ->  issue  ->  Prims.int = (fun i1 i2 -> (match (((i1.issue_range), (i2.issue_range))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "0")
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____5492)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Pervasives_Native.Some (uu____5498), FStar_Pervasives_Native.None) -> begin
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

let uu____5531 = (

let uu____5534 = (FStar_ST.op_Bang errs)
in (e)::uu____5534)
in (FStar_ST.op_Colon_Equals errs uu____5531))
end
| uu____5583 -> begin
(print_issue e)
end))
in (

let count_errors = (fun uu____5589 -> (

let uu____5590 = (FStar_ST.op_Bang errs)
in (FStar_List.length uu____5590)))
in (

let report = (fun uu____5623 -> (

let sorted1 = (

let uu____5627 = (FStar_ST.op_Bang errs)
in (FStar_List.sortWith compare_issues uu____5627))
in ((match (print7) with
| true -> begin
(FStar_List.iter print_issue sorted1)
end
| uu____5655 -> begin
()
end);
sorted1;
)))
in (

let clear1 = (fun uu____5662 -> (FStar_ST.op_Colon_Equals errs []))
in {eh_add_one = add_one; eh_count_errors = count_errors; eh_report = report; eh_clear = clear1}))))))


let default_handler : error_handler = (mk_default_handler true)


let current_handler : error_handler FStar_ST.ref = (FStar_Util.mk_ref default_handler)


let mk_issue : issue_level  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  issue = (fun level range msg n1 -> {issue_message = msg; issue_level = level; issue_range = range; issue_number = n1})


let get_err_count : unit  ->  Prims.int = (fun uu____5730 -> (

let uu____5731 = (

let uu____5737 = (FStar_ST.op_Bang current_handler)
in uu____5737.eh_count_errors)
in (uu____5731 ())))


let wrapped_eh_add_one : error_handler  ->  issue  ->  unit = (fun h issue -> ((h.eh_add_one issue);
(match ((Prims.op_disEquality issue.issue_level EInfo)) with
| true -> begin
((

let uu____5771 = (

let uu____5773 = (FStar_ST.op_Bang FStar_Options.abort_counter)
in (uu____5773 - (Prims.parse_int "1")))
in (FStar_ST.op_Colon_Equals FStar_Options.abort_counter uu____5771));
(

let uu____5818 = (

let uu____5820 = (FStar_ST.op_Bang FStar_Options.abort_counter)
in (Prims.op_Equality uu____5820 (Prims.parse_int "0")))
in (match (uu____5818) with
| true -> begin
(failwith "Aborting due to --abort_on")
end
| uu____5847 -> begin
()
end));
)
end
| uu____5849 -> begin
()
end);
))


let add_one : issue  ->  unit = (fun issue -> (FStar_Util.atomically (fun uu____5859 -> (

let uu____5860 = (FStar_ST.op_Bang current_handler)
in (wrapped_eh_add_one uu____5860 issue)))))


let add_many : issue Prims.list  ->  unit = (fun issues -> (FStar_Util.atomically (fun uu____5892 -> (

let uu____5893 = (

let uu____5898 = (FStar_ST.op_Bang current_handler)
in (wrapped_eh_add_one uu____5898))
in (FStar_List.iter uu____5893 issues)))))


let report_all : unit  ->  issue Prims.list = (fun uu____5925 -> (

let uu____5926 = (

let uu____5933 = (FStar_ST.op_Bang current_handler)
in uu____5933.eh_report)
in (uu____5926 ())))


let clear : unit  ->  unit = (fun uu____5958 -> (

let uu____5959 = (

let uu____5964 = (FStar_ST.op_Bang current_handler)
in uu____5964.eh_clear)
in (uu____5959 ())))


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

let clear_prefix = (fun uu____6187 -> (FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None))
in (

let append_prefix = (fun s -> (

let uu____6223 = (FStar_ST.op_Bang pfx)
in (match (uu____6223) with
| FStar_Pervasives_Native.None -> begin
s
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____6257 = (FStar_String.op_Hat ": " s)
in (FStar_String.op_Hat p uu____6257))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let findIndex : 'Auu____6269 'Auu____6270 . ('Auu____6269 * 'Auu____6270) Prims.list  ->  'Auu____6269  ->  Prims.int = (fun l v1 -> (FStar_All.pipe_right l (FStar_List.index (fun uu___0_6308 -> (match (uu___0_6308) with
| (e, uu____6315) when (Prims.op_Equality e v1) -> begin
true
end
| uu____6317 -> begin
false
end)))))


let errno_of_error : raw_error  ->  Prims.int = (fun e -> (findIndex default_flags e))


let init_warn_error_flags : FStar_Options.error_flag Prims.list = (FStar_List.map FStar_Pervasives_Native.snd default_flags)


let diag : FStar_Range.range  ->  Prims.string  ->  unit = (fun r msg -> (

let uu____6350 = (FStar_Options.debug_any ())
in (match (uu____6350) with
| true -> begin
(add_one (mk_issue EInfo (FStar_Pervasives_Native.Some (r)) msg FStar_Pervasives_Native.None))
end
| uu____6354 -> begin
()
end)))


let defensive_errno : Prims.int = (errno_of_error Warning_Defensive)


let lookup : FStar_Options.error_flag Prims.list  ->  Prims.int  ->  FStar_Options.error_flag = (fun flags errno -> (

let uu____6375 = ((Prims.op_Equality errno defensive_errno) && (FStar_Options.defensive_fail ()))
in (match (uu____6375) with
| true -> begin
FStar_Options.CAlwaysError
end
| uu____6379 -> begin
(FStar_List.nth flags errno)
end)))


let log_issue : FStar_Range.range  ->  (raw_error * Prims.string)  ->  unit = (fun r uu____6396 -> (match (uu____6396) with
| (e, msg) -> begin
(

let errno = (errno_of_error e)
in (

let uu____6408 = (

let uu____6409 = (FStar_Options.error_flags ())
in (lookup uu____6409 errno))
in (match (uu____6408) with
| FStar_Options.CAlwaysError -> begin
(add_one (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno))))
end
| FStar_Options.CError -> begin
(add_one (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno))))
end
| FStar_Options.CWarning -> begin
(add_one (mk_issue EWarning (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno))))
end
| FStar_Options.CSilent -> begin
()
end
| FStar_Options.CFatal -> begin
(

let i = (mk_issue EError (FStar_Pervasives_Native.Some (r)) msg (FStar_Pervasives_Native.Some (errno)))
in (

let uu____6417 = (FStar_Options.ide ())
in (match (uu____6417) with
| true -> begin
(add_one i)
end
| uu____6420 -> begin
(

let uu____6422 = (

let uu____6424 = (format_issue i)
in (FStar_String.op_Hat "don\'t use log_issue to report fatal error, should use raise_error: " uu____6424))
in (failwith uu____6422))
end)))
end)))
end))


let add_errors : (raw_error * Prims.string * FStar_Range.range) Prims.list  ->  unit = (fun errs -> (FStar_Util.atomically (fun uu____6452 -> (FStar_List.iter (fun uu____6465 -> (match (uu____6465) with
| (e, msg, r) -> begin
(

let uu____6478 = (

let uu____6484 = (message_prefix.append_prefix msg)
in ((e), (uu____6484)))
in (log_issue r uu____6478))
end)) errs))))


let issue_of_exn : Prims.exn  ->  issue FStar_Pervasives_Native.option = (fun uu___1_6494 -> (match (uu___1_6494) with
| Error (e, msg, r) -> begin
(

let errno = (errno_of_error e)
in (

let uu____6504 = (

let uu____6505 = (message_prefix.append_prefix msg)
in (mk_issue EError (FStar_Pervasives_Native.Some (r)) uu____6505 (FStar_Pervasives_Native.Some (errno))))
in FStar_Pervasives_Native.Some (uu____6504)))
end
| FStar_Util.NYI (msg) -> begin
(

let uu____6510 = (

let uu____6511 = (message_prefix.append_prefix msg)
in (mk_issue ENotImplemented FStar_Pervasives_Native.None uu____6511 FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____6510))
end
| Err (e, msg) -> begin
(

let errno = (errno_of_error e)
in (

let uu____6520 = (

let uu____6521 = (message_prefix.append_prefix msg)
in (mk_issue EError FStar_Pervasives_Native.None uu____6521 (FStar_Pervasives_Native.Some (errno))))
in FStar_Pervasives_Native.Some (uu____6520)))
end
| uu____6524 -> begin
FStar_Pervasives_Native.None
end))


let err_exn : Prims.exn  ->  unit = (fun exn -> (match ((Prims.op_Equality exn Stop)) with
| true -> begin
()
end
| uu____6532 -> begin
(

let uu____6534 = (issue_of_exn exn)
in (match (uu____6534) with
| FStar_Pervasives_Native.Some (issue) -> begin
(add_one issue)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise exn)
end))
end))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___2_6544 -> (match (uu___2_6544) with
| Error (uu____6546) -> begin
true
end
| FStar_Util.NYI (uu____6555) -> begin
true
end
| Stop -> begin
true
end
| Err (uu____6559) -> begin
true
end
| uu____6566 -> begin
false
end))


let stop_if_err : unit  ->  unit = (fun uu____6573 -> (

let uu____6574 = (

let uu____6576 = (get_err_count ())
in (uu____6576 > (Prims.parse_int "0")))
in (match (uu____6574) with
| true -> begin
(FStar_Exn.raise Stop)
end
| uu____6580 -> begin
()
end)))


let raise_error : 'Auu____6589 . (raw_error * Prims.string)  ->  FStar_Range.range  ->  'Auu____6589 = (fun uu____6603 r -> (match (uu____6603) with
| (e, msg) -> begin
(FStar_Exn.raise (Error (((e), (msg), (r)))))
end))


let raise_err : 'Auu____6620 . (raw_error * Prims.string)  ->  'Auu____6620 = (fun uu____6630 -> (match (uu____6630) with
| (e, msg) -> begin
(FStar_Exn.raise (Err (((e), (msg)))))
end))


let update_flags : (FStar_Options.error_flag * Prims.string) Prims.list  ->  FStar_Options.error_flag Prims.list = (fun l -> (

let flags = init_warn_error_flags
in (

let compare1 = (fun uu____6698 uu____6699 -> (match (((uu____6698), (uu____6699))) with
| ((uu____6741, (a, uu____6743)), (uu____6744, (b, uu____6746))) -> begin
(match ((a > b)) with
| true -> begin
(Prims.parse_int "1")
end
| uu____6790 -> begin
(match ((a < b)) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____6795 -> begin
(Prims.parse_int "0")
end)
end)
end))
in (

let set_one_flag = (fun f d -> (match (((f), (d))) with
| (FStar_Options.CWarning, FStar_Options.CAlwaysError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot turn an error into warning")))
end
| (FStar_Options.CError, FStar_Options.CAlwaysError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot turn an error into warning")))
end
| (FStar_Options.CSilent, FStar_Options.CAlwaysError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot silence an error")))
end
| (uu____6815, FStar_Options.CFatal) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot reset the error level of a fatal error")))
end
| uu____6818 -> begin
f
end))
in (

let rec set_flag = (fun i l1 -> (

let d = (FStar_List.nth flags i)
in (match (l1) with
| [] -> begin
d
end
| ((f, (l2, h)))::tl1 -> begin
(match (((i >= l2) && (i <= h))) with
| true -> begin
(set_one_flag f d)
end
| uu____6908 -> begin
(match ((i < l2)) with
| true -> begin
d
end
| uu____6911 -> begin
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

let uu____6976 = (

let uu____6979 = (

let uu____6982 = (set_flag i sorted1)
in (uu____6982)::[])
in (FStar_List.append f uu____6979))
in (aux uu____6976 (i + (Prims.parse_int "1")) tl1 sorted1))
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

let uu____7084 = (match (r) with
| (r1)::(r2)::[] -> begin
(

let uu____7104 = (FStar_Util.int_of_string r1)
in (

let uu____7106 = (FStar_Util.int_of_string r2)
in ((uu____7104), (uu____7106))))
end
| uu____7110 -> begin
(

let uu____7114 = (

let uu____7120 = (FStar_Util.format1 "Malformed warn-error range %s" s)
in ((Fatal_InvalidWarnErrorSetting), (uu____7120)))
in (raise_err uu____7114))
end)
in (match (uu____7084) with
| (l2, h) -> begin
((match (((l2 < (Prims.parse_int "0")) || (h >= (FStar_List.length default_flags)))) with
| true -> begin
(

let uu____7155 = (

let uu____7161 = (

let uu____7163 = (FStar_Util.string_of_int l2)
in (

let uu____7165 = (FStar_Util.string_of_int h)
in (FStar_Util.format2 "No error for warn_error %s..%s" uu____7163 uu____7165)))
in ((Fatal_InvalidWarnErrorSetting), (uu____7161)))
in (raise_err uu____7155))
end
| uu____7169 -> begin
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
in (aux [] (Prims.parse_int "0") init_warn_error_flags sorted1))))))))))


let catch_errors : 'a . (unit  ->  'a)  ->  (issue Prims.list * 'a FStar_Pervasives_Native.option) = (fun f -> (

let newh = (mk_default_handler false)
in (

let old = (FStar_ST.op_Bang current_handler)
in ((FStar_ST.op_Colon_Equals current_handler newh);
(

let r = (FStar_All.try_with (fun uu___279_7329 -> (match (()) with
| () -> begin
(

let r = (f ())
in FStar_Pervasives_Native.Some (r))
end)) (fun uu___278_7335 -> ((err_exn uu___278_7335);
FStar_Pervasives_Native.None;
)))
in (

let errs = (newh.eh_report ())
in ((FStar_ST.op_Colon_Equals current_handler old);
((errs), (r));
)));
))))




