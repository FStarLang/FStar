
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


let uu___is_Error_DependencyAnalysisFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_DependencyAnalysisFailed -> begin
true
end
| uu____4 -> begin
false
end))


let uu___is_Error_IDETooManyPops : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDETooManyPops -> begin
true
end
| uu____8 -> begin
false
end))


let uu___is_Error_IDEUnrecognized : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDEUnrecognized -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_Error_InductiveTypeNotSatisfyPositivityCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InductiveTypeNotSatisfyPositivityCondition -> begin
true
end
| uu____16 -> begin
false
end))


let uu___is_Error_InvalidUniverseVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_InvalidUniverseVar -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_Error_MissingFileName : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_MissingFileName -> begin
true
end
| uu____24 -> begin
false
end))


let uu___is_Error_ModuleFileNameMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_ModuleFileNameMismatch -> begin
true
end
| uu____28 -> begin
false
end))


let uu___is_Error_OpPlusInUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_OpPlusInUniverse -> begin
true
end
| uu____32 -> begin
false
end))


let uu___is_Error_OutOfRange : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_OutOfRange -> begin
true
end
| uu____36 -> begin
false
end))


let uu___is_Error_ProofObligationFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_ProofObligationFailed -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Error_TooManyFiles : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TooManyFiles -> begin
true
end
| uu____44 -> begin
false
end))


let uu___is_Error_TypeCheckerFailToProve : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TypeCheckerFailToProve -> begin
true
end
| uu____48 -> begin
false
end))


let uu___is_Error_TypeError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_TypeError -> begin
true
end
| uu____52 -> begin
false
end))


let uu___is_Error_UncontrainedUnificationVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UncontrainedUnificationVar -> begin
true
end
| uu____56 -> begin
false
end))


let uu___is_Error_UnexpectedGTotComputation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedGTotComputation -> begin
true
end
| uu____60 -> begin
false
end))


let uu___is_Error_UnexpectedInstance : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnexpectedInstance -> begin
true
end
| uu____64 -> begin
false
end))


let uu___is_Error_UnknownFatal_AssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_UnknownFatal_AssertionFailure -> begin
true
end
| uu____68 -> begin
false
end))


let uu___is_Error_Z3InvocationError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_Z3InvocationError -> begin
true
end
| uu____72 -> begin
false
end))


let uu___is_Error_IDEAssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_IDEAssertionFailure -> begin
true
end
| uu____76 -> begin
false
end))


let uu___is_Error_Z3SolverError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_Z3SolverError -> begin
true
end
| uu____80 -> begin
false
end))


let uu___is_Fatal_AbstractTypeDeclarationInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AbstractTypeDeclarationInInterface -> begin
true
end
| uu____84 -> begin
false
end))


let uu___is_Fatal_ActionMustHaveFunctionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ActionMustHaveFunctionType -> begin
true
end
| uu____88 -> begin
false
end))


let uu___is_Fatal_AlreadyDefinedTopLevelDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AlreadyDefinedTopLevelDeclaration -> begin
true
end
| uu____92 -> begin
false
end))


let uu___is_Fatal_ArgumentLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ArgumentLengthMismatch -> begin
true
end
| uu____96 -> begin
false
end))


let uu___is_Fatal_AssertionFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssertionFailure -> begin
true
end
| uu____100 -> begin
false
end))


let uu___is_Fatal_AssignToImmutableValues : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssignToImmutableValues -> begin
true
end
| uu____104 -> begin
false
end))


let uu___is_Fatal_AssumeValInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_AssumeValInInterface -> begin
true
end
| uu____108 -> begin
false
end))


let uu___is_Fatal_BadlyInstantiatedSynthByTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BadlyInstantiatedSynthByTactic -> begin
true
end
| uu____112 -> begin
false
end))


let uu___is_Fatal_BadSignatureShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BadSignatureShape -> begin
true
end
| uu____116 -> begin
false
end))


let uu___is_Fatal_BinderAndArgsLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BinderAndArgsLengthMismatch -> begin
true
end
| uu____120 -> begin
false
end))


let uu___is_Fatal_BothValAndLetInInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_BothValAndLetInInterface -> begin
true
end
| uu____124 -> begin
false
end))


let uu___is_Fatal_CardinalityConstraintViolated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CardinalityConstraintViolated -> begin
true
end
| uu____128 -> begin
false
end))


let uu___is_Fatal_ComputationNotTotal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputationNotTotal -> begin
true
end
| uu____132 -> begin
false
end))


let uu___is_Fatal_ComputationTypeNotAllowed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputationTypeNotAllowed -> begin
true
end
| uu____136 -> begin
false
end))


let uu___is_Fatal_ComputedTypeNotMatchAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ComputedTypeNotMatchAnnotation -> begin
true
end
| uu____140 -> begin
false
end))


let uu___is_Fatal_ConstructorArgLengthMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorArgLengthMismatch -> begin
true
end
| uu____144 -> begin
false
end))


let uu___is_Fatal_ConstructorFailedCheck : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorFailedCheck -> begin
true
end
| uu____148 -> begin
false
end))


let uu___is_Fatal_ConstructorNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstructorNotFound -> begin
true
end
| uu____152 -> begin
false
end))


let uu___is_Fatal_ConstsructorBuildWrongType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ConstsructorBuildWrongType -> begin
true
end
| uu____156 -> begin
false
end))


let uu___is_Fatal_CycleInRecTypeAbbreviation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_CycleInRecTypeAbbreviation -> begin
true
end
| uu____160 -> begin
false
end))


let uu___is_Fatal_DataContructorNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DataContructorNotFound -> begin
true
end
| uu____164 -> begin
false
end))


let uu___is_Fatal_DefaultQualifierNotAllowedOnEffects : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DefaultQualifierNotAllowedOnEffects -> begin
true
end
| uu____168 -> begin
false
end))


let uu___is_Fatal_DefinitionNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DefinitionNotFound -> begin
true
end
| uu____172 -> begin
false
end))


let uu___is_Fatal_DisjuctivePatternVarsMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DisjuctivePatternVarsMismatch -> begin
true
end
| uu____176 -> begin
false
end))


let uu___is_Fatal_DivergentComputationCannotBeIncludedInTotal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DivergentComputationCannotBeIncludedInTotal -> begin
true
end
| uu____180 -> begin
false
end))


let uu___is_Fatal_DuplicateInImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateInImplementation -> begin
true
end
| uu____184 -> begin
false
end))


let uu___is_Fatal_DuplicateModuleOrInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateModuleOrInterface -> begin
true
end
| uu____188 -> begin
false
end))


let uu___is_Fatal_DuplicateTopLevelNames : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateTopLevelNames -> begin
true
end
| uu____192 -> begin
false
end))


let uu___is_Fatal_DuplicateTypeAnnotationAndValDecl : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_DuplicateTypeAnnotationAndValDecl -> begin
true
end
| uu____196 -> begin
false
end))


let uu___is_Fatal_EffectCannotBeReified : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectCannotBeReified -> begin
true
end
| uu____200 -> begin
false
end))


let uu___is_Fatal_EffectConstructorNotFullyApplied : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectConstructorNotFullyApplied -> begin
true
end
| uu____204 -> begin
false
end))


let uu___is_Fatal_EffectfulAndPureComputationMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectfulAndPureComputationMismatch -> begin
true
end
| uu____208 -> begin
false
end))


let uu___is_Fatal_EffectNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectNotFound -> begin
true
end
| uu____212 -> begin
false
end))


let uu___is_Fatal_EffectsCannotBeComposed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EffectsCannotBeComposed -> begin
true
end
| uu____216 -> begin
false
end))


let uu___is_Fatal_ErrorInSolveDeferredConstraints : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ErrorInSolveDeferredConstraints -> begin
true
end
| uu____220 -> begin
false
end))


let uu___is_Fatal_ErrorsReported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ErrorsReported -> begin
true
end
| uu____224 -> begin
false
end))


let uu___is_Fatal_EscapedBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_EscapedBoundVar -> begin
true
end
| uu____228 -> begin
false
end))


let uu___is_Fatal_ExpectedArrowAnnotatedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedArrowAnnotatedType -> begin
true
end
| uu____232 -> begin
false
end))


let uu___is_Fatal_ExpectedGhostExpression : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedGhostExpression -> begin
true
end
| uu____236 -> begin
false
end))


let uu___is_Fatal_ExpectedPureExpression : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectedPureExpression -> begin
true
end
| uu____240 -> begin
false
end))


let uu___is_Fatal_ExpectNormalizedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectNormalizedEffect -> begin
true
end
| uu____244 -> begin
false
end))


let uu___is_Fatal_ExpectTermGotFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectTermGotFunction -> begin
true
end
| uu____248 -> begin
false
end))


let uu___is_Fatal_ExpectTrivialPreCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ExpectTrivialPreCondition -> begin
true
end
| uu____252 -> begin
false
end))


let uu___is_Fatal_FailToCompileNativeTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToCompileNativeTactic -> begin
true
end
| uu____256 -> begin
false
end))


let uu___is_Fatal_FailToExtractNativeTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToExtractNativeTactic -> begin
true
end
| uu____260 -> begin
false
end))


let uu___is_Fatal_FailToProcessPragma : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToProcessPragma -> begin
true
end
| uu____264 -> begin
false
end))


let uu___is_Fatal_FailToResolveImplicitArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToResolveImplicitArgument -> begin
true
end
| uu____268 -> begin
false
end))


let uu___is_Fatal_FailToSolveUniverseInEquality : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FailToSolveUniverseInEquality -> begin
true
end
| uu____272 -> begin
false
end))


let uu___is_Fatal_FieldsNotBelongToSameRecordType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FieldsNotBelongToSameRecordType -> begin
true
end
| uu____276 -> begin
false
end))


let uu___is_Fatal_ForbiddenReferenceToCurrentModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ForbiddenReferenceToCurrentModule -> begin
true
end
| uu____280 -> begin
false
end))


let uu___is_Fatal_FreeVariables : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FreeVariables -> begin
true
end
| uu____284 -> begin
false
end))


let uu___is_Fatal_FunctionTypeExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_FunctionTypeExpected -> begin
true
end
| uu____288 -> begin
false
end))


let uu___is_Fatal_IdentifierNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IdentifierNotFound -> begin
true
end
| uu____292 -> begin
false
end))


let uu___is_Fatal_IllAppliedConstant : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllAppliedConstant -> begin
true
end
| uu____296 -> begin
false
end))


let uu___is_Fatal_IllegalCharInByteArray : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllegalCharInByteArray -> begin
true
end
| uu____300 -> begin
false
end))


let uu___is_Fatal_IllegalCharInOperatorName : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllegalCharInOperatorName -> begin
true
end
| uu____304 -> begin
false
end))


let uu___is_Fatal_IllTyped : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IllTyped -> begin
true
end
| uu____308 -> begin
false
end))


let uu___is_Fatal_ImpossibleAbbrevLidBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleAbbrevLidBundle -> begin
true
end
| uu____312 -> begin
false
end))


let uu___is_Fatal_ImpossibleAbbrevRenameBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleAbbrevRenameBundle -> begin
true
end
| uu____316 -> begin
false
end))


let uu___is_Fatal_ImpossibleInductiveWithAbbrev : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleInductiveWithAbbrev -> begin
true
end
| uu____320 -> begin
false
end))


let uu___is_Fatal_ImpossiblePrePostAbs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossiblePrePostAbs -> begin
true
end
| uu____324 -> begin
false
end))


let uu___is_Fatal_ImpossiblePrePostArrow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossiblePrePostArrow -> begin
true
end
| uu____328 -> begin
false
end))


let uu___is_Fatal_ImpossibleToGenerateDMEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleToGenerateDMEffect -> begin
true
end
| uu____332 -> begin
false
end))


let uu___is_Fatal_ImpossibleTypeAbbrevBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleTypeAbbrevBundle -> begin
true
end
| uu____336 -> begin
false
end))


let uu___is_Fatal_ImpossibleTypeAbbrevSigeltBundle : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ImpossibleTypeAbbrevSigeltBundle -> begin
true
end
| uu____340 -> begin
false
end))


let uu___is_Fatal_IncludeModuleNotPrepared : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncludeModuleNotPrepared -> begin
true
end
| uu____344 -> begin
false
end))


let uu___is_Fatal_IncoherentInlineUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncoherentInlineUniverse -> begin
true
end
| uu____348 -> begin
false
end))


let uu___is_Fatal_IncompatibleKinds : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleKinds -> begin
true
end
| uu____352 -> begin
false
end))


let uu___is_Fatal_IncompatibleNumberOfTypes : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleNumberOfTypes -> begin
true
end
| uu____356 -> begin
false
end))


let uu___is_Fatal_IncompatibleSetOfUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleSetOfUniverse -> begin
true
end
| uu____360 -> begin
false
end))


let uu___is_Fatal_IncompatibleUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncompatibleUniverse -> begin
true
end
| uu____364 -> begin
false
end))


let uu___is_Fatal_InconsistentImplicitArgumentAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentImplicitArgumentAnnotation -> begin
true
end
| uu____368 -> begin
false
end))


let uu___is_Fatal_InconsistentImplicitQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentImplicitQualifier -> begin
true
end
| uu____372 -> begin
false
end))


let uu___is_Fatal_InconsistentQualifierAnnotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InconsistentQualifierAnnotation -> begin
true
end
| uu____376 -> begin
false
end))


let uu___is_Fatal_InferredTypeCauseVarEscape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InferredTypeCauseVarEscape -> begin
true
end
| uu____380 -> begin
false
end))


let uu___is_Fatal_InlineRenamedAsUnfold : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InlineRenamedAsUnfold -> begin
true
end
| uu____384 -> begin
false
end))


let uu___is_Fatal_InsufficientPatternArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InsufficientPatternArguments -> begin
true
end
| uu____388 -> begin
false
end))


let uu___is_Fatal_InterfaceAlreadyProcessed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceAlreadyProcessed -> begin
true
end
| uu____392 -> begin
false
end))


let uu___is_Fatal_InterfaceNotImplementedByModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceNotImplementedByModule -> begin
true
end
| uu____396 -> begin
false
end))


let uu___is_Fatal_InterfaceWithTypeImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InterfaceWithTypeImplementation -> begin
true
end
| uu____400 -> begin
false
end))


let uu___is_Fatal_InvalidFloatingPointNumber : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidFloatingPointNumber -> begin
true
end
| uu____404 -> begin
false
end))


let uu___is_Fatal_InvalidFSDocKeyword : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidFSDocKeyword -> begin
true
end
| uu____408 -> begin
false
end))


let uu___is_Fatal_InvalidIdentifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidIdentifier -> begin
true
end
| uu____412 -> begin
false
end))


let uu___is_Fatal_InvalidLemmaArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidLemmaArgument -> begin
true
end
| uu____416 -> begin
false
end))


let uu___is_Fatal_InvalidNumericLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidNumericLiteral -> begin
true
end
| uu____420 -> begin
false
end))


let uu___is_Fatal_InvalidRedefinitionOfLexT : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidRedefinitionOfLexT -> begin
true
end
| uu____424 -> begin
false
end))


let uu___is_Fatal_InvalidUnicodeInStringLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidUnicodeInStringLiteral -> begin
true
end
| uu____428 -> begin
false
end))


let uu___is_Fatal_InvalidUTF8Encoding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidUTF8Encoding -> begin
true
end
| uu____432 -> begin
false
end))


let uu___is_Fatal_InvalidWarnErrorSetting : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_InvalidWarnErrorSetting -> begin
true
end
| uu____436 -> begin
false
end))


let uu___is_Fatal_LetBoundMonadicMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetBoundMonadicMismatch -> begin
true
end
| uu____440 -> begin
false
end))


let uu___is_Fatal_LetMutableForVariablesOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetMutableForVariablesOnly -> begin
true
end
| uu____444 -> begin
false
end))


let uu___is_Fatal_LetOpenModuleOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetOpenModuleOnly -> begin
true
end
| uu____448 -> begin
false
end))


let uu___is_Fatal_LetRecArgumentMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_LetRecArgumentMismatch -> begin
true
end
| uu____452 -> begin
false
end))


let uu___is_Fatal_MalformedActionDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MalformedActionDeclaration -> begin
true
end
| uu____456 -> begin
false
end))


let uu___is_Fatal_MismatchedPatternType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MismatchedPatternType -> begin
true
end
| uu____460 -> begin
false
end))


let uu___is_Fatal_MismatchUniversePolymorphic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MismatchUniversePolymorphic -> begin
true
end
| uu____464 -> begin
false
end))


let uu___is_Fatal_MissingDataConstructor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingDataConstructor -> begin
true
end
| uu____468 -> begin
false
end))


let uu___is_Fatal_MissingExposeInterfacesOption : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingExposeInterfacesOption -> begin
true
end
| uu____472 -> begin
false
end))


let uu___is_Fatal_MissingFieldInRecord : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingFieldInRecord -> begin
true
end
| uu____476 -> begin
false
end))


let uu___is_Fatal_MissingImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingImplementation -> begin
true
end
| uu____480 -> begin
false
end))


let uu___is_Fatal_MissingImplicitArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingImplicitArguments -> begin
true
end
| uu____484 -> begin
false
end))


let uu___is_Fatal_MissingInterface : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingInterface -> begin
true
end
| uu____488 -> begin
false
end))


let uu___is_Fatal_MissingNameInBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingNameInBinder -> begin
true
end
| uu____492 -> begin
false
end))


let uu___is_Fatal_MissingPrimsModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingPrimsModule -> begin
true
end
| uu____496 -> begin
false
end))


let uu___is_Fatal_MissingQuantifierBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MissingQuantifierBinder -> begin
true
end
| uu____500 -> begin
false
end))


let uu___is_Fatal_ModuleExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleExpected -> begin
true
end
| uu____504 -> begin
false
end))


let uu___is_Fatal_ModuleFileNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleFileNotFound -> begin
true
end
| uu____508 -> begin
false
end))


let uu___is_Fatal_ModuleFirstStatement : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleFirstStatement -> begin
true
end
| uu____512 -> begin
false
end))


let uu___is_Fatal_ModuleNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleNotFound -> begin
true
end
| uu____516 -> begin
false
end))


let uu___is_Fatal_ModuleOrFileNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ModuleOrFileNotFound -> begin
true
end
| uu____520 -> begin
false
end))


let uu___is_Fatal_MonadAlreadyDefined : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MonadAlreadyDefined -> begin
true
end
| uu____524 -> begin
false
end))


let uu___is_Fatal_MoreThanOneDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MoreThanOneDeclaration -> begin
true
end
| uu____528 -> begin
false
end))


let uu___is_Fatal_MultipleLetBinding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_MultipleLetBinding -> begin
true
end
| uu____532 -> begin
false
end))


let uu___is_Fatal_NameNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NameNotFound -> begin
true
end
| uu____536 -> begin
false
end))


let uu___is_Fatal_NameSpaceNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NameSpaceNotFound -> begin
true
end
| uu____540 -> begin
false
end))


let uu___is_Fatal_NegativeUniverseConstFatal_NotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NegativeUniverseConstFatal_NotSupported -> begin
true
end
| uu____544 -> begin
false
end))


let uu___is_Fatal_NoFileProvided : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NoFileProvided -> begin
true
end
| uu____548 -> begin
false
end))


let uu___is_Fatal_NonInductiveInMutuallyDefinedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonInductiveInMutuallyDefinedType -> begin
true
end
| uu____552 -> begin
false
end))


let uu___is_Fatal_NonLinearPatternNotPermitted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonLinearPatternNotPermitted -> begin
true
end
| uu____556 -> begin
false
end))


let uu___is_Fatal_NonLinearPatternVars : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonLinearPatternVars -> begin
true
end
| uu____560 -> begin
false
end))


let uu___is_Fatal_NonSingletonTopLevel : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonSingletonTopLevel -> begin
true
end
| uu____564 -> begin
false
end))


let uu___is_Fatal_NonSingletonTopLevelModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonSingletonTopLevelModule -> begin
true
end
| uu____568 -> begin
false
end))


let uu___is_Fatal_NonTopRecFunctionNotFullyEncoded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonTopRecFunctionNotFullyEncoded -> begin
true
end
| uu____572 -> begin
false
end))


let uu___is_Fatal_NonTrivialPreConditionInPrims : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonTrivialPreConditionInPrims -> begin
true
end
| uu____576 -> begin
false
end))


let uu___is_Fatal_NonVariableInductiveTypeParameter : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NonVariableInductiveTypeParameter -> begin
true
end
| uu____580 -> begin
false
end))


let uu___is_Fatal_NotApplicationOrFv : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotApplicationOrFv -> begin
true
end
| uu____584 -> begin
false
end))


let uu___is_Fatal_NotEnoughArgsToEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotEnoughArgsToEffect -> begin
true
end
| uu____588 -> begin
false
end))


let uu___is_Fatal_NotEnoughArgumentsForEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotEnoughArgumentsForEffect -> begin
true
end
| uu____592 -> begin
false
end))


let uu___is_Fatal_NotFunctionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotFunctionType -> begin
true
end
| uu____596 -> begin
false
end))


let uu___is_Fatal_NotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotSupported -> begin
true
end
| uu____600 -> begin
false
end))


let uu___is_Fatal_NotTopLevelModule : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotTopLevelModule -> begin
true
end
| uu____604 -> begin
false
end))


let uu___is_Fatal_NotValidFStarFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotValidFStarFile -> begin
true
end
| uu____608 -> begin
false
end))


let uu___is_Fatal_NotValidIncludeDirectory : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_NotValidIncludeDirectory -> begin
true
end
| uu____612 -> begin
false
end))


let uu___is_Fatal_OneModulePerFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OneModulePerFile -> begin
true
end
| uu____616 -> begin
false
end))


let uu___is_Fatal_OpenGoalsInSynthesis : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OpenGoalsInSynthesis -> begin
true
end
| uu____620 -> begin
false
end))


let uu___is_Fatal_OptionsNotCompatible : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OptionsNotCompatible -> begin
true
end
| uu____624 -> begin
false
end))


let uu___is_Fatal_OutOfOrder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_OutOfOrder -> begin
true
end
| uu____628 -> begin
false
end))


let uu___is_Fatal_ParseErrors : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ParseErrors -> begin
true
end
| uu____632 -> begin
false
end))


let uu___is_Fatal_ParseItError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ParseItError -> begin
true
end
| uu____636 -> begin
false
end))


let uu___is_Fatal_PolyTypeExpected : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PolyTypeExpected -> begin
true
end
| uu____640 -> begin
false
end))


let uu___is_Fatal_PossibleInfiniteTyp : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PossibleInfiniteTyp -> begin
true
end
| uu____644 -> begin
false
end))


let uu___is_Fatal_PreModuleMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_PreModuleMismatch -> begin
true
end
| uu____648 -> begin
false
end))


let uu___is_Fatal_QulifierListNotPermitted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_QulifierListNotPermitted -> begin
true
end
| uu____652 -> begin
false
end))


let uu___is_Fatal_RecursiveFunctionLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_RecursiveFunctionLiteral -> begin
true
end
| uu____656 -> begin
false
end))


let uu___is_Fatal_ReflectOnlySupportedOnEffects : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ReflectOnlySupportedOnEffects -> begin
true
end
| uu____660 -> begin
false
end))


let uu___is_Fatal_ReservedPrefix : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ReservedPrefix -> begin
true
end
| uu____664 -> begin
false
end))


let uu___is_Fatal_SMTOutputParseError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTOutputParseError -> begin
true
end
| uu____668 -> begin
false
end))


let uu___is_Fatal_SMTSolverError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTSolverError -> begin
true
end
| uu____672 -> begin
false
end))


let uu___is_Fatal_SyntaxError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SyntaxError -> begin
true
end
| uu____676 -> begin
false
end))


let uu___is_Fatal_SynthByTacticError : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SynthByTacticError -> begin
true
end
| uu____680 -> begin
false
end))


let uu___is_Fatal_TacticGotStuck : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TacticGotStuck -> begin
true
end
| uu____684 -> begin
false
end))


let uu___is_Fatal_TcOneFragmentFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TcOneFragmentFailed -> begin
true
end
| uu____688 -> begin
false
end))


let uu___is_Fatal_TermOutsideOfDefLanguage : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TermOutsideOfDefLanguage -> begin
true
end
| uu____692 -> begin
false
end))


let uu___is_Fatal_ToManyArgumentToFunction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ToManyArgumentToFunction -> begin
true
end
| uu____696 -> begin
false
end))


let uu___is_Fatal_TooManyOrTooFewFileMatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyOrTooFewFileMatch -> begin
true
end
| uu____700 -> begin
false
end))


let uu___is_Fatal_TooManyPatternArguments : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyPatternArguments -> begin
true
end
| uu____704 -> begin
false
end))


let uu___is_Fatal_TooManyUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TooManyUniverse -> begin
true
end
| uu____708 -> begin
false
end))


let uu___is_Fatal_TypeMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TypeMismatch -> begin
true
end
| uu____712 -> begin
false
end))


let uu___is_Fatal_TypeWithinPatternsAllowedOnVariablesOnly : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TypeWithinPatternsAllowedOnVariablesOnly -> begin
true
end
| uu____716 -> begin
false
end))


let uu___is_Fatal_UnableToReadFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnableToReadFile -> begin
true
end
| uu____720 -> begin
false
end))


let uu___is_Fatal_UnepxectedOrUnboundOperator : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnepxectedOrUnboundOperator -> begin
true
end
| uu____724 -> begin
false
end))


let uu___is_Fatal_UnexpectedBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedBinder -> begin
true
end
| uu____728 -> begin
false
end))


let uu___is_Fatal_UnexpectedBindShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedBindShape -> begin
true
end
| uu____732 -> begin
false
end))


let uu___is_Fatal_UnexpectedChar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedChar -> begin
true
end
| uu____736 -> begin
false
end))


let uu___is_Fatal_UnexpectedComputationTypeForLetRec : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedComputationTypeForLetRec -> begin
true
end
| uu____740 -> begin
false
end))


let uu___is_Fatal_UnexpectedConstructorType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedConstructorType -> begin
true
end
| uu____744 -> begin
false
end))


let uu___is_Fatal_UnexpectedDataConstructor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedDataConstructor -> begin
true
end
| uu____748 -> begin
false
end))


let uu___is_Fatal_UnexpectedEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedEffect -> begin
true
end
| uu____752 -> begin
false
end))


let uu___is_Fatal_UnexpectedEmptyRecord : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedEmptyRecord -> begin
true
end
| uu____756 -> begin
false
end))


let uu___is_Fatal_UnexpectedExpressionType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedExpressionType -> begin
true
end
| uu____760 -> begin
false
end))


let uu___is_Fatal_UnexpectedFunctionParameterType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedFunctionParameterType -> begin
true
end
| uu____764 -> begin
false
end))


let uu___is_Fatal_UnexpectedGeneralizedUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGeneralizedUniverse -> begin
true
end
| uu____768 -> begin
false
end))


let uu___is_Fatal_UnexpectedGTotForLetRec : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGTotForLetRec -> begin
true
end
| uu____772 -> begin
false
end))


let uu___is_Fatal_UnexpectedGuard : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedGuard -> begin
true
end
| uu____776 -> begin
false
end))


let uu___is_Fatal_UnexpectedIdentifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedIdentifier -> begin
true
end
| uu____780 -> begin
false
end))


let uu___is_Fatal_UnexpectedImplicitArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedImplicitArgument -> begin
true
end
| uu____784 -> begin
false
end))


let uu___is_Fatal_UnexpectedImplictArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedImplictArgument -> begin
true
end
| uu____788 -> begin
false
end))


let uu___is_Fatal_UnexpectedInductivetype : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedInductivetype -> begin
true
end
| uu____792 -> begin
false
end))


let uu___is_Fatal_UnexpectedLetBinding : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedLetBinding -> begin
true
end
| uu____796 -> begin
false
end))


let uu___is_Fatal_UnexpectedModuleDeclaration : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedModuleDeclaration -> begin
true
end
| uu____800 -> begin
false
end))


let uu___is_Fatal_UnexpectedNumberOfUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedNumberOfUniverse -> begin
true
end
| uu____804 -> begin
false
end))


let uu___is_Fatal_UnexpectedNumericLiteral : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedNumericLiteral -> begin
true
end
| uu____808 -> begin
false
end))


let uu___is_Fatal_UnexpectedOperatorSymbol : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedOperatorSymbol -> begin
true
end
| uu____812 -> begin
false
end))


let uu___is_Fatal_UnexpectedPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedPattern -> begin
true
end
| uu____816 -> begin
false
end))


let uu___is_Fatal_UnexpectedPosition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedPosition -> begin
true
end
| uu____820 -> begin
false
end))


let uu___is_Fatal_UnExpectedPreCondition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnExpectedPreCondition -> begin
true
end
| uu____824 -> begin
false
end))


let uu___is_Fatal_UnexpectedReturnShape : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedReturnShape -> begin
true
end
| uu____828 -> begin
false
end))


let uu___is_Fatal_UnexpectedSignatureForMonad : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedSignatureForMonad -> begin
true
end
| uu____832 -> begin
false
end))


let uu___is_Fatal_UnexpectedTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTerm -> begin
true
end
| uu____836 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermInUniverse : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermInUniverse -> begin
true
end
| uu____840 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermType -> begin
true
end
| uu____844 -> begin
false
end))


let uu___is_Fatal_UnexpectedTermVQuote : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedTermVQuote -> begin
true
end
| uu____848 -> begin
false
end))


let uu___is_Fatal_UnexpectedUniversePolymorphicReturn : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedUniversePolymorphicReturn -> begin
true
end
| uu____852 -> begin
false
end))


let uu___is_Fatal_UnexpectedUniverseVariable : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedUniverseVariable -> begin
true
end
| uu____856 -> begin
false
end))


let uu___is_Fatal_UnfoldableDeprecated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnfoldableDeprecated -> begin
true
end
| uu____860 -> begin
false
end))


let uu___is_Fatal_UnificationNotWellFormed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnificationNotWellFormed -> begin
true
end
| uu____864 -> begin
false
end))


let uu___is_Fatal_Uninstantiated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_Uninstantiated -> begin
true
end
| uu____868 -> begin
false
end))


let uu___is_Fatal_UninstantiatedUnificationVarInTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UninstantiatedUnificationVarInTactic -> begin
true
end
| uu____872 -> begin
false
end))


let uu___is_Fatal_UninstantiatedVarInTactic : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UninstantiatedVarInTactic -> begin
true
end
| uu____876 -> begin
false
end))


let uu___is_Fatal_UniverseMightContainSumOfTwoUnivVars : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UniverseMightContainSumOfTwoUnivVars -> begin
true
end
| uu____880 -> begin
false
end))


let uu___is_Fatal_UniversePolymorphicInnerLetBound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UniversePolymorphicInnerLetBound -> begin
true
end
| uu____884 -> begin
false
end))


let uu___is_Fatal_UnknownAttribute : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnknownAttribute -> begin
true
end
| uu____888 -> begin
false
end))


let uu___is_Fatal_UnknownToolForDep : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnknownToolForDep -> begin
true
end
| uu____892 -> begin
false
end))


let uu___is_Fatal_UnrecognizedExtension : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnrecognizedExtension -> begin
true
end
| uu____896 -> begin
false
end))


let uu___is_Fatal_UnresolvedPatternVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnresolvedPatternVar -> begin
true
end
| uu____900 -> begin
false
end))


let uu___is_Fatal_UnsupportedConstant : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedConstant -> begin
true
end
| uu____904 -> begin
false
end))


let uu___is_Fatal_UnsupportedDisjuctivePatterns : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedDisjuctivePatterns -> begin
true
end
| uu____908 -> begin
false
end))


let uu___is_Fatal_UnsupportedQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnsupportedQualifier -> begin
true
end
| uu____912 -> begin
false
end))


let uu___is_Fatal_UserTacticFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UserTacticFailure -> begin
true
end
| uu____916 -> begin
false
end))


let uu___is_Fatal_ValueRestriction : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_ValueRestriction -> begin
true
end
| uu____920 -> begin
false
end))


let uu___is_Fatal_VariableNotFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_VariableNotFound -> begin
true
end
| uu____924 -> begin
false
end))


let uu___is_Fatal_WrongBodyTypeForReturnWP : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongBodyTypeForReturnWP -> begin
true
end
| uu____928 -> begin
false
end))


let uu___is_Fatal_WrongDataAppHeadFormat : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongDataAppHeadFormat -> begin
true
end
| uu____932 -> begin
false
end))


let uu___is_Fatal_WrongDefinitionOrder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongDefinitionOrder -> begin
true
end
| uu____936 -> begin
false
end))


let uu___is_Fatal_WrongResultTypeAfterConstrutor : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongResultTypeAfterConstrutor -> begin
true
end
| uu____940 -> begin
false
end))


let uu___is_Fatal_WrongTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WrongTerm -> begin
true
end
| uu____944 -> begin
false
end))


let uu___is_Fatal_WhenClauseNotSupported : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_WhenClauseNotSupported -> begin
true
end
| uu____948 -> begin
false
end))


let uu___is_Unused01 : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unused01 -> begin
true
end
| uu____952 -> begin
false
end))


let uu___is_Warning_AddImplicitAssumeNewQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_AddImplicitAssumeNewQualifier -> begin
true
end
| uu____956 -> begin
false
end))


let uu___is_Warning_AdmitWithoutDefinition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_AdmitWithoutDefinition -> begin
true
end
| uu____960 -> begin
false
end))


let uu___is_Warning_CachedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CachedFile -> begin
true
end
| uu____964 -> begin
false
end))


let uu___is_Warning_DefinitionNotTranslated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DefinitionNotTranslated -> begin
true
end
| uu____968 -> begin
false
end))


let uu___is_Warning_DependencyFound : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DependencyFound -> begin
true
end
| uu____972 -> begin
false
end))


let uu___is_Warning_DeprecatedEqualityOnBinder : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedEqualityOnBinder -> begin
true
end
| uu____976 -> begin
false
end))


let uu___is_Warning_DeprecatedOpaqueQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedOpaqueQualifier -> begin
true
end
| uu____980 -> begin
false
end))


let uu___is_Warning_DocOverwrite : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DocOverwrite -> begin
true
end
| uu____984 -> begin
false
end))


let uu___is_Warning_FileNotWritten : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FileNotWritten -> begin
true
end
| uu____988 -> begin
false
end))


let uu___is_Warning_Filtered : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Filtered -> begin
true
end
| uu____992 -> begin
false
end))


let uu___is_Warning_FunctionLiteralPrecisionLoss : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FunctionLiteralPrecisionLoss -> begin
true
end
| uu____996 -> begin
false
end))


let uu___is_Warning_FunctionNotExtacted : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_FunctionNotExtacted -> begin
true
end
| uu____1000 -> begin
false
end))


let uu___is_Warning_HintFailedToReplayProof : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_HintFailedToReplayProof -> begin
true
end
| uu____1004 -> begin
false
end))


let uu___is_Warning_HitReplayFailed : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_HitReplayFailed -> begin
true
end
| uu____1008 -> begin
false
end))


let uu___is_Warning_IDEIgnoreCodeGen : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IDEIgnoreCodeGen -> begin
true
end
| uu____1012 -> begin
false
end))


let uu___is_Warning_IllFormedGoal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IllFormedGoal -> begin
true
end
| uu____1016 -> begin
false
end))


let uu___is_Warning_InaccessibleArgument : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_InaccessibleArgument -> begin
true
end
| uu____1020 -> begin
false
end))


let uu___is_Warning_IncoherentImplicitQualifier : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IncoherentImplicitQualifier -> begin
true
end
| uu____1024 -> begin
false
end))


let uu___is_Warning_IrrelevantQualifierOnArgumentToReflect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IrrelevantQualifierOnArgumentToReflect -> begin
true
end
| uu____1028 -> begin
false
end))


let uu___is_Warning_IrrelevantQualifierOnArgumentToReify : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_IrrelevantQualifierOnArgumentToReify -> begin
true
end
| uu____1032 -> begin
false
end))


let uu___is_Warning_MalformedWarnErrorList : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MalformedWarnErrorList -> begin
true
end
| uu____1036 -> begin
false
end))


let uu___is_Warning_MetaAlienNotATmUnknown : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MetaAlienNotATmUnknown -> begin
true
end
| uu____1040 -> begin
false
end))


let uu___is_Warning_MultipleAscriptions : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MultipleAscriptions -> begin
true
end
| uu____1044 -> begin
false
end))


let uu___is_Warning_NondependentUserDefinedDataType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NondependentUserDefinedDataType -> begin
true
end
| uu____1048 -> begin
false
end))


let uu___is_Warning_NonListLiteralSMTPattern : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NonListLiteralSMTPattern -> begin
true
end
| uu____1052 -> begin
false
end))


let uu___is_Warning_NormalizationFailure : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NormalizationFailure -> begin
true
end
| uu____1056 -> begin
false
end))


let uu___is_Warning_NotDependentArrow : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NotDependentArrow -> begin
true
end
| uu____1060 -> begin
false
end))


let uu___is_Warning_NotEmbedded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NotEmbedded -> begin
true
end
| uu____1064 -> begin
false
end))


let uu___is_Warning_PatternMissingBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_PatternMissingBoundVar -> begin
true
end
| uu____1068 -> begin
false
end))


let uu___is_Warning_RecursiveDependency : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_RecursiveDependency -> begin
true
end
| uu____1072 -> begin
false
end))


let uu___is_Warning_RedundantExplicitCurrying : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_RedundantExplicitCurrying -> begin
true
end
| uu____1076 -> begin
false
end))


let uu___is_Warning_SMTPatTDeprecated : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_SMTPatTDeprecated -> begin
true
end
| uu____1080 -> begin
false
end))


let uu___is_Warning_SMTPatternMissingBoundVar : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_SMTPatternMissingBoundVar -> begin
true
end
| uu____1084 -> begin
false
end))


let uu___is_Warning_TopLevelEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_TopLevelEffect -> begin
true
end
| uu____1088 -> begin
false
end))


let uu___is_Warning_UnboundModuleReference : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnboundModuleReference -> begin
true
end
| uu____1092 -> begin
false
end))


let uu___is_Warning_UnexpectedFile : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedFile -> begin
true
end
| uu____1096 -> begin
false
end))


let uu___is_Warning_UnexpectedFsTypApp : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedFsTypApp -> begin
true
end
| uu____1100 -> begin
false
end))


let uu___is_Warning_UnexpectedZ3Output : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnexpectedZ3Output -> begin
true
end
| uu____1104 -> begin
false
end))


let uu___is_Warning_UnprotectedTerm : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnprotectedTerm -> begin
true
end
| uu____1108 -> begin
false
end))


let uu___is_Warning_UnrecognizedAttribute : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnrecognizedAttribute -> begin
true
end
| uu____1112 -> begin
false
end))


let uu___is_Warning_UpperBoundCandidateAlreadyVisited : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UpperBoundCandidateAlreadyVisited -> begin
true
end
| uu____1116 -> begin
false
end))


let uu___is_Warning_UseDefaultEffect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UseDefaultEffect -> begin
true
end
| uu____1120 -> begin
false
end))


let uu___is_Warning_WrongErrorLocation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_WrongErrorLocation -> begin
true
end
| uu____1124 -> begin
false
end))


let uu___is_Warning_Z3InvocationWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Z3InvocationWarning -> begin
true
end
| uu____1128 -> begin
false
end))


let uu___is_Warning_CallNotImplementedAsWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CallNotImplementedAsWarning -> begin
true
end
| uu____1132 -> begin
false
end))


let uu___is_Warning_MissingInterfaceOrImplementation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_MissingInterfaceOrImplementation -> begin
true
end
| uu____1136 -> begin
false
end))


let uu___is_Warning_ConstructorBuildsUnexpectedType : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ConstructorBuildsUnexpectedType -> begin
true
end
| uu____1140 -> begin
false
end))


let uu___is_Warning_ModuleOrFileNotFoundWarning : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ModuleOrFileNotFoundWarning -> begin
true
end
| uu____1144 -> begin
false
end))


let uu___is_Error_NoLetMutable : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_NoLetMutable -> begin
true
end
| uu____1148 -> begin
false
end))


let uu___is_Error_BadImplicit : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_BadImplicit -> begin
true
end
| uu____1152 -> begin
false
end))


let uu___is_Warning_DeprecatedDefinition : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_DeprecatedDefinition -> begin
true
end
| uu____1156 -> begin
false
end))


let uu___is_Fatal_SMTEncodingArityMismatch : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_SMTEncodingArityMismatch -> begin
true
end
| uu____1160 -> begin
false
end))


let uu___is_Warning_Defensive : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_Defensive -> begin
true
end
| uu____1164 -> begin
false
end))


let uu___is_Warning_CantInspect : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_CantInspect -> begin
true
end
| uu____1168 -> begin
false
end))


let uu___is_Warning_NilGivenExplicitArgs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_NilGivenExplicitArgs -> begin
true
end
| uu____1172 -> begin
false
end))


let uu___is_Warning_ConsAppliedExplicitArgs : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_ConsAppliedExplicitArgs -> begin
true
end
| uu____1176 -> begin
false
end))


let uu___is_Warning_UnembedBinderKnot : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_UnembedBinderKnot -> begin
true
end
| uu____1180 -> begin
false
end))


let uu___is_Fatal_TacticProofRelevantGoal : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_TacticProofRelevantGoal -> begin
true
end
| uu____1184 -> begin
false
end))


let uu___is_Warning_TacAdmit : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning_TacAdmit -> begin
true
end
| uu____1188 -> begin
false
end))


let uu___is_Fatal_IncoherentPatterns : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_IncoherentPatterns -> begin
true
end
| uu____1192 -> begin
false
end))


let uu___is_Error_NoSMTButNeeded : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error_NoSMTButNeeded -> begin
true
end
| uu____1196 -> begin
false
end))


let uu___is_Fatal_UnexpectedAntiquotation : raw_error  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Fatal_UnexpectedAntiquotation -> begin
true
end
| uu____1200 -> begin
false
end))

type flag =
| CError
| CFatal
| CWarning
| CSilent


let uu___is_CError : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CError -> begin
true
end
| uu____1204 -> begin
false
end))


let uu___is_CFatal : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CFatal -> begin
true
end
| uu____1208 -> begin
false
end))


let uu___is_CWarning : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CWarning -> begin
true
end
| uu____1212 -> begin
false
end))


let uu___is_CSilent : flag  ->  Prims.bool = (fun projectee -> (match (projectee) with
| CSilent -> begin
true
end
| uu____1216 -> begin
false
end))


let default_flags : (raw_error * flag) Prims.list = (((Error_DependencyAnalysisFailed), (CError)))::(((Error_IDETooManyPops), (CError)))::(((Error_IDEUnrecognized), (CError)))::(((Error_InductiveTypeNotSatisfyPositivityCondition), (CError)))::(((Error_InvalidUniverseVar), (CError)))::(((Error_MissingFileName), (CError)))::(((Error_ModuleFileNameMismatch), (CError)))::(((Error_OpPlusInUniverse), (CError)))::(((Error_OutOfRange), (CError)))::(((Error_ProofObligationFailed), (CError)))::(((Error_TooManyFiles), (CError)))::(((Error_TypeCheckerFailToProve), (CError)))::(((Error_TypeError), (CError)))::(((Error_UncontrainedUnificationVar), (CError)))::(((Error_UnexpectedGTotComputation), (CError)))::(((Error_UnexpectedInstance), (CError)))::(((Error_UnknownFatal_AssertionFailure), (CError)))::(((Error_Z3InvocationError), (CError)))::(((Error_IDEAssertionFailure), (CError)))::(((Error_Z3SolverError), (CError)))::(((Fatal_AbstractTypeDeclarationInInterface), (CFatal)))::(((Fatal_ActionMustHaveFunctionType), (CFatal)))::(((Fatal_AlreadyDefinedTopLevelDeclaration), (CFatal)))::(((Fatal_ArgumentLengthMismatch), (CFatal)))::(((Fatal_AssertionFailure), (CFatal)))::(((Fatal_AssignToImmutableValues), (CFatal)))::(((Fatal_AssumeValInInterface), (CFatal)))::(((Fatal_BadlyInstantiatedSynthByTactic), (CFatal)))::(((Fatal_BadSignatureShape), (CFatal)))::(((Fatal_BinderAndArgsLengthMismatch), (CFatal)))::(((Fatal_BothValAndLetInInterface), (CFatal)))::(((Fatal_CardinalityConstraintViolated), (CFatal)))::(((Fatal_ComputationNotTotal), (CFatal)))::(((Fatal_ComputationTypeNotAllowed), (CFatal)))::(((Fatal_ComputedTypeNotMatchAnnotation), (CFatal)))::(((Fatal_ConstructorArgLengthMismatch), (CFatal)))::(((Fatal_ConstructorFailedCheck), (CFatal)))::(((Fatal_ConstructorNotFound), (CFatal)))::(((Fatal_ConstsructorBuildWrongType), (CFatal)))::(((Fatal_CycleInRecTypeAbbreviation), (CFatal)))::(((Fatal_DataContructorNotFound), (CFatal)))::(((Fatal_DefaultQualifierNotAllowedOnEffects), (CFatal)))::(((Fatal_DefinitionNotFound), (CFatal)))::(((Fatal_DisjuctivePatternVarsMismatch), (CFatal)))::(((Fatal_DivergentComputationCannotBeIncludedInTotal), (CFatal)))::(((Fatal_DuplicateInImplementation), (CFatal)))::(((Fatal_DuplicateModuleOrInterface), (CFatal)))::(((Fatal_DuplicateTopLevelNames), (CFatal)))::(((Fatal_DuplicateTypeAnnotationAndValDecl), (CFatal)))::(((Fatal_EffectCannotBeReified), (CFatal)))::(((Fatal_EffectConstructorNotFullyApplied), (CFatal)))::(((Fatal_EffectfulAndPureComputationMismatch), (CFatal)))::(((Fatal_EffectNotFound), (CFatal)))::(((Fatal_EffectsCannotBeComposed), (CFatal)))::(((Fatal_ErrorInSolveDeferredConstraints), (CFatal)))::(((Fatal_ErrorsReported), (CFatal)))::(((Fatal_EscapedBoundVar), (CFatal)))::(((Fatal_ExpectedArrowAnnotatedType), (CFatal)))::(((Fatal_ExpectedGhostExpression), (CFatal)))::(((Fatal_ExpectedPureExpression), (CFatal)))::(((Fatal_ExpectNormalizedEffect), (CFatal)))::(((Fatal_ExpectTermGotFunction), (CFatal)))::(((Fatal_ExpectTrivialPreCondition), (CFatal)))::(((Fatal_FailToExtractNativeTactic), (CFatal)))::(((Fatal_FailToCompileNativeTactic), (CFatal)))::(((Fatal_FailToProcessPragma), (CFatal)))::(((Fatal_FailToResolveImplicitArgument), (CFatal)))::(((Fatal_FailToSolveUniverseInEquality), (CFatal)))::(((Fatal_FieldsNotBelongToSameRecordType), (CFatal)))::(((Fatal_ForbiddenReferenceToCurrentModule), (CFatal)))::(((Fatal_FreeVariables), (CFatal)))::(((Fatal_FunctionTypeExpected), (CFatal)))::(((Fatal_IdentifierNotFound), (CFatal)))::(((Fatal_IllAppliedConstant), (CFatal)))::(((Fatal_IllegalCharInByteArray), (CFatal)))::(((Fatal_IllegalCharInOperatorName), (CFatal)))::(((Fatal_IllTyped), (CFatal)))::(((Fatal_ImpossibleAbbrevLidBundle), (CFatal)))::(((Fatal_ImpossibleAbbrevRenameBundle), (CFatal)))::(((Fatal_ImpossibleInductiveWithAbbrev), (CFatal)))::(((Fatal_ImpossiblePrePostAbs), (CFatal)))::(((Fatal_ImpossiblePrePostArrow), (CFatal)))::(((Fatal_ImpossibleToGenerateDMEffect), (CFatal)))::(((Fatal_ImpossibleTypeAbbrevBundle), (CFatal)))::(((Fatal_ImpossibleTypeAbbrevSigeltBundle), (CFatal)))::(((Fatal_IncludeModuleNotPrepared), (CFatal)))::(((Fatal_IncoherentInlineUniverse), (CFatal)))::(((Fatal_IncompatibleKinds), (CFatal)))::(((Fatal_IncompatibleNumberOfTypes), (CFatal)))::(((Fatal_IncompatibleSetOfUniverse), (CFatal)))::(((Fatal_IncompatibleUniverse), (CFatal)))::(((Fatal_InconsistentImplicitArgumentAnnotation), (CFatal)))::(((Fatal_InconsistentImplicitQualifier), (CFatal)))::(((Fatal_InconsistentQualifierAnnotation), (CFatal)))::(((Fatal_InferredTypeCauseVarEscape), (CFatal)))::(((Fatal_InlineRenamedAsUnfold), (CFatal)))::(((Fatal_InsufficientPatternArguments), (CFatal)))::(((Fatal_InterfaceAlreadyProcessed), (CFatal)))::(((Fatal_InterfaceNotImplementedByModule), (CFatal)))::(((Fatal_InterfaceWithTypeImplementation), (CFatal)))::(((Fatal_InvalidFloatingPointNumber), (CFatal)))::(((Fatal_InvalidFSDocKeyword), (CFatal)))::(((Fatal_InvalidIdentifier), (CFatal)))::(((Fatal_InvalidLemmaArgument), (CFatal)))::(((Fatal_InvalidNumericLiteral), (CFatal)))::(((Fatal_InvalidRedefinitionOfLexT), (CFatal)))::(((Fatal_InvalidUnicodeInStringLiteral), (CFatal)))::(((Fatal_InvalidUTF8Encoding), (CFatal)))::(((Fatal_InvalidWarnErrorSetting), (CFatal)))::(((Fatal_LetBoundMonadicMismatch), (CFatal)))::(((Fatal_LetMutableForVariablesOnly), (CFatal)))::(((Fatal_LetOpenModuleOnly), (CFatal)))::(((Fatal_LetRecArgumentMismatch), (CFatal)))::(((Fatal_MalformedActionDeclaration), (CFatal)))::(((Fatal_MismatchedPatternType), (CFatal)))::(((Fatal_MismatchUniversePolymorphic), (CFatal)))::(((Fatal_MissingDataConstructor), (CFatal)))::(((Fatal_MissingExposeInterfacesOption), (CFatal)))::(((Fatal_MissingFieldInRecord), (CFatal)))::(((Fatal_MissingImplementation), (CFatal)))::(((Fatal_MissingImplicitArguments), (CFatal)))::(((Fatal_MissingInterface), (CFatal)))::(((Fatal_MissingNameInBinder), (CFatal)))::(((Fatal_MissingPrimsModule), (CFatal)))::(((Fatal_MissingQuantifierBinder), (CFatal)))::(((Fatal_ModuleExpected), (CFatal)))::(((Fatal_ModuleFileNotFound), (CFatal)))::(((Fatal_ModuleFirstStatement), (CFatal)))::(((Fatal_ModuleNotFound), (CFatal)))::(((Fatal_ModuleOrFileNotFound), (CFatal)))::(((Fatal_MonadAlreadyDefined), (CFatal)))::(((Fatal_MoreThanOneDeclaration), (CFatal)))::(((Fatal_MultipleLetBinding), (CFatal)))::(((Fatal_NameNotFound), (CFatal)))::(((Fatal_NameSpaceNotFound), (CFatal)))::(((Fatal_NegativeUniverseConstFatal_NotSupported), (CFatal)))::(((Fatal_NoFileProvided), (CFatal)))::(((Fatal_NonInductiveInMutuallyDefinedType), (CFatal)))::(((Fatal_NonLinearPatternNotPermitted), (CFatal)))::(((Fatal_NonLinearPatternVars), (CFatal)))::(((Fatal_NonSingletonTopLevel), (CFatal)))::(((Fatal_NonSingletonTopLevelModule), (CFatal)))::(((Fatal_NonTopRecFunctionNotFullyEncoded), (CFatal)))::(((Fatal_NonTrivialPreConditionInPrims), (CFatal)))::(((Fatal_NonVariableInductiveTypeParameter), (CFatal)))::(((Fatal_NotApplicationOrFv), (CFatal)))::(((Fatal_NotEnoughArgsToEffect), (CFatal)))::(((Fatal_NotEnoughArgumentsForEffect), (CFatal)))::(((Fatal_NotFunctionType), (CFatal)))::(((Fatal_NotSupported), (CFatal)))::(((Fatal_NotTopLevelModule), (CFatal)))::(((Fatal_NotValidFStarFile), (CFatal)))::(((Fatal_NotValidIncludeDirectory), (CFatal)))::(((Fatal_OneModulePerFile), (CFatal)))::(((Fatal_OpenGoalsInSynthesis), (CFatal)))::(((Fatal_OptionsNotCompatible), (CFatal)))::(((Fatal_OutOfOrder), (CFatal)))::(((Fatal_ParseErrors), (CFatal)))::(((Fatal_ParseItError), (CFatal)))::(((Fatal_PolyTypeExpected), (CFatal)))::(((Fatal_PossibleInfiniteTyp), (CFatal)))::(((Fatal_PreModuleMismatch), (CFatal)))::(((Fatal_QulifierListNotPermitted), (CFatal)))::(((Fatal_RecursiveFunctionLiteral), (CFatal)))::(((Fatal_ReflectOnlySupportedOnEffects), (CFatal)))::(((Fatal_ReservedPrefix), (CFatal)))::(((Fatal_SMTOutputParseError), (CFatal)))::(((Fatal_SMTSolverError), (CFatal)))::(((Fatal_SyntaxError), (CFatal)))::(((Fatal_SynthByTacticError), (CFatal)))::(((Fatal_TacticGotStuck), (CFatal)))::(((Fatal_TcOneFragmentFailed), (CFatal)))::(((Fatal_TermOutsideOfDefLanguage), (CFatal)))::(((Fatal_ToManyArgumentToFunction), (CFatal)))::(((Fatal_TooManyOrTooFewFileMatch), (CFatal)))::(((Fatal_TooManyPatternArguments), (CFatal)))::(((Fatal_TooManyUniverse), (CFatal)))::(((Fatal_TypeMismatch), (CFatal)))::(((Fatal_TypeWithinPatternsAllowedOnVariablesOnly), (CFatal)))::(((Fatal_UnableToReadFile), (CFatal)))::(((Fatal_UnepxectedOrUnboundOperator), (CFatal)))::(((Fatal_UnexpectedBinder), (CFatal)))::(((Fatal_UnexpectedBindShape), (CFatal)))::(((Fatal_UnexpectedChar), (CFatal)))::(((Fatal_UnexpectedComputationTypeForLetRec), (CFatal)))::(((Fatal_UnexpectedConstructorType), (CFatal)))::(((Fatal_UnexpectedDataConstructor), (CFatal)))::(((Fatal_UnexpectedEffect), (CFatal)))::(((Fatal_UnexpectedEmptyRecord), (CFatal)))::(((Fatal_UnexpectedExpressionType), (CFatal)))::(((Fatal_UnexpectedFunctionParameterType), (CFatal)))::(((Fatal_UnexpectedGeneralizedUniverse), (CFatal)))::(((Fatal_UnexpectedGTotForLetRec), (CFatal)))::(((Fatal_UnexpectedGuard), (CFatal)))::(((Fatal_UnexpectedIdentifier), (CFatal)))::(((Fatal_UnexpectedImplicitArgument), (CFatal)))::(((Fatal_UnexpectedImplictArgument), (CFatal)))::(((Fatal_UnexpectedInductivetype), (CFatal)))::(((Fatal_UnexpectedLetBinding), (CFatal)))::(((Fatal_UnexpectedModuleDeclaration), (CFatal)))::(((Fatal_UnexpectedNumberOfUniverse), (CFatal)))::(((Fatal_UnexpectedNumericLiteral), (CFatal)))::(((Fatal_UnexpectedOperatorSymbol), (CFatal)))::(((Fatal_UnexpectedPattern), (CFatal)))::(((Fatal_UnexpectedPosition), (CFatal)))::(((Fatal_UnExpectedPreCondition), (CFatal)))::(((Fatal_UnexpectedReturnShape), (CFatal)))::(((Fatal_UnexpectedSignatureForMonad), (CFatal)))::(((Fatal_UnexpectedTerm), (CFatal)))::(((Fatal_UnexpectedTermInUniverse), (CFatal)))::(((Fatal_UnexpectedTermType), (CFatal)))::(((Fatal_UnexpectedTermVQuote), (CFatal)))::(((Fatal_UnexpectedUniversePolymorphicReturn), (CFatal)))::(((Fatal_UnexpectedUniverseVariable), (CFatal)))::(((Fatal_UnfoldableDeprecated), (CFatal)))::(((Fatal_UnificationNotWellFormed), (CFatal)))::(((Fatal_Uninstantiated), (CFatal)))::(((Fatal_UninstantiatedUnificationVarInTactic), (CFatal)))::(((Fatal_UninstantiatedVarInTactic), (CFatal)))::(((Fatal_UniverseMightContainSumOfTwoUnivVars), (CFatal)))::(((Fatal_UniversePolymorphicInnerLetBound), (CFatal)))::(((Fatal_UnknownAttribute), (CFatal)))::(((Fatal_UnknownToolForDep), (CFatal)))::(((Fatal_UnrecognizedExtension), (CFatal)))::(((Fatal_UnresolvedPatternVar), (CFatal)))::(((Fatal_UnsupportedConstant), (CFatal)))::(((Fatal_UnsupportedDisjuctivePatterns), (CFatal)))::(((Fatal_UnsupportedQualifier), (CFatal)))::(((Fatal_UserTacticFailure), (CFatal)))::(((Fatal_ValueRestriction), (CFatal)))::(((Fatal_VariableNotFound), (CFatal)))::(((Fatal_WrongBodyTypeForReturnWP), (CFatal)))::(((Fatal_WrongDataAppHeadFormat), (CFatal)))::(((Fatal_WrongDefinitionOrder), (CFatal)))::(((Fatal_WrongResultTypeAfterConstrutor), (CFatal)))::(((Fatal_WrongTerm), (CFatal)))::(((Fatal_WhenClauseNotSupported), (CFatal)))::(((Unused01), (CFatal)))::(((Warning_CallNotImplementedAsWarning), (CWarning)))::(((Warning_AddImplicitAssumeNewQualifier), (CWarning)))::(((Warning_AdmitWithoutDefinition), (CWarning)))::(((Warning_CachedFile), (CWarning)))::(((Warning_DefinitionNotTranslated), (CWarning)))::(((Warning_DependencyFound), (CWarning)))::(((Warning_DeprecatedEqualityOnBinder), (CWarning)))::(((Warning_DeprecatedOpaqueQualifier), (CWarning)))::(((Warning_DocOverwrite), (CWarning)))::(((Warning_FileNotWritten), (CWarning)))::(((Warning_Filtered), (CWarning)))::(((Warning_FunctionLiteralPrecisionLoss), (CWarning)))::(((Warning_FunctionNotExtacted), (CWarning)))::(((Warning_HintFailedToReplayProof), (CWarning)))::(((Warning_HitReplayFailed), (CWarning)))::(((Warning_IDEIgnoreCodeGen), (CWarning)))::(((Warning_IllFormedGoal), (CWarning)))::(((Warning_InaccessibleArgument), (CWarning)))::(((Warning_IncoherentImplicitQualifier), (CWarning)))::(((Warning_IrrelevantQualifierOnArgumentToReflect), (CWarning)))::(((Warning_IrrelevantQualifierOnArgumentToReify), (CWarning)))::(((Warning_MalformedWarnErrorList), (CWarning)))::(((Warning_MetaAlienNotATmUnknown), (CWarning)))::(((Warning_MultipleAscriptions), (CWarning)))::(((Warning_NondependentUserDefinedDataType), (CWarning)))::(((Warning_NonListLiteralSMTPattern), (CWarning)))::(((Warning_NormalizationFailure), (CWarning)))::(((Warning_NotDependentArrow), (CWarning)))::(((Warning_NotEmbedded), (CWarning)))::(((Warning_PatternMissingBoundVar), (CWarning)))::(((Warning_RecursiveDependency), (CWarning)))::(((Warning_RedundantExplicitCurrying), (CWarning)))::(((Warning_SMTPatTDeprecated), (CWarning)))::(((Warning_SMTPatternMissingBoundVar), (CWarning)))::(((Warning_TopLevelEffect), (CWarning)))::(((Warning_UnboundModuleReference), (CWarning)))::(((Warning_UnexpectedFile), (CWarning)))::(((Warning_UnexpectedFsTypApp), (CWarning)))::(((Warning_UnexpectedZ3Output), (CWarning)))::(((Warning_UnprotectedTerm), (CWarning)))::(((Warning_UnrecognizedAttribute), (CWarning)))::(((Warning_UpperBoundCandidateAlreadyVisited), (CWarning)))::(((Warning_UseDefaultEffect), (CWarning)))::(((Warning_WrongErrorLocation), (CWarning)))::(((Warning_Z3InvocationWarning), (CWarning)))::(((Warning_MissingInterfaceOrImplementation), (CWarning)))::(((Warning_ConstructorBuildsUnexpectedType), (CWarning)))::(((Warning_ModuleOrFileNotFoundWarning), (CWarning)))::(((Error_NoLetMutable), (CError)))::(((Error_BadImplicit), (CError)))::(((Warning_DeprecatedDefinition), (CWarning)))::(((Fatal_SMTEncodingArityMismatch), (CFatal)))::(((Warning_Defensive), (CWarning)))::(((Warning_CantInspect), (CWarning)))::(((Warning_NilGivenExplicitArgs), (CWarning)))::(((Warning_ConsAppliedExplicitArgs), (CWarning)))::(((Warning_UnembedBinderKnot), (CWarning)))::(((Fatal_TacticProofRelevantGoal), (CFatal)))::(((Warning_TacAdmit), (CWarning)))::(((Fatal_IncoherentPatterns), (CFatal)))::(((Error_NoSMTButNeeded), (CError)))::(((Fatal_UnexpectedAntiquotation), (CFatal)))::[]

exception Err of ((raw_error * Prims.string))


let uu___is_Err : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Err (uu____2437) -> begin
true
end
| uu____2442 -> begin
false
end))


let __proj__Err__item__uu___ : Prims.exn  ->  (raw_error * Prims.string) = (fun projectee -> (match (projectee) with
| Err (uu____2457) -> begin
uu____2457
end))

exception Error of ((raw_error * Prims.string * FStar_Range.range))


let uu___is_Error : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Error (uu____2474) -> begin
true
end
| uu____2481 -> begin
false
end))


let __proj__Error__item__uu___ : Prims.exn  ->  (raw_error * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Error (uu____2500) -> begin
uu____2500
end))

exception Warning of ((raw_error * Prims.string * FStar_Range.range))


let uu___is_Warning : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Warning (uu____2519) -> begin
true
end
| uu____2526 -> begin
false
end))


let __proj__Warning__item__uu___ : Prims.exn  ->  (raw_error * Prims.string * FStar_Range.range) = (fun projectee -> (match (projectee) with
| Warning (uu____2545) -> begin
uu____2545
end))

exception Stop


let uu___is_Stop : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Stop -> begin
true
end
| uu____2555 -> begin
false
end))

exception Empty_frag


let uu___is_Empty_frag : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Empty_frag -> begin
true
end
| uu____2559 -> begin
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
| uu____2563 -> begin
false
end))


let uu___is_EInfo : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EInfo -> begin
true
end
| uu____2567 -> begin
false
end))


let uu___is_EWarning : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EWarning -> begin
true
end
| uu____2571 -> begin
false
end))


let uu___is_EError : issue_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| EError -> begin
true
end
| uu____2575 -> begin
false
end))

type issue =
{issue_message : Prims.string; issue_level : issue_level; issue_range : FStar_Range.range FStar_Pervasives_Native.option; issue_number : Prims.int FStar_Pervasives_Native.option}


let __proj__Mkissue__item__issue_message : issue  ->  Prims.string = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range; issue_number = __fname__issue_number} -> begin
__fname__issue_message
end))


let __proj__Mkissue__item__issue_level : issue  ->  issue_level = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range; issue_number = __fname__issue_number} -> begin
__fname__issue_level
end))


let __proj__Mkissue__item__issue_range : issue  ->  FStar_Range.range FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range; issue_number = __fname__issue_number} -> begin
__fname__issue_range
end))


let __proj__Mkissue__item__issue_number : issue  ->  Prims.int FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {issue_message = __fname__issue_message; issue_level = __fname__issue_level; issue_range = __fname__issue_range; issue_number = __fname__issue_number} -> begin
__fname__issue_number
end))

type error_handler =
{eh_add_one : issue  ->  Prims.unit; eh_count_errors : Prims.unit  ->  Prims.int; eh_report : Prims.unit  ->  issue Prims.list; eh_clear : Prims.unit  ->  Prims.unit}


let __proj__Mkerror_handler__item__eh_add_one : error_handler  ->  issue  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_add_one
end))


let __proj__Mkerror_handler__item__eh_count_errors : error_handler  ->  Prims.unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_count_errors
end))


let __proj__Mkerror_handler__item__eh_report : error_handler  ->  Prims.unit  ->  issue Prims.list = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_report
end))


let __proj__Mkerror_handler__item__eh_clear : error_handler  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {eh_add_one = __fname__eh_add_one; eh_count_errors = __fname__eh_count_errors; eh_report = __fname__eh_report; eh_clear = __fname__eh_clear} -> begin
__fname__eh_clear
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

let uu____2774 = (match (issue.issue_range) with
| FStar_Pervasives_Native.None -> begin
((""), (""))
end
| FStar_Pervasives_Native.Some (r) -> begin
(

let uu____2784 = (

let uu____2785 = (FStar_Range.string_of_use_range r)
in (FStar_Util.format1 "%s: " uu____2785))
in (

let uu____2786 = (

let uu____2787 = (

let uu____2788 = (FStar_Range.use_range r)
in (

let uu____2789 = (FStar_Range.def_range r)
in (Prims.op_Equality uu____2788 uu____2789)))
in (match (uu____2787) with
| true -> begin
""
end
| uu____2790 -> begin
(

let uu____2791 = (FStar_Range.string_of_range r)
in (FStar_Util.format1 " (see also %s)" uu____2791))
end))
in ((uu____2784), (uu____2786))))
end)
in (match (uu____2774) with
| (range_str, see_also_str) -> begin
(

let issue_number = (match (issue.issue_number) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (n1) -> begin
(

let uu____2796 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 " %s" uu____2796))
end)
in (FStar_Util.format5 "%s(%s%s) %s%s\n" range_str level_header issue_number issue.issue_message see_also_str))
end))))


let print_issue : issue  ->  Prims.unit = (fun issue -> (

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

let uu____2805 = (format_issue issue)
in (printer uu____2805))))


let compare_issues : issue  ->  issue  ->  Prims.int = (fun i1 i2 -> (match (((i1.issue_range), (i2.issue_range))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "0")
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____2820)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Pervasives_Native.Some (uu____2825), FStar_Pervasives_Native.None) -> begin
(Prims.parse_int "1")
end
| (FStar_Pervasives_Native.Some (r1), FStar_Pervasives_Native.Some (r2)) -> begin
(FStar_Range.compare_use_range r1 r2)
end))


let default_handler : error_handler = (

let errs = (FStar_Util.mk_ref [])
in (

let add_one = (fun e -> (match (e.issue_level) with
| EError -> begin
(

let uu____2847 = (

let uu____2850 = (FStar_ST.op_Bang errs)
in (e)::uu____2850)
in (FStar_ST.op_Colon_Equals errs uu____2847))
end
| uu____3051 -> begin
(print_issue e)
end))
in (

let count_errors = (fun uu____3055 -> (

let uu____3056 = (FStar_ST.op_Bang errs)
in (FStar_List.length uu____3056)))
in (

let report = (fun uu____3163 -> (

let sorted1 = (

let uu____3167 = (FStar_ST.op_Bang errs)
in (FStar_List.sortWith compare_issues uu____3167))
in ((FStar_List.iter print_issue sorted1);
sorted1;
)))
in (

let clear1 = (fun uu____3273 -> (FStar_ST.op_Colon_Equals errs []))
in {eh_add_one = add_one; eh_count_errors = count_errors; eh_report = report; eh_clear = clear1})))))


let current_handler : error_handler FStar_ST.ref = (FStar_Util.mk_ref default_handler)


let mk_issue : issue_level  ->  FStar_Range.range FStar_Pervasives_Native.option  ->  Prims.string  ->  Prims.int FStar_Pervasives_Native.option  ->  issue = (fun level range msg n1 -> {issue_message = msg; issue_level = level; issue_range = range; issue_number = n1})


let get_err_count : Prims.unit  ->  Prims.int = (fun uu____3436 -> (

let uu____3437 = (

let uu____3440 = (FStar_ST.op_Bang current_handler)
in uu____3440.eh_count_errors)
in (uu____3437 ())))


let add_one : issue  ->  Prims.unit = (fun issue -> (FStar_Util.atomically (fun uu____3471 -> (

let uu____3472 = (

let uu____3475 = (FStar_ST.op_Bang current_handler)
in uu____3475.eh_add_one)
in (uu____3472 issue)))))


let add_many : issue Prims.list  ->  Prims.unit = (fun issues -> (FStar_Util.atomically (fun uu____3510 -> (

let uu____3511 = (

let uu____3514 = (FStar_ST.op_Bang current_handler)
in uu____3514.eh_add_one)
in (FStar_List.iter uu____3511 issues)))))


let report_all : Prims.unit  ->  issue Prims.list = (fun uu____3544 -> (

let uu____3545 = (

let uu____3550 = (FStar_ST.op_Bang current_handler)
in uu____3550.eh_report)
in (uu____3545 ())))


let clear : Prims.unit  ->  Prims.unit = (fun uu____3578 -> (

let uu____3579 = (

let uu____3582 = (FStar_ST.op_Bang current_handler)
in uu____3582.eh_clear)
in (uu____3579 ())))


let set_handler : error_handler  ->  Prims.unit = (fun handler -> (

let issues = (report_all ())
in ((clear ());
(FStar_ST.op_Colon_Equals current_handler handler);
(add_many issues);
)))

type error_message_prefix =
{set_prefix : Prims.string  ->  Prims.unit; append_prefix : Prims.string  ->  Prims.string; clear_prefix : Prims.unit  ->  Prims.unit}


let __proj__Mkerror_message_prefix__item__set_prefix : error_message_prefix  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {set_prefix = __fname__set_prefix; append_prefix = __fname__append_prefix; clear_prefix = __fname__clear_prefix} -> begin
__fname__set_prefix
end))


let __proj__Mkerror_message_prefix__item__append_prefix : error_message_prefix  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {set_prefix = __fname__set_prefix; append_prefix = __fname__append_prefix; clear_prefix = __fname__clear_prefix} -> begin
__fname__append_prefix
end))


let __proj__Mkerror_message_prefix__item__clear_prefix : error_message_prefix  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {set_prefix = __fname__set_prefix; append_prefix = __fname__append_prefix; clear_prefix = __fname__clear_prefix} -> begin
__fname__clear_prefix
end))


let message_prefix : error_message_prefix = (

let pfx = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_prefix = (fun s -> (FStar_ST.op_Colon_Equals pfx (FStar_Pervasives_Native.Some (s))))
in (

let clear_prefix = (fun uu____3826 -> (FStar_ST.op_Colon_Equals pfx FStar_Pervasives_Native.None))
in (

let append_prefix = (fun s -> (

let uu____3930 = (FStar_ST.op_Bang pfx)
in (match (uu____3930) with
| FStar_Pervasives_Native.None -> begin
s
end
| FStar_Pervasives_Native.Some (p) -> begin
(Prims.strcat p (Prims.strcat ": " s))
end)))
in {set_prefix = set_prefix; append_prefix = append_prefix; clear_prefix = clear_prefix}))))


let findIndex : 'Auu____4037 'Auu____4038 . ('Auu____4037 * 'Auu____4038) Prims.list  ->  'Auu____4037  ->  Prims.int = (fun l v1 -> (FStar_All.pipe_right l (FStar_List.index (fun uu___29_4072 -> (match (uu___29_4072) with
| (e, uu____4078) when (Prims.op_Equality e v1) -> begin
true
end
| uu____4079 -> begin
false
end)))))


let errno_of_error : raw_error  ->  Prims.int = (fun e -> (findIndex default_flags e))


let flags : flag Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_warn_error_flags : Prims.unit = (

let rec aux = (fun r l -> (match (l) with
| [] -> begin
r
end
| ((e, f))::tl1 -> begin
(aux (FStar_List.append r ((f)::[])) tl1)
end))
in (

let uu____4172 = (aux [] default_flags)
in (FStar_ST.op_Colon_Equals flags uu____4172)))


let diag : FStar_Range.range  ->  Prims.string  ->  Prims.unit = (fun r msg -> (

let uu____4210 = (FStar_Options.debug_any ())
in (match (uu____4210) with
| true -> begin
(add_one (mk_issue EInfo (FStar_Pervasives_Native.Some (r)) msg FStar_Pervasives_Native.None))
end
| uu____4211 -> begin
()
end)))


let defensive_errno : Prims.int = (errno_of_error Warning_Defensive)


let lookup : flag Prims.list  ->  Prims.int  ->  flag = (fun flags1 errno -> (

let uu____4222 = ((Prims.op_Equality errno defensive_errno) && (FStar_Options.defensive_fail ()))
in (match (uu____4222) with
| true -> begin
CError
end
| uu____4223 -> begin
(FStar_List.nth flags1 errno)
end)))


let log_issue : FStar_Range.range  ->  (raw_error * Prims.string)  ->  Prims.unit = (fun r uu____4233 -> (match (uu____4233) with
| (e, msg) -> begin
(

let errno = (errno_of_error e)
in (

let uu____4241 = (

let uu____4242 = (FStar_ST.op_Bang flags)
in (lookup uu____4242 errno))
in (match (uu____4241) with
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

let uu____4275 = (FStar_Options.ide ())
in (match (uu____4275) with
| true -> begin
(add_one i)
end
| uu____4276 -> begin
(

let uu____4277 = (

let uu____4278 = (format_issue i)
in (Prims.strcat "don\'t use log_issue to report fatal error, should use raise_error: " uu____4278))
in (failwith uu____4277))
end)))
end)))
end))


let add_errors : (raw_error * Prims.string * FStar_Range.range) Prims.list  ->  Prims.unit = (fun errs -> (FStar_Util.atomically (fun uu____4299 -> (FStar_List.iter (fun uu____4311 -> (match (uu____4311) with
| (e, msg, r) -> begin
(

let uu____4321 = (

let uu____4326 = (message_prefix.append_prefix msg)
in ((e), (uu____4326)))
in (log_issue r uu____4321))
end)) errs))))


let issue_of_exn : Prims.exn  ->  issue FStar_Pervasives_Native.option = (fun uu___30_4331 -> (match (uu___30_4331) with
| Error (e, msg, r) -> begin
(

let errno = (errno_of_error e)
in (

let uu____4338 = (

let uu____4339 = (message_prefix.append_prefix msg)
in (mk_issue EError (FStar_Pervasives_Native.Some (r)) uu____4339 (FStar_Pervasives_Native.Some (errno))))
in FStar_Pervasives_Native.Some (uu____4338)))
end
| FStar_Util.NYI (msg) -> begin
(

let uu____4341 = (

let uu____4342 = (message_prefix.append_prefix msg)
in (mk_issue ENotImplemented FStar_Pervasives_Native.None uu____4342 FStar_Pervasives_Native.None))
in FStar_Pervasives_Native.Some (uu____4341))
end
| Err (e, msg) -> begin
(

let errno = (errno_of_error e)
in (

let uu____4346 = (

let uu____4347 = (message_prefix.append_prefix msg)
in (mk_issue EError FStar_Pervasives_Native.None uu____4347 (FStar_Pervasives_Native.Some (errno))))
in FStar_Pervasives_Native.Some (uu____4346)))
end
| uu____4348 -> begin
FStar_Pervasives_Native.None
end))


let err_exn : Prims.exn  ->  Prims.unit = (fun exn -> (match ((Prims.op_Equality exn Stop)) with
| true -> begin
()
end
| uu____4352 -> begin
(

let uu____4353 = (issue_of_exn exn)
in (match (uu____4353) with
| FStar_Pervasives_Native.Some (issue) -> begin
(add_one issue)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise exn)
end))
end))


let handleable : Prims.exn  ->  Prims.bool = (fun uu___31_4359 -> (match (uu___31_4359) with
| Error (uu____4360) -> begin
true
end
| FStar_Util.NYI (uu____4367) -> begin
true
end
| Stop -> begin
true
end
| Err (uu____4368) -> begin
true
end
| uu____4373 -> begin
false
end))


let stop_if_err : Prims.unit  ->  Prims.unit = (fun uu____4376 -> (

let uu____4377 = (

let uu____4378 = (get_err_count ())
in (uu____4378 > (Prims.parse_int "0")))
in (match (uu____4377) with
| true -> begin
(FStar_Exn.raise Stop)
end
| uu____4379 -> begin
()
end)))


let raise_error : 'Auu____4383 . (raw_error * Prims.string)  ->  FStar_Range.range  ->  'Auu____4383 = (fun uu____4394 r -> (match (uu____4394) with
| (e, msg) -> begin
(FStar_Exn.raise (Error (((e), (msg), (r)))))
end))


let raise_err : 'Auu____4404 . (raw_error * Prims.string)  ->  'Auu____4404 = (fun uu____4412 -> (match (uu____4412) with
| (e, msg) -> begin
(FStar_Exn.raise (Err (((e), (msg)))))
end))


let update_flags : (flag * Prims.string) Prims.list  ->  Prims.unit = (fun l -> (

let compare1 = (fun uu____4455 uu____4456 -> (match (((uu____4455), (uu____4456))) with
| ((uu____4489, (a, uu____4491)), (uu____4492, (b, uu____4494))) -> begin
(match ((a > b)) with
| true -> begin
(Prims.parse_int "1")
end
| uu____4519 -> begin
(match ((a < b)) with
| true -> begin
(~- ((Prims.parse_int "1")))
end
| uu____4520 -> begin
(Prims.parse_int "0")
end)
end)
end))
in (

let set_one_flag = (fun f d -> (match (((f), (d))) with
| (CWarning, CError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot turn an error into warning")))
end
| (CSilent, CError) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot silence an error")))
end
| (uu____4528, CFatal) -> begin
(raise_err ((Fatal_InvalidWarnErrorSetting), ("cannot reset the error level of a fatal error")))
end
| uu____4529 -> begin
f
end))
in (

let rec set_flag = (fun i l1 -> (

let d = (

let uu____4562 = (FStar_ST.op_Bang flags)
in (FStar_List.nth uu____4562 i))
in (match (l1) with
| [] -> begin
d
end
| ((f, (l2, h)))::tl1 -> begin
(match (((i >= l2) && (i <= h))) with
| true -> begin
(set_one_flag f d)
end
| uu____4628 -> begin
(match ((i < l2)) with
| true -> begin
d
end
| uu____4629 -> begin
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

let uu____4679 = (

let uu____4682 = (

let uu____4685 = (set_flag i sorted1)
in (uu____4685)::[])
in (FStar_List.append f uu____4682))
in (aux uu____4679 (i + (Prims.parse_int "1")) tl1 sorted1))
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

let uu____4765 = (match (r) with
| (r1)::(r2)::[] -> begin
(

let uu____4776 = (FStar_Util.int_of_string r1)
in (

let uu____4777 = (FStar_Util.int_of_string r2)
in ((uu____4776), (uu____4777))))
end
| uu____4778 -> begin
(

let uu____4781 = (

let uu____4786 = (FStar_Util.format1 "Malformed warn-error range %s" s)
in ((Fatal_InvalidWarnErrorSetting), (uu____4786)))
in (raise_err uu____4781))
end)
in (match (uu____4765) with
| (l2, h) -> begin
((match (((l2 < (Prims.parse_int "0")) || (h >= (FStar_List.length default_flags)))) with
| true -> begin
(

let uu____4808 = (

let uu____4813 = (

let uu____4814 = (FStar_Util.string_of_int l2)
in (

let uu____4815 = (FStar_Util.string_of_int h)
in (FStar_Util.format2 "No error for warn_error %s..%s" uu____4814 uu____4815)))
in ((Fatal_InvalidWarnErrorSetting), (uu____4813)))
in (raise_err uu____4808))
end
| uu____4816 -> begin
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

let uu____4883 = (

let uu____4886 = (FStar_ST.op_Bang flags)
in (aux [] (Prims.parse_int "0") uu____4886 sorted1))
in (FStar_ST.op_Colon_Equals flags uu____4883))))))))))




