#light "off"
module FStar.Errors
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Util
open FStar.Range

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

type flag =
  | CFatal          //CFatal: these are reported using a raise_error: compiler cannot progress
  | CAlwaysError    //CAlwaysError: these errors are reported using log_issue and cannot be suppressed
                    //the compiler can progress after reporting them
  | CError          //CError: these are reported as errors using log_issue
                    //        but they can be turned into warnings or silenced
  | CWarning        //CWarning: reported using log_issue as warnings by default;
                    //          then can be silenced or escalated to errors
  | CSilent         //CSilent: never the default for any issue, but warnings can be silenced

// This list should be considered STABLE
// Which means, if you need to add an error, APPEND it, to keep old error numbers the same
// If an error is deprecated, do not remove it! Change its name (if needed)
let default_flags =
 [(Error_DependencyAnalysisFailed                    , CAlwaysError);
  (Error_IDETooManyPops                              , CAlwaysError);
  (Error_IDEUnrecognized                             , CAlwaysError);
  (Error_InductiveTypeNotSatisfyPositivityCondition  , CAlwaysError);
  (Error_InvalidUniverseVar                          , CAlwaysError);
  (Error_MissingFileName                             , CAlwaysError);
  (Error_ModuleFileNameMismatch                      , CAlwaysError);
  (Error_OpPlusInUniverse                            , CAlwaysError);
  (Error_OutOfRange                                  , CAlwaysError);
  (Error_ProofObligationFailed                       , CAlwaysError);
  (Error_TooManyFiles                                , CAlwaysError);
  (Error_TypeCheckerFailToProve                      , CAlwaysError);
  (Error_TypeError                                   , CAlwaysError);
  (Error_UncontrainedUnificationVar                  , CAlwaysError);
  (Error_UnexpectedGTotComputation                   , CAlwaysError);
  (Error_UnexpectedInstance                          , CAlwaysError);
  (Error_UnknownFatal_AssertionFailure               , CAlwaysError);
  (Error_Z3InvocationError                           , CAlwaysError);
  (Error_IDEAssertionFailure                         , CAlwaysError);
  (Error_Z3SolverError                               , CAlwaysError);
  (Fatal_AbstractTypeDeclarationInInterface          , CFatal);
  (Fatal_ActionMustHaveFunctionType                  , CFatal);
  (Fatal_AlreadyDefinedTopLevelDeclaration           , CFatal);
  (Fatal_ArgumentLengthMismatch                      , CFatal);
  (Fatal_AssertionFailure                            , CFatal);
  (Fatal_AssignToImmutableValues                     , CFatal);
  (Fatal_AssumeValInInterface                        , CFatal);
  (Fatal_BadlyInstantiatedSynthByTactic              , CFatal);
  (Fatal_BadSignatureShape                           , CFatal);
  (Fatal_BinderAndArgsLengthMismatch                 , CFatal);
  (Fatal_BothValAndLetInInterface                    , CFatal);
  (Fatal_CardinalityConstraintViolated               , CFatal);
  (Fatal_ComputationNotTotal                         , CFatal);
  (Fatal_ComputationTypeNotAllowed                   , CFatal);
  (Fatal_ComputedTypeNotMatchAnnotation              , CFatal);
  (Fatal_ConstructorArgLengthMismatch                , CFatal);
  (Fatal_ConstructorFailedCheck                      , CFatal);
  (Fatal_ConstructorNotFound                         , CFatal);
  (Fatal_ConstsructorBuildWrongType                  , CFatal);
  (Fatal_CycleInRecTypeAbbreviation                  , CFatal);
  (Fatal_DataContructorNotFound                      , CFatal);
  (Fatal_DefaultQualifierNotAllowedOnEffects         , CFatal);
  (Fatal_DefinitionNotFound                          , CFatal);
  (Fatal_DisjuctivePatternVarsMismatch               , CFatal);
  (Fatal_DivergentComputationCannotBeIncludedInTotal , CFatal);
  (Fatal_DuplicateInImplementation                   , CFatal);
  (Fatal_DuplicateModuleOrInterface                  , CFatal);
  (Fatal_DuplicateTopLevelNames                      , CFatal);
  (Fatal_DuplicateTypeAnnotationAndValDecl           , CFatal);
  (Fatal_EffectCannotBeReified                       , CFatal);
  (Fatal_EffectConstructorNotFullyApplied            , CFatal);
  (Fatal_EffectfulAndPureComputationMismatch         , CFatal);
  (Fatal_EffectNotFound                              , CFatal);
  (Fatal_EffectsCannotBeComposed                     , CFatal);
  (Fatal_ErrorInSolveDeferredConstraints             , CFatal);
  (Fatal_ErrorsReported                              , CFatal);
  (Fatal_EscapedBoundVar                             , CFatal);
  (Fatal_ExpectedArrowAnnotatedType                  , CFatal);
  (Fatal_ExpectedGhostExpression                     , CFatal);
  (Fatal_ExpectedPureExpression                      , CFatal);
  (Fatal_ExpectNormalizedEffect                      , CFatal);
  (Fatal_ExpectTermGotFunction                       , CFatal);
  (Fatal_ExpectTrivialPreCondition                   , CFatal);
  (Fatal_FailToExtractNativeTactic                   , CFatal);
  (Fatal_FailToCompileNativeTactic                   , CFatal);
  (Fatal_FailToProcessPragma                         , CFatal);
  (Fatal_FailToResolveImplicitArgument               , CFatal);
  (Fatal_FailToSolveUniverseInEquality               , CFatal);
  (Fatal_FieldsNotBelongToSameRecordType             , CFatal);
  (Fatal_ForbiddenReferenceToCurrentModule           , CFatal);
  (Fatal_FreeVariables                               , CFatal);
  (Fatal_FunctionTypeExpected                        , CFatal);
  (Fatal_IdentifierNotFound                          , CFatal);
  (Fatal_IllAppliedConstant                          , CFatal);
  (Fatal_IllegalCharInByteArray                      , CFatal);
  (Fatal_IllegalCharInOperatorName                   , CFatal);
  (Fatal_IllTyped                                    , CFatal);
  (Fatal_ImpossibleAbbrevLidBundle                   , CFatal);
  (Fatal_ImpossibleAbbrevRenameBundle                , CFatal);
  (Fatal_ImpossibleInductiveWithAbbrev               , CFatal);
  (Fatal_ImpossiblePrePostAbs                        , CFatal);
  (Fatal_ImpossiblePrePostArrow                      , CFatal);
  (Fatal_ImpossibleToGenerateDMEffect                , CFatal);
  (Fatal_ImpossibleTypeAbbrevBundle                  , CFatal);
  (Fatal_ImpossibleTypeAbbrevSigeltBundle            , CFatal);
  (Fatal_IncludeModuleNotPrepared                    , CFatal);
  (Fatal_IncoherentInlineUniverse                    , CFatal);
  (Fatal_IncompatibleKinds                           , CFatal);
  (Fatal_IncompatibleNumberOfTypes                   , CFatal);
  (Fatal_IncompatibleSetOfUniverse                   , CFatal);
  (Fatal_IncompatibleUniverse                        , CFatal);
  (Fatal_InconsistentImplicitArgumentAnnotation      , CFatal);
  (Fatal_InconsistentImplicitQualifier               , CFatal);
  (Fatal_InconsistentQualifierAnnotation             , CFatal);
  (Fatal_InferredTypeCauseVarEscape                  , CFatal);
  (Fatal_InlineRenamedAsUnfold                       , CFatal);
  (Fatal_InsufficientPatternArguments                , CFatal);
  (Fatal_InterfaceAlreadyProcessed                   , CFatal);
  (Fatal_InterfaceNotImplementedByModule             , CFatal);
  (Fatal_InterfaceWithTypeImplementation             , CFatal);
  (Fatal_InvalidFloatingPointNumber                  , CFatal);
  (Fatal_InvalidFSDocKeyword                         , CFatal);
  (Fatal_InvalidIdentifier                           , CFatal);
  (Fatal_InvalidLemmaArgument                        , CFatal);
  (Fatal_InvalidNumericLiteral                       , CFatal);
  (Fatal_InvalidRedefinitionOfLexT                   , CFatal);
  (Fatal_InvalidUnicodeInStringLiteral               , CFatal);
  (Fatal_InvalidUTF8Encoding                         , CFatal);
  (Fatal_InvalidWarnErrorSetting                     , CFatal);
  (Fatal_LetBoundMonadicMismatch                     , CFatal);
  (Fatal_LetMutableForVariablesOnly                  , CFatal);
  (Fatal_LetOpenModuleOnly                           , CFatal);
  (Fatal_LetRecArgumentMismatch                      , CFatal);
  (Fatal_MalformedActionDeclaration                  , CFatal);
  (Fatal_MismatchedPatternType                       , CFatal);
  (Fatal_MismatchUniversePolymorphic                 , CFatal);
  (Fatal_MissingDataConstructor                      , CFatal);
  (Fatal_MissingExposeInterfacesOption               , CFatal);
  (Fatal_MissingFieldInRecord                        , CFatal);
  (Fatal_MissingImplementation                       , CFatal);
  (Fatal_MissingImplicitArguments                    , CFatal);
  (Fatal_MissingInterface                            , CFatal);
  (Fatal_MissingNameInBinder                         , CFatal);
  (Fatal_MissingPrimsModule                          , CFatal);
  (Fatal_MissingQuantifierBinder                     , CFatal);
  (Fatal_ModuleExpected                              , CFatal);
  (Fatal_ModuleFileNotFound                          , CFatal);
  (Fatal_ModuleFirstStatement                        , CFatal);
  (Fatal_ModuleNotFound                              , CFatal);
  (Fatal_ModuleOrFileNotFound                        , CFatal);
  (Fatal_MonadAlreadyDefined                         , CFatal);
  (Fatal_MoreThanOneDeclaration                      , CFatal);
  (Fatal_MultipleLetBinding                          , CFatal);
  (Fatal_NameNotFound                                , CFatal);
  (Fatal_NameSpaceNotFound                           , CFatal);
  (Fatal_NegativeUniverseConstFatal_NotSupported     , CFatal);
  (Fatal_NoFileProvided                              , CFatal);
  (Fatal_NonInductiveInMutuallyDefinedType           , CFatal);
  (Fatal_NonLinearPatternNotPermitted                , CFatal);
  (Fatal_NonLinearPatternVars                        , CFatal);
  (Fatal_NonSingletonTopLevel                        , CFatal);
  (Fatal_NonSingletonTopLevelModule                  , CFatal);
  (Fatal_NonTopRecFunctionNotFullyEncoded            , CFatal);
  (Fatal_NonTrivialPreConditionInPrims               , CFatal);
  (Fatal_NonVariableInductiveTypeParameter           , CFatal);
  (Fatal_NotApplicationOrFv                          , CFatal);
  (Fatal_NotEnoughArgsToEffect                       , CFatal);
  (Fatal_NotEnoughArgumentsForEffect                 , CFatal);
  (Fatal_NotFunctionType                             , CFatal);
  (Fatal_NotSupported                                , CFatal);
  (Fatal_NotTopLevelModule                           , CFatal);
  (Fatal_NotValidFStarFile                           , CFatal);
  (Fatal_NotValidIncludeDirectory                    , CFatal);
  (Fatal_OneModulePerFile                            , CFatal);
  (Fatal_OpenGoalsInSynthesis                        , CFatal);
  (Fatal_OptionsNotCompatible                        , CFatal);
  (Fatal_OutOfOrder                                  , CFatal);
  (Fatal_ParseErrors                                 , CFatal);
  (Fatal_ParseItError                                , CFatal);
  (Fatal_PolyTypeExpected                            , CFatal);
  (Fatal_PossibleInfiniteTyp                         , CFatal);
  (Fatal_PreModuleMismatch                           , CFatal);
  (Fatal_QulifierListNotPermitted                    , CFatal);
  (Fatal_RecursiveFunctionLiteral                    , CFatal);
  (Fatal_ReflectOnlySupportedOnEffects               , CFatal);
  (Fatal_ReservedPrefix                              , CFatal);
  (Fatal_SMTOutputParseError                         , CFatal);
  (Fatal_SMTSolverError                              , CFatal);
  (Fatal_SyntaxError                                 , CFatal);
  (Fatal_SynthByTacticError                          , CFatal);
  (Fatal_TacticGotStuck                              , CFatal);
  (Fatal_TcOneFragmentFailed                         , CFatal);
  (Fatal_TermOutsideOfDefLanguage                    , CFatal);
  (Fatal_ToManyArgumentToFunction                    , CFatal);
  (Fatal_TooManyOrTooFewFileMatch                    , CFatal);
  (Fatal_TooManyPatternArguments                     , CFatal);
  (Fatal_TooManyUniverse                             , CFatal);
  (Fatal_TypeMismatch                                , CFatal);
  (Fatal_TypeWithinPatternsAllowedOnVariablesOnly    , CFatal);
  (Fatal_UnableToReadFile                            , CFatal);
  (Fatal_UnepxectedOrUnboundOperator                 , CFatal);
  (Fatal_UnexpectedBinder                            , CFatal);
  (Fatal_UnexpectedBindShape                         , CFatal);
  (Fatal_UnexpectedChar                              , CFatal);
  (Fatal_UnexpectedComputationTypeForLetRec          , CFatal);
  (Fatal_UnexpectedConstructorType                   , CFatal);
  (Fatal_UnexpectedDataConstructor                   , CFatal);
  (Fatal_UnexpectedEffect                            , CFatal);
  (Fatal_UnexpectedEmptyRecord                       , CFatal);
  (Fatal_UnexpectedExpressionType                    , CFatal);
  (Fatal_UnexpectedFunctionParameterType             , CFatal);
  (Fatal_UnexpectedGeneralizedUniverse               , CFatal);
  (Fatal_UnexpectedGTotForLetRec                     , CFatal);
  (Fatal_UnexpectedGuard                             , CFatal);
  (Fatal_UnexpectedIdentifier                        , CFatal);
  (Fatal_UnexpectedImplicitArgument                  , CFatal);
  (Fatal_UnexpectedImplictArgument                   , CFatal);
  (Fatal_UnexpectedInductivetype                     , CFatal);
  (Fatal_UnexpectedLetBinding                        , CFatal);
  (Fatal_UnexpectedModuleDeclaration                 , CFatal);
  (Fatal_UnexpectedNumberOfUniverse                  , CFatal);
  (Fatal_UnexpectedNumericLiteral                    , CFatal);
  (Fatal_UnexpectedOperatorSymbol                    , CFatal);
  (Fatal_UnexpectedPattern                           , CFatal);
  (Fatal_UnexpectedPosition                          , CFatal);
  (Fatal_UnExpectedPreCondition                      , CFatal);
  (Fatal_UnexpectedReturnShape                       , CFatal);
  (Fatal_UnexpectedSignatureForMonad                 , CFatal);
  (Fatal_UnexpectedTerm                              , CFatal);
  (Fatal_UnexpectedTermInUniverse                    , CFatal);
  (Fatal_UnexpectedTermType                          , CFatal);
  (Fatal_UnexpectedTermVQuote                        , CFatal);
  (Fatal_UnexpectedUniversePolymorphicReturn         , CFatal);
  (Fatal_UnexpectedUniverseVariable                  , CFatal);
  (Fatal_UnfoldableDeprecated                        , CFatal);
  (Fatal_UnificationNotWellFormed                    , CFatal);
  (Fatal_Uninstantiated                              , CFatal);
  (Error_UninstantiatedUnificationVarInTactic        , CError);
  (Fatal_UninstantiatedVarInTactic                   , CFatal);
  (Fatal_UniverseMightContainSumOfTwoUnivVars        , CFatal);
  (Fatal_UniversePolymorphicInnerLetBound            , CFatal);
  (Fatal_UnknownAttribute                            , CFatal);
  (Fatal_UnknownToolForDep                           , CFatal);
  (Fatal_UnrecognizedExtension                       , CFatal);
  (Fatal_UnresolvedPatternVar                        , CFatal);
  (Fatal_UnsupportedConstant                         , CFatal);
  (Fatal_UnsupportedDisjuctivePatterns               , CFatal);
  (Fatal_UnsupportedQualifier                        , CFatal);
  (Fatal_UserTacticFailure                           , CFatal);
  (Fatal_ValueRestriction                            , CFatal);
  (Fatal_VariableNotFound                            , CFatal);
  (Fatal_WrongBodyTypeForReturnWP                    , CFatal);
  (Fatal_WrongDataAppHeadFormat                      , CFatal);
  (Fatal_WrongDefinitionOrder                        , CFatal);
  (Fatal_WrongResultTypeAfterConstrutor              , CFatal);
  (Fatal_WrongTerm                                   , CFatal);
  (Fatal_WhenClauseNotSupported                      , CFatal);
  (Unused01                                          , CFatal);
  (Warning_CallNotImplementedAsWarning               , CWarning);
  (Warning_AddImplicitAssumeNewQualifier             , CWarning);
  (Warning_AdmitWithoutDefinition                    , CWarning);
  (Warning_CachedFile                                , CWarning);
  (Warning_DefinitionNotTranslated                   , CWarning);
  (Warning_DependencyFound                           , CWarning);
  (Warning_DeprecatedEqualityOnBinder                , CWarning);
  (Warning_DeprecatedOpaqueQualifier                 , CWarning);
  (Warning_DocOverwrite                              , CWarning);
  (Warning_FileNotWritten                            , CWarning);
  (Warning_Filtered                                  , CWarning);
  (Warning_FunctionLiteralPrecisionLoss              , CWarning);
  (Warning_FunctionNotExtacted                       , CWarning);
  (Warning_HintFailedToReplayProof                   , CWarning);
  (Warning_HitReplayFailed                           , CWarning);
  (Warning_IDEIgnoreCodeGen                          , CWarning);
  (Warning_IllFormedGoal                             , CWarning);
  (Warning_InaccessibleArgument                      , CWarning);
  (Warning_IncoherentImplicitQualifier               , CWarning);
  (Warning_IrrelevantQualifierOnArgumentToReflect    , CWarning);
  (Warning_IrrelevantQualifierOnArgumentToReify      , CWarning);
  (Warning_MalformedWarnErrorList                    , CWarning);
  (Warning_MetaAlienNotATmUnknown                    , CWarning);
  (Warning_MultipleAscriptions                       , CWarning);
  (Warning_NondependentUserDefinedDataType           , CWarning);
  (Warning_NonListLiteralSMTPattern                  , CWarning);
  (Warning_NormalizationFailure                      , CWarning);
  (Warning_NotDependentArrow                         , CWarning);
  (Warning_NotEmbedded                               , CWarning);
  (Warning_PatternMissingBoundVar                    , CWarning);
  (Warning_RecursiveDependency                       , CWarning);
  (Warning_RedundantExplicitCurrying                 , CWarning);
  (Warning_SMTPatTDeprecated                         , CWarning);
  (Warning_SMTPatternMissingBoundVar                 , CWarning);
  (Warning_TopLevelEffect                            , CWarning);
  (Warning_UnboundModuleReference                    , CWarning);
  (Warning_UnexpectedFile                            , CWarning);
  (Warning_UnexpectedFsTypApp                        , CWarning);
  (Warning_UnexpectedZ3Output                        , CError);
  (Warning_UnprotectedTerm                           , CWarning);
  (Warning_UnrecognizedAttribute                     , CWarning);
  (Warning_UpperBoundCandidateAlreadyVisited         , CWarning);
  (Warning_UseDefaultEffect                          , CWarning);
  (Warning_WrongErrorLocation                        , CWarning);
  (Warning_Z3InvocationWarning                       , CWarning);
  (Warning_MissingInterfaceOrImplementation          , CWarning);
  (Warning_ConstructorBuildsUnexpectedType           , CWarning);
  (Warning_ModuleOrFileNotFoundWarning               , CWarning);
  (Error_NoLetMutable                                , CAlwaysError);
  (Error_BadImplicit                                 , CAlwaysError);
  (Warning_DeprecatedDefinition                      , CWarning);
  (Fatal_SMTEncodingArityMismatch                    , CFatal);
  (Warning_Defensive                                 , CWarning);
  (Warning_CantInspect                               , CWarning);
  (Warning_NilGivenExplicitArgs                      , CWarning);
  (Warning_ConsAppliedExplicitArgs                   , CWarning);
  (Warning_UnembedBinderKnot                         , CWarning);
  (Fatal_TacticProofRelevantGoal                     , CFatal);
  (Warning_TacAdmit                                  , CWarning);
  (Fatal_IncoherentPatterns                          , CFatal);
  (Error_NoSMTButNeeded                              , CAlwaysError);
  (Fatal_UnexpectedAntiquotation                     , CFatal);
  (Fatal_SplicedUndef                                , CFatal);
  (Fatal_SpliceUnembedFail                           , CFatal);
  (Warning_ExtractionUnexpectedEffect                , CWarning);
  (Error_DidNotFail                                  , CAlwaysError);
  (Warning_UnappliedFail                             , CWarning);
  (Warning_QuantifierWithoutPattern                  , CSilent);
  (Error_EmptyFailErrs                               , CAlwaysError);
  (Warning_logicqualifier                            , CWarning);
  (Fatal_CyclicDependence                            , CFatal);
  (Error_InductiveAnnotNotAType                      , CError);
  (Fatal_FriendInterface                             , CFatal);
  (Error_CannotRedefineConst                         , CError);
  (Error_BadClassDecl                                , CError);
  (* Protip: if we keep the semicolon at the end, we modify exactly one
   * line for each error we add. This means we get a cleaner git history/blame *)
  ]

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
    issue_range: option<Range.range>;
    issue_number: option<int>
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
        | EInfo -> "Info"
        | EWarning -> "Warning"
        | EError -> "Error"
        | ENotImplemented -> "Feature not yet implemented: " in
    let range_str, see_also_str =
        match issue.issue_range with
        | None -> "", ""
        | Some r when r = dummyRange -> "", ""
        | Some r ->
          (BU.format1 "%s: " (Range.string_of_use_range r),
           (if use_range r = def_range r then ""
            else BU.format1 " (see also %s)" (Range.string_of_range r))) in
    let issue_number =
        match issue.issue_number with
        | None -> ""
        | Some n -> BU.format1 " %s" (string_of_int n) in
    BU.format5 "%s(%s%s) %s%s\n" range_str level_header issue_number issue.issue_message see_also_str

let print_issue issue =
    let printer =
        match issue.issue_level with
        | EInfo -> BU.print_string
        | EWarning -> BU.print_warning
        | EError -> BU.print_error
        | ENotImplemented -> BU.print_error in
    printer (format_issue issue)

let compare_issues i1 i2 =
    match i1.issue_range, i2.issue_range with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some r1, Some r2 -> Range.compare_use_range r1 r2

let mk_default_handler print =
    let errs : ref<list<issue>> = BU.mk_ref [] in
    let add_one (e: issue) =
        match e.issue_level with
        | EError -> errs := e :: !errs
        | _ -> print_issue e in
    let count_errors () =
        List.length !errs in
    let report () =
        let sorted = List.sortWith compare_issues !errs in
        if print then
            List.iter print_issue sorted;
        sorted in
    let clear () =
        errs := [] in
    { eh_add_one = add_one;
      eh_count_errors = count_errors;
      eh_report = report;
      eh_clear = clear }

let default_handler = mk_default_handler true

let current_handler =
    BU.mk_ref default_handler

let mk_issue level range msg n =
    { issue_level = level; issue_range = range; issue_message = msg; issue_number = n}

let get_err_count () = (!current_handler).eh_count_errors ()

let wrapped_eh_add_one (h : error_handler) (issue : issue) : unit =
    h.eh_add_one issue;
    if issue.issue_level <> EInfo then begin
      Options.abort_counter := !Options.abort_counter - 1;
      if !Options.abort_counter = 0 then
        failwith "Aborting due to --abort_on"
    end

let add_one issue =
    atomically (fun () -> wrapped_eh_add_one (!current_handler) issue)

let add_many issues =
    atomically (fun () -> List.iter (wrapped_eh_add_one (!current_handler)) issues)

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

let findIndex l v = l |> List.index (function (e, _) when e=v -> true | _ -> false)
let errno_of_error e = findIndex default_flags e
let flags: ref<list<flag>> = mk_ref []

let init_warn_error_flags =
  let rec aux r l =
    match l with
    | [] -> r
    | (e, f)::tl -> aux (r@[f]) tl
  in
  flags := aux [] default_flags

let diag r msg =
  if Options.debug_any() then add_one (mk_issue EInfo (Some r) msg None)

let defensive_errno = errno_of_error Warning_Defensive
let lookup flags errno =
    if errno = defensive_errno && Options.defensive_fail ()
    then CAlwaysError
    else List.nth flags errno

let log_issue r (e, msg) =
  let errno = errno_of_error (e) in
  match lookup !flags errno with
  | CAlwaysError
  | CError ->
     add_one (mk_issue EError (Some r) msg (Some errno))
  | CWarning ->
     add_one (mk_issue EWarning (Some r) msg (Some errno))
  | CSilent -> ()
  // We allow using log_issue to report a Fatal error in interactive mode
  | CFatal ->
    let i = mk_issue EError (Some r) msg (Some errno) in
    if Options.ide()
    then add_one i
    else failwith ("don't use log_issue to report fatal error, should use raise_error: " ^format_issue i)

let add_errors errs =
    atomically (fun () -> List.iter (fun (e, msg, r) -> log_issue r (e, (message_prefix.append_prefix msg))) errs)

let issue_of_exn = function
    | Error(e, msg, r) ->
      let errno = errno_of_error (e) in
      Some (mk_issue EError (Some r) (message_prefix.append_prefix msg) (Some errno))
    | NYI msg ->
      Some (mk_issue ENotImplemented None (message_prefix.append_prefix msg) None)
    | Err (e, msg) ->
      let errno = errno_of_error (e) in
      Some (mk_issue EError None (message_prefix.append_prefix msg) (Some errno))
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

let update_flags l =
  let compare (_, (a, _)) (_, (b, _)) =
    if a > b then 1
    else if a < b then -1
    else 0
  in
  let set_one_flag f d =
    match (f, d) with
    | (CWarning, CAlwaysError) -> raise_err (Fatal_InvalidWarnErrorSetting, "cannot turn an error into warning")
    | (CError, CAlwaysError) -> raise_err (Fatal_InvalidWarnErrorSetting, "cannot turn an error into warning")
    | (CSilent, CAlwaysError) -> raise_err (Fatal_InvalidWarnErrorSetting, "cannot silence an error")
    | (_, CFatal) -> raise_err (Fatal_InvalidWarnErrorSetting, "cannot reset the error level of a fatal error")
    | _ -> f
  in
  let rec set_flag i l=
    let d = List.nth !flags i in
    match l with
    | [] -> d
    | (f, (l, h))::tl ->
      if (i>=l && i <= h) then set_one_flag f d
      else if (i<l) then d
      else set_flag i tl
  in
  let rec aux f i l sorted = match l with
    | [] -> f
    | hd::tl -> aux (f@[set_flag i sorted]) (i+1) tl sorted
  in
  let rec compute_range result l = match l with
    | [] -> result
    | (f, s)::tl ->
      let r = Util.split s ".." in
      let (l,h) = match r with
        | [r1; r2] -> (int_of_string r1, int_of_string r2)
        | _ -> raise_err (Fatal_InvalidWarnErrorSetting,
                          BU.format1 "Malformed warn-error range %s" s)
      in
      if (l < 0)  || (h >= List.length default_flags)
      then raise_err (Fatal_InvalidWarnErrorSetting,
                      BU.format2 "No error for warn_error %s..%s" (string_of_int l) (string_of_int h));
      compute_range (result@[(f, (l, h))]) tl
  in
  let range = compute_range [] l in
  let sorted = List.sortWith compare range in
  flags := aux [] 0 !flags sorted

let catch_errors (f : unit -> 'a) : list<issue> * option<'a> =
    let newh = mk_default_handler false in
    let old = !current_handler in
    current_handler := newh;
    let r = try let r = f () in Some r
            with | ex -> err_exn ex; None
    in
    let errs = newh.eh_report() in
    current_handler := old;
    errs, r
