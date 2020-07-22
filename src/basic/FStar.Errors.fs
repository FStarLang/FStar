#light "off"
module FStar.Errors
open FStar.String
open FStar.ST
open FStar.Exn
open FStar.All
open FStar.Util
open FStar.Range
open FStar.Options

(** This exception is raised in FStar.Error
    when a warn_error string could not be processed;
    The exception is handled in FStar.Options as part of
    option parsing. *)
exception Invalid_warn_error_setting of string

type error_flag =
  | CFatal          //CFatal: these are reported using a raise_error: compiler cannot progress
  | CAlwaysError    //CAlwaysError: these errors are reported using log_issue and cannot be suppressed
                    //the compiler can progress after reporting them
  | CError          //CError: these are reported as errors using log_issue
                    //        but they can be turned into warnings or silenced
  | CWarning        //CWarning: reported using log_issue as warnings by default;
                    //          then can be silenced or escalated to errors
  | CSilent         //CSilent: never the default for any issue, but warnings can be silenced

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
  | Warning_PatternMissingBoundVar  //AR: this is deprecated, use Warning_SMTPatternIllFormed instead
                                    //    not removing it so as not to mess up the error numbers
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

type flag = error_flag
type error_setting = raw_error * error_flag * int
let default_settings : list<error_setting> =
  [
    Error_DependencyAnalysisFailed                    , CAlwaysError, 0;
    Error_IDETooManyPops                              , CAlwaysError, 1;
    Error_IDEUnrecognized                             , CAlwaysError, 2;
    Error_InductiveTypeNotSatisfyPositivityCondition  , CAlwaysError, 3;
    Error_InvalidUniverseVar                          , CAlwaysError, 4;
    Error_MissingFileName                             , CAlwaysError, 5;
    Error_ModuleFileNameMismatch                      , CAlwaysError, 6;
    Error_OpPlusInUniverse                            , CAlwaysError, 7;
    Error_OutOfRange                                  , CAlwaysError, 8;
    Error_ProofObligationFailed                       , CError, 9;
    Error_TooManyFiles                                , CAlwaysError, 10;
    Error_TypeCheckerFailToProve                      , CAlwaysError, 11;
    Error_TypeError                                   , CAlwaysError, 12;
    Error_UncontrainedUnificationVar                  , CAlwaysError, 13;
    Error_UnexpectedGTotComputation                   , CAlwaysError, 14;
    Error_UnexpectedInstance                          , CAlwaysError, 15;
    Error_UnknownFatal_AssertionFailure               , CError, 16;
    Error_Z3InvocationError                           , CAlwaysError, 17;
    Error_IDEAssertionFailure                         , CAlwaysError, 18;
    Error_Z3SolverError                               , CError, 19;
    Fatal_AbstractTypeDeclarationInInterface          , CFatal, 20;
    Fatal_ActionMustHaveFunctionType                  , CFatal, 21;
    Fatal_AlreadyDefinedTopLevelDeclaration           , CFatal, 22;
    Fatal_ArgumentLengthMismatch                      , CFatal, 23;
    Fatal_AssertionFailure                            , CFatal, 24;
    Fatal_AssignToImmutableValues                     , CFatal, 25;
    Fatal_AssumeValInInterface                        , CFatal, 26;
    Fatal_BadlyInstantiatedSynthByTactic              , CFatal, 27;
    Fatal_BadSignatureShape                           , CFatal, 28;
    Fatal_BinderAndArgsLengthMismatch                 , CFatal, 29;
    Fatal_BothValAndLetInInterface                    , CFatal, 30;
    Fatal_CardinalityConstraintViolated               , CFatal, 31;
    Fatal_ComputationNotTotal                         , CFatal, 32;
    Fatal_ComputationTypeNotAllowed                   , CFatal, 33;
    Fatal_ComputedTypeNotMatchAnnotation              , CFatal, 34;
    Fatal_ConstructorArgLengthMismatch                , CFatal, 35;
    Fatal_ConstructorFailedCheck                      , CFatal, 36;
    Fatal_ConstructorNotFound                         , CFatal, 37;
    Fatal_ConstsructorBuildWrongType                  , CFatal, 38;
    Fatal_CycleInRecTypeAbbreviation                  , CFatal, 39;
    Fatal_DataContructorNotFound                      , CFatal, 40;
    Fatal_DefaultQualifierNotAllowedOnEffects         , CFatal, 41;
    Fatal_DefinitionNotFound                          , CFatal, 42;
    Fatal_DisjuctivePatternVarsMismatch               , CFatal, 43;
    Fatal_DivergentComputationCannotBeIncludedInTotal , CFatal, 44;
    Fatal_DuplicateInImplementation                   , CFatal, 45;
    Fatal_DuplicateModuleOrInterface                  , CFatal, 46;
    Fatal_DuplicateTopLevelNames                      , CFatal, 47;
    Fatal_DuplicateTypeAnnotationAndValDecl           , CFatal, 48;
    Fatal_EffectCannotBeReified                       , CFatal, 49;
    Fatal_EffectConstructorNotFullyApplied            , CFatal, 50;
    Fatal_EffectfulAndPureComputationMismatch         , CFatal, 51;
    Fatal_EffectNotFound                              , CFatal, 52;
    Fatal_EffectsCannotBeComposed                     , CFatal, 53;
    Fatal_ErrorInSolveDeferredConstraints             , CFatal, 54;
    Fatal_ErrorsReported                              , CFatal, 55;
    Fatal_EscapedBoundVar                             , CFatal, 56;
    Fatal_ExpectedArrowAnnotatedType                  , CFatal, 57;
    Fatal_ExpectedGhostExpression                     , CFatal, 58;
    Fatal_ExpectedPureExpression                      , CFatal, 59;
    Fatal_ExpectNormalizedEffect                      , CFatal, 60;
    Fatal_ExpectTermGotFunction                       , CFatal, 61;
    Fatal_ExpectTrivialPreCondition                   , CFatal, 62;
    Fatal_FailToExtractNativeTactic                   , CFatal, 63;
    Fatal_FailToCompileNativeTactic                   , CFatal, 64;
    Fatal_FailToProcessPragma                         , CFatal, 65;
    Fatal_FailToResolveImplicitArgument               , CFatal, 66;
    Fatal_FailToSolveUniverseInEquality               , CFatal, 67;
    Fatal_FieldsNotBelongToSameRecordType             , CFatal, 68;
    Fatal_ForbiddenReferenceToCurrentModule           , CFatal, 69;
    Fatal_FreeVariables                               , CFatal, 70;
    Fatal_FunctionTypeExpected                        , CFatal, 71;
    Fatal_IdentifierNotFound                          , CFatal, 72;
    Fatal_IllAppliedConstant                          , CFatal, 73;
    Fatal_IllegalCharInByteArray                      , CFatal, 74;
    Fatal_IllegalCharInOperatorName                   , CFatal, 75;
    Fatal_IllTyped                                    , CFatal, 76;
    Fatal_ImpossibleAbbrevLidBundle                   , CFatal, 77;
    Fatal_ImpossibleAbbrevRenameBundle                , CFatal, 78;
    Fatal_ImpossibleInductiveWithAbbrev               , CFatal, 79;
    Fatal_ImpossiblePrePostAbs                        , CFatal, 80;
    Fatal_ImpossiblePrePostArrow                      , CFatal, 81;
    Fatal_ImpossibleToGenerateDMEffect                , CFatal, 82;
    Fatal_ImpossibleTypeAbbrevBundle                  , CFatal, 83;
    Fatal_ImpossibleTypeAbbrevSigeltBundle            , CFatal, 84;
    Fatal_IncludeModuleNotPrepared                    , CFatal, 85;
    Fatal_IncoherentInlineUniverse                    , CFatal, 86;
    Fatal_IncompatibleKinds                           , CFatal, 87;
    Fatal_IncompatibleNumberOfTypes                   , CFatal, 88;
    Fatal_IncompatibleSetOfUniverse                   , CFatal, 89;
    Fatal_IncompatibleUniverse                        , CFatal, 90;
    Fatal_InconsistentImplicitArgumentAnnotation      , CFatal, 91;
    Fatal_InconsistentImplicitQualifier               , CFatal, 92;
    Fatal_InconsistentQualifierAnnotation             , CFatal, 93;
    Fatal_InferredTypeCauseVarEscape                  , CFatal, 94;
    Fatal_InlineRenamedAsUnfold                       , CFatal, 95;
    Fatal_InsufficientPatternArguments                , CFatal, 96;
    Fatal_InterfaceAlreadyProcessed                   , CFatal, 97;
    Fatal_InterfaceNotImplementedByModule             , CFatal, 98;
    Fatal_InterfaceWithTypeImplementation             , CFatal, 99;
    Fatal_InvalidFloatingPointNumber                  , CFatal, 100;
    Fatal_InvalidFSDocKeyword                         , CFatal, 101;
    Fatal_InvalidIdentifier                           , CFatal, 102;
    Fatal_InvalidLemmaArgument                        , CFatal, 103;
    Fatal_InvalidNumericLiteral                       , CFatal, 104;
    Fatal_InvalidRedefinitionOfLexT                   , CFatal, 105;
    Fatal_InvalidUnicodeInStringLiteral               , CFatal, 106;
    Fatal_InvalidUTF8Encoding                         , CFatal, 107;
    Fatal_InvalidWarnErrorSetting                     , CFatal, 108;
    Fatal_LetBoundMonadicMismatch                     , CFatal, 109;
    Fatal_LetMutableForVariablesOnly                  , CFatal, 110;
    Fatal_LetOpenModuleOnly                           , CFatal, 111;
    Fatal_LetRecArgumentMismatch                      , CFatal, 112;
    Fatal_MalformedActionDeclaration                  , CFatal, 113;
    Fatal_MismatchedPatternType                       , CFatal, 114;
    Fatal_MismatchUniversePolymorphic                 , CFatal, 115;
    Fatal_MissingDataConstructor                      , CFatal, 116;
    Fatal_MissingExposeInterfacesOption               , CFatal, 117;
    Fatal_MissingFieldInRecord                        , CFatal, 118;
    Fatal_MissingImplementation                       , CFatal, 119;
    Fatal_MissingImplicitArguments                    , CFatal, 120;
    Fatal_MissingInterface                            , CFatal, 121;
    Fatal_MissingNameInBinder                         , CFatal, 122;
    Fatal_MissingPrimsModule                          , CFatal, 123;
    Fatal_MissingQuantifierBinder                     , CFatal, 124;
    Fatal_ModuleExpected                              , CFatal, 125;
    Fatal_ModuleFileNotFound                          , CFatal, 126;
    Fatal_ModuleFirstStatement                        , CFatal, 127;
    Fatal_ModuleNotFound                              , CFatal, 128;
    Fatal_ModuleOrFileNotFound                        , CFatal, 129;
    Fatal_MonadAlreadyDefined                         , CFatal, 130;
    Fatal_MoreThanOneDeclaration                      , CFatal, 131;
    Fatal_MultipleLetBinding                          , CFatal, 132;
    Fatal_NameNotFound                                , CFatal, 133;
    Fatal_NameSpaceNotFound                           , CFatal, 134;
    Fatal_NegativeUniverseConstFatal_NotSupported     , CFatal, 135;
    Fatal_NoFileProvided                              , CFatal, 136;
    Fatal_NonInductiveInMutuallyDefinedType           , CFatal, 137;
    Fatal_NonLinearPatternNotPermitted                , CFatal, 138;
    Fatal_NonLinearPatternVars                        , CFatal, 139;
    Fatal_NonSingletonTopLevel                        , CFatal, 140;
    Fatal_NonSingletonTopLevelModule                  , CFatal, 141;
    Error_NonTopRecFunctionNotFullyEncoded            , CError, 142;
    Fatal_NonTrivialPreConditionInPrims               , CFatal, 143;
    Fatal_NonVariableInductiveTypeParameter           , CFatal, 144;
    Fatal_NotApplicationOrFv                          , CFatal, 145;
    Fatal_NotEnoughArgsToEffect                       , CFatal, 146;
    Fatal_NotEnoughArgumentsForEffect                 , CFatal, 147;
    Fatal_NotFunctionType                             , CFatal, 148;
    Fatal_NotSupported                                , CFatal, 149;
    Fatal_NotTopLevelModule                           , CFatal, 150;
    Fatal_NotValidFStarFile                           , CFatal, 151;
    Fatal_NotValidIncludeDirectory                    , CFatal, 152;
    Fatal_OneModulePerFile                            , CFatal, 153;
    Fatal_OpenGoalsInSynthesis                        , CFatal, 154;
    Fatal_OptionsNotCompatible                        , CFatal, 155;
    Fatal_OutOfOrder                                  , CFatal, 156;
    Fatal_ParseErrors                                 , CFatal, 157;
    Fatal_ParseItError                                , CFatal, 158;
    Fatal_PolyTypeExpected                            , CFatal, 159;
    Fatal_PossibleInfiniteTyp                         , CFatal, 160;
    Fatal_PreModuleMismatch                           , CFatal, 161;
    Fatal_QulifierListNotPermitted                    , CFatal, 162;
    Fatal_RecursiveFunctionLiteral                    , CFatal, 163;
    Fatal_ReflectOnlySupportedOnEffects               , CFatal, 164;
    Fatal_ReservedPrefix                              , CFatal, 165;
    Fatal_SMTOutputParseError                         , CFatal, 166;
    Fatal_SMTSolverError                              , CFatal, 167;
    Fatal_SyntaxError                                 , CFatal, 168;
    Fatal_SynthByTacticError                          , CFatal, 169;
    Fatal_TacticGotStuck                              , CFatal, 170;
    Fatal_TcOneFragmentFailed                         , CFatal, 171;
    Fatal_TermOutsideOfDefLanguage                    , CFatal, 172;
    Fatal_ToManyArgumentToFunction                    , CFatal, 173;
    Fatal_TooManyOrTooFewFileMatch                    , CFatal, 174;
    Fatal_TooManyPatternArguments                     , CFatal, 175;
    Fatal_TooManyUniverse                             , CFatal, 176;
    Fatal_TypeMismatch                                , CFatal, 177;
    Fatal_TypeWithinPatternsAllowedOnVariablesOnly    , CFatal, 178;
    Fatal_UnableToReadFile                            , CFatal, 179;
    Fatal_UnepxectedOrUnboundOperator                 , CFatal, 180;
    Fatal_UnexpectedBinder                            , CFatal, 181;
    Fatal_UnexpectedBindShape                         , CFatal, 182;
    Fatal_UnexpectedChar                              , CFatal, 183;
    Fatal_UnexpectedComputationTypeForLetRec          , CFatal, 184;
    Fatal_UnexpectedConstructorType                   , CFatal, 185;
    Fatal_UnexpectedDataConstructor                   , CFatal, 186;
    Fatal_UnexpectedEffect                            , CFatal, 187;
    Fatal_UnexpectedEmptyRecord                       , CFatal, 188;
    Fatal_UnexpectedExpressionType                    , CFatal, 189;
    Fatal_UnexpectedFunctionParameterType             , CFatal, 190;
    Fatal_UnexpectedGeneralizedUniverse               , CFatal, 191;
    Fatal_UnexpectedGTotForLetRec                     , CFatal, 192;
    Fatal_UnexpectedGuard                             , CFatal, 193;
    Fatal_UnexpectedIdentifier                        , CFatal, 194;
    Fatal_UnexpectedImplicitArgument                  , CFatal, 195;
    Fatal_UnexpectedImplictArgument                   , CFatal, 196;
    Fatal_UnexpectedInductivetype                     , CFatal, 197;
    Fatal_UnexpectedLetBinding                        , CFatal, 198;
    Fatal_UnexpectedModuleDeclaration                 , CFatal, 199;
    Fatal_UnexpectedNumberOfUniverse                  , CFatal, 200;
    Fatal_UnexpectedNumericLiteral                    , CFatal, 201;
    Fatal_UnexpectedOperatorSymbol                    , CFatal, 202;
    Fatal_UnexpectedPattern                           , CFatal, 203;
    Fatal_UnexpectedPosition                          , CFatal, 204;
    Fatal_UnExpectedPreCondition                      , CFatal, 205;
    Fatal_UnexpectedReturnShape                       , CFatal, 206;
    Fatal_UnexpectedSignatureForMonad                 , CFatal, 207;
    Fatal_UnexpectedTerm                              , CFatal, 208;
    Fatal_UnexpectedTermInUniverse                    , CFatal, 209;
    Fatal_UnexpectedTermType                          , CFatal, 210;
    Fatal_UnexpectedTermVQuote                        , CFatal, 211;
    Fatal_UnexpectedUniversePolymorphicReturn         , CFatal, 212;
    Fatal_UnexpectedUniverseVariable                  , CFatal, 213;
    Fatal_UnfoldableDeprecated                        , CFatal, 214;
    Fatal_UnificationNotWellFormed                    , CFatal, 215;
    Fatal_Uninstantiated                              , CFatal, 216;
    Error_UninstantiatedUnificationVarInTactic        , CError, 217;
    Fatal_UninstantiatedVarInTactic                   , CFatal, 218;
    Fatal_UniverseMightContainSumOfTwoUnivVars        , CFatal, 219;
    Fatal_UniversePolymorphicInnerLetBound            , CFatal, 220;
    Fatal_UnknownAttribute                            , CFatal, 221;
    Fatal_UnknownToolForDep                           , CFatal, 222;
    Fatal_UnrecognizedExtension                       , CFatal, 223;
    Fatal_UnresolvedPatternVar                        , CFatal, 224;
    Fatal_UnsupportedConstant                         , CFatal, 225;
    Fatal_UnsupportedDisjuctivePatterns               , CFatal, 226;
    Fatal_UnsupportedQualifier                        , CFatal, 227;
    Fatal_UserTacticFailure                           , CFatal, 228;
    Fatal_ValueRestriction                            , CFatal, 229;
    Fatal_VariableNotFound                            , CFatal, 230;
    Fatal_WrongBodyTypeForReturnWP                    , CFatal, 231;
    Fatal_WrongDataAppHeadFormat                      , CFatal, 232;
    Fatal_WrongDefinitionOrder                        , CFatal, 233;
    Fatal_WrongResultTypeAfterConstrutor              , CFatal, 234;
    Fatal_WrongTerm                                   , CFatal, 235;
    Fatal_WhenClauseNotSupported                      , CFatal, 236;
    Unused01                                          , CFatal, 237;
    Warning_PluginNotImplemented                      , CError, 238;
    Warning_AddImplicitAssumeNewQualifier             , CWarning, 239;
    Warning_AdmitWithoutDefinition                    , CWarning, 240;
    Warning_CachedFile                                , CWarning, 241;
    Warning_DefinitionNotTranslated                   , CWarning, 242;
    Warning_DependencyFound                           , CWarning, 243;
    Warning_DeprecatedEqualityOnBinder                , CWarning, 244;
    Warning_DeprecatedOpaqueQualifier                 , CWarning, 245;
    Warning_DocOverwrite                              , CWarning, 246;
    Warning_FileNotWritten                            , CWarning, 247;
    Warning_Filtered                                  , CWarning, 248;
    Warning_FunctionLiteralPrecisionLoss              , CWarning, 249;
    Warning_FunctionNotExtacted                       , CWarning, 250;
    Warning_HintFailedToReplayProof                   , CWarning, 251;
    Warning_HitReplayFailed                           , CWarning, 252;
    Warning_IDEIgnoreCodeGen                          , CWarning, 253;
    Warning_IllFormedGoal                             , CWarning, 254;
    Warning_InaccessibleArgument                      , CWarning, 255;
    Warning_IncoherentImplicitQualifier               , CWarning, 256;
    Warning_IrrelevantQualifierOnArgumentToReflect    , CWarning, 257;
    Warning_IrrelevantQualifierOnArgumentToReify      , CWarning, 258;
    Warning_MalformedWarnErrorList                    , CWarning, 259;
    Warning_MetaAlienNotATmUnknown                    , CWarning, 260;
    Warning_MultipleAscriptions                       , CWarning, 261;
    Warning_NondependentUserDefinedDataType           , CWarning, 262;
    Warning_NonListLiteralSMTPattern                  , CWarning, 263;
    Warning_NormalizationFailure                      , CWarning, 264;
    Warning_NotDependentArrow                         , CWarning, 265;
    Warning_NotEmbedded                               , CWarning, 266;
    Warning_PatternMissingBoundVar                    , CWarning, 267;
    Warning_RecursiveDependency                       , CWarning, 268;
    Warning_RedundantExplicitCurrying                 , CWarning, 269;
    Warning_SMTPatTDeprecated                         , CWarning, 270;
    Warning_SMTPatternIllFormed                       , CWarning, 271;
    Warning_TopLevelEffect                            , CWarning, 272;
    Warning_UnboundModuleReference                    , CWarning, 273;
    Warning_UnexpectedFile                            , CWarning, 274;
    Warning_UnexpectedFsTypApp                        , CWarning, 275;
    Warning_UnexpectedZ3Output                        , CError, 276;
    Warning_UnprotectedTerm                           , CWarning, 277;
    Warning_UnrecognizedAttribute                     , CWarning, 278;
    Warning_UpperBoundCandidateAlreadyVisited         , CWarning, 279;
    Warning_UseDefaultEffect                          , CWarning, 280;
    Warning_WrongErrorLocation                        , CWarning, 281;
    Warning_Z3InvocationWarning                       , CWarning, 282;
    Warning_MissingInterfaceOrImplementation          , CWarning, 283;
    Warning_ConstructorBuildsUnexpectedType           , CWarning, 284;
    Warning_ModuleOrFileNotFoundWarning               , CWarning, 285;
    Error_NoLetMutable                                , CAlwaysError, 286;
    Error_BadImplicit                                 , CAlwaysError, 287;
    Warning_DeprecatedDefinition                      , CWarning, 288;
    Fatal_SMTEncodingArityMismatch                    , CFatal, 289;
    Warning_Defensive                                 , CWarning, 290;
    Warning_CantInspect                               , CWarning, 291;
    Warning_NilGivenExplicitArgs                      , CWarning, 292;
    Warning_ConsAppliedExplicitArgs                   , CWarning, 293;
    Warning_UnembedBinderKnot                         , CWarning, 294;
    Fatal_TacticProofRelevantGoal                     , CFatal, 295;
    Warning_TacAdmit                                  , CWarning, 296;
    Fatal_IncoherentPatterns                          , CFatal, 297;
    Error_NoSMTButNeeded                              , CAlwaysError, 298;
    Fatal_UnexpectedAntiquotation                     , CFatal, 299;
    Fatal_SplicedUndef                                , CFatal, 300;
    Fatal_SpliceUnembedFail                           , CFatal, 301;
    Warning_ExtractionUnexpectedEffect                , CWarning, 302;
    Error_DidNotFail                                  , CAlwaysError, 303;
    Warning_UnappliedFail                             , CWarning, 304;
    Warning_QuantifierWithoutPattern                  , CSilent, 305;
    Error_EmptyFailErrs                               , CAlwaysError, 306;
    Warning_logicqualifier                            , CWarning, 307;
    Fatal_CyclicDependence                            , CFatal, 308;
    Error_InductiveAnnotNotAType                      , CError, 309;
    Fatal_FriendInterface                             , CFatal, 310;
    Error_CannotRedefineConst                         , CError, 311;
    Error_BadClassDecl                                , CError, 312;
    Error_BadInductiveParam                           , CFatal, 313;
    Error_FieldShadow                                 , CFatal, 314;
    Error_UnexpectedDM4FType                          , CFatal, 315;
    Fatal_EffectAbbreviationResultTypeMismatch        , CFatal, 316;
    Error_AlreadyCachedAssertionFailure               , CFatal, 317;
    Error_MustEraseMissing                            , CWarning, 318;
    Warning_EffectfulArgumentToErasedFunction         , CWarning, 319;
    Fatal_EmptySurfaceLet                             , CFatal, 320;
    Warning_UnexpectedCheckedFile                     , CWarning, 321;
    Fatal_ExtractionUnsupported                       , CFatal, 322;
    Warning_SMTErrorReason                            , CWarning, 323;
    Warning_CoercionNotFound                          , CWarning, 324;
    Error_QuakeFailed                                 , CError, 325;
    Error_IllSMTPat                                   , CError, 326;
    Error_IllScopedTerm                               , CError, 327;
    Warning_UnusedLetRec                              , CWarning, 328;
    Fatal_Effects_Ordering_Coherence                  , CError, 329;
    Warning_BleedingEdge_Feature                      , CWarning, 330;
    Warning_IgnoredBinding                            , CWarning, 331;
    Warning_CouldNotReadHints                         , CWarning, 333;
    Fatal_BadUvar                                     , CFatal,   334;
    Warning_WarnOnUse                                 , CSilent,  335;
    Warning_DeprecatedAttributeSyntax                 , CSilent,  336;
    Warning_DeprecatedGeneric                         , CWarning, 337;
    ]
module BU = FStar.Util

let lookup_error settings e =
  match
    BU.try_find (fun (v, _, i) -> e=v) settings
  with
  | Some i -> i
  | None -> failwith "Impossible: unrecognized error"

(** Find a (potentially empty) set of issues whose numbers
    are in the interval [l,h].

    Note: We intentionally do not warn on the use of non-existent
    issue number *)
let lookup_error_range settings (l, h) =
  let matches, _ =
    List.partition (fun (_, _, i) -> l <= i && i <= h) settings
  in
  matches

let error_number (_, _, i) = i

let warn_on_use_errno = error_number (lookup_error default_settings Warning_WarnOnUse)
let defensive_errno   = error_number (lookup_error default_settings Warning_Defensive)

let update_flags (l:list<(error_flag * string)>)
  : list<error_setting>
  = let set_one_flag i flag default_flag =
      match flag, default_flag with
      | (CWarning, CAlwaysError)
      | (CError, CAlwaysError) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot turn error %s into warning"
                             (BU.string_of_int i)))
      | (CSilent, CAlwaysError) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot silence error %s"
                             (BU.string_of_int i)))
      | (_, CFatal) ->
        raise (Invalid_warn_error_setting
                 (BU.format1 "cannot change the error level of fatal error %s"
                             (BU.string_of_int i)))
      | _ -> flag
   in
   let set_flag_for_range (flag, range) =
    let errs = lookup_error_range default_settings range in
    List.map (fun (v, default_flag, i) -> v, set_one_flag i flag default_flag, i) errs
   in
   let compute_range (flag, s) =
     let r = Util.split s ".." in
     let (l,h) =
         match r with
         | [r1; r2] -> (int_of_string r1, int_of_string r2)
         | _ -> raise (Invalid_warn_error_setting
                       (BU.format1 "Malformed warn-error range %s" s))
     in
     flag, (l, h)
  in
  let error_range_settings = List.map compute_range l in
  List.collect set_flag_for_range error_range_settings
  @ default_settings


type error = raw_error * string * Range.range

exception Err     of raw_error * string
exception Error   of error
exception Warning of error
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
        | Some r when r = dummyRange ->
            "", (if def_range r = def_range dummyRange then ""
                 else BU.format1 " (see also %s)" (Range.string_of_range r))
        | Some r ->
          (BU.format1 "%s: " (Range.string_of_use_range r),
           (if use_range r = def_range r || def_range r = def_range dummyRange
            then ""
            else BU.format1 " (see also %s)" (Range.string_of_range r)))
    in
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
    let issues : ref<list<issue>> = BU.mk_ref [] in
    let add_one (e: issue) =
        if Options.defensive_abort () && e.issue_number = Some defensive_errno then
          failwith "Aborting due to --defensive abort";
        match e.issue_level with
        | EInfo -> print_issue e
        | _ -> issues := e :: !issues
    in
    let count_errors () =
        List.fold_left (fun n i ->
          match i.issue_level with
          | EError -> n + 1
          | _ -> n)
          0
          (!issues)
    in
    let report () =
        let unique_issues = BU.remove_dups (fun i0 i1 -> i0=i1) !issues in
        let sorted_unique_issues = List.sortWith compare_issues unique_issues in
        if print then List.iter print_issue sorted_unique_issues;
        sorted_unique_issues
    in
    let clear () = issues := [] in
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
    push_prefix:    string -> unit;
    pop_prefix:     unit -> string;
    clear_prefixs:  unit -> unit;
    append_prefixs: string -> string;
}

let message_prefix =
    let pfxs = BU.mk_ref [] in
    let push_prefix s = pfxs := s :: !pfxs in
    let pop_prefix s =
        match !pfxs with
        | h::t -> (pfxs := t; h)
        | _ -> failwith "cannot pop error prefix..."
    in
    let clear_prefixs () = pfxs := [] in
    let append_prefixs s =
        List.fold_left (fun s p ->
          p ^ ":\n\t" ^ s)
          s
          !pfxs
    in
    { push_prefix    = push_prefix
    ; pop_prefix     = pop_prefix
    ; clear_prefixs  = clear_prefixs
    ; append_prefixs = append_prefixs
    }


let diag r msg =
  if Options.debug_any()
  then add_one (mk_issue EInfo (Some r) msg None)

let warn_unsafe_options rng_opt msg =
  match Options.report_assumes () with
  | Some "warn" ->
    add_one (mk_issue EWarning rng_opt ("Every use of this option triggers a warning: " ^msg) (Some warn_on_use_errno))
  | Some "error" ->
    add_one (mk_issue EError rng_opt ("Every use of this option triggers an error: " ^msg) (Some warn_on_use_errno))
  | _ -> ()

let set_option_warning_callback_range (ropt:option<Range.range>) =
    Options.set_option_warning_callback (warn_unsafe_options ropt)

let set_parse_warn_error,
    error_flags =
    (* To parse a warn_error string we expect a callback to be set in FStar.Main.setup_hooks *)
    let parser_callback : ref<option<(string -> list<error_setting>)>> = mk_ref None in
    (* The reporting of errors, particularly errors in the warn_error string itself
       is delicate.
       We keep a map from warn_error strings to their parsed results,
         - Some list<error_setting> in case it parses and is interpreted successfully
         - None in case it does not parse or is not intepretable
    *)
    let error_flags : BU.smap<(option<(list<error_setting>)>)> = BU.smap_create 10 in
    (* set_error_flags is called by Options.set_options, parse_cmd_line etc,
       upon parsing the options.
       It parses the current warn_error string and sets the result in the
       error_flags map above. In case it fails, it reports an Getopt error
       for Options to report. Options may, in turn, report that error
       back using the functionality of this module, e.g., log_issue *)
    let set_error_flags () =
        let parse (s:string) =
          match !parser_callback with
          | None -> failwith "Callback for parsing warn_error strings is not set"
          | Some f -> f s
        in
        let we = Options.warn_error () in
        try let r = parse we in
            BU.smap_add error_flags we (Some r);
            Getopt.Success
        with Invalid_warn_error_setting msg ->
            (BU.smap_add error_flags we None;
             Getopt.Error ("Invalid --warn_error setting: " ^msg))
    in
    (* get_error_flags is called when logging an issue to figure out
       which error level to report a particular issue at (Warning, Error etc.)
       It is important that this function itself never raises an exception:
       raising an error when trying to report an error is bad news, e.g., it
       crashes the ide mode since it causes F* to exit abruptly.
       So, we don't do any parsing here ... just look up the result of a
       prior parse, falling back to the default settings in case the
       parse didn't succeed *)
    let get_error_flags () =
      let we = Options.warn_error () in
      match BU.smap_try_find error_flags we with
      | Some (Some w) -> w
      | _ -> default_settings
    in
    (* Setting the parser callback received from setup_hooks
       and installing, in turn, callbacks in Options for
       parsing warn_error settings and also for warning on the use of
       unsafe options. *)
    let set_callbacks (f:string -> list<error_setting>) =
        parser_callback := Some f;
        Options.set_error_flags_callback set_error_flags;
        Options.set_option_warning_callback (warn_unsafe_options None)
    in
    set_callbacks, get_error_flags

let lookup err =
  let flags = error_flags () in
  let v, level, i = lookup_error flags err in
  let with_level level = v, level, i in
  match v with
  | Warning_Defensive when Options.defensive_error () || Options.defensive_abort () ->
    with_level CAlwaysError

  | Warning_WarnOnUse ->
    let level' =
      //the level of warn_on_use is the
      //max severity of the report_assumes setting (none, warn, error)
      //and whatever the level is by default (e.g., due to a --warn_error setting)
      match Options.report_assumes () with
      | None -> level
      | Some "warn" ->
        (match level with
         | CSilent -> CWarning
         | _ -> level)
      | Some "error" ->
        (match level with
         | CWarning
         | CSilent -> CError
         | _ -> level)
      | Some _ ->
        level
    in
    with_level level'

  | _ ->
    with_level level

let log_issue r (e, msg) =
  match lookup e with
  | (_, CAlwaysError, errno)
  | (_, CError, errno)  ->
     add_one (mk_issue EError (Some r) msg (Some errno))
  | (_, CWarning, errno) ->
     add_one (mk_issue EWarning (Some r) msg (Some errno))
  | (_, CSilent, _) -> ()
  // We allow using log_issue to report a Fatal error in interactive mode
  | (_, CFatal, errno) ->
    let i = mk_issue EError (Some r) msg (Some errno) in
    if Options.ide()
    then add_one i
    else failwith ("don't use log_issue to report fatal error, should use raise_error: " ^format_issue i)

let add_errors errs =
    atomically (fun () -> List.iter (fun (e, msg, r) -> log_issue r (e, (message_prefix.append_prefixs msg))) errs)

let issue_of_exn = function
    | Error(e, msg, r) ->
      let errno = error_number (lookup e) in
      Some (mk_issue EError (Some r) (message_prefix.append_prefixs msg) (Some errno))
    | Err (e, msg) ->
      let errno = error_number (lookup e) in
      Some (mk_issue EError None (message_prefix.append_prefixs msg) (Some errno))
    | _ -> None

let err_exn exn =
    if exn = Stop then ()
    else
    match issue_of_exn exn with
    | Some issue -> add_one issue
    | None -> raise exn

let handleable = function
  | Error _
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

let catch_errors (f : unit -> 'a) : list<issue> * option<'a> =
    let newh = mk_default_handler false in
    let old = !current_handler in
    current_handler := newh;
    let r = try let r = f () in Some r
            with | ex -> err_exn ex; None
    in
    let all_issues = newh.eh_report() in //de-duplicated already
    current_handler := old;
    let errs, rest = List.partition (fun i -> i.issue_level = EError) all_issues in
    List.iter old.eh_add_one rest; //add the remaining issues back to the outer handler to be reported as usual
    errs, r

(* Finds a discrepancy between two multisets of ints. Result is (elem, amount1, amount2)
 * eg. find_multiset_discrepancy [1;1;3;5] [1;1;3;3;4;5] = Some (3, 1, 2)
 *     since 3 appears 1 time in l1, but 2 times in l2. *)
let find_multiset_discrepancy (l1 : list<int>) (l2 : list<int>) : option<(int * int * int)> =
    let sort = List.sortWith (fun x y -> x - y) in
    let rec collect (l : list<'a>) : list<('a * int)> =
        match l with
        | [] -> []
        | hd :: tl ->
            begin match collect tl with
            | [] -> [(hd, 1)]
            | (h, n) :: t ->
                if h = hd
                then (h, n+1) :: t
                else (hd, 1) :: (h, n) :: t
            end
    in
    let summ l =
        collect l
    in
    let l1 = summ (sort l1) in
    let l2 = summ (sort l2) in
    let rec aux l1 l2 =
        match l1, l2 with
        | [], [] -> None

        | (e, n) :: _, [] ->
            Some (e, n, 0)

        | [], (e, n) :: _ ->
            Some (e, 0, n)

        | (hd1, n1) :: tl1, (hd2, n2) :: tl2 ->
            if hd1 < hd2 then
                Some (hd1, n1, 0)
            else if hd1 > hd2 then
                Some (hd2, 0, n2)
            else if n1 <> n2 then
                Some (hd1, n1, n2)
            else aux tl1 tl2
    in
    aux l1 l2
