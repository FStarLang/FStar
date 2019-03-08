FSTAR_HOME=../..
include ../Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: verify iverify not-verify extract


##################
# Positive tests #
##################

# These will be checked as part of the F* regressions.
SHOULD_VERIFY_CLOSED=bug022.fst bug024.fst bug025.fst bug026.fst bug026b.fst bug028.fst bug046.fst bug052.fst\
  bug056.fst bug058.fst bug058b.fst bug067.fst bug069.fst bug077.fst bug097b.fst bug102.fst bug103.fst\
  bug111.fst bug116.fst bug122.fst bug124.fst bug125.fst bug126.fst bug128.fst bug138.fst bug139.fst bug152.fst\
  bug155.fst bug161.fst bug162.fst bug170.fst bug173.fst bug175.fst bug178.fst bug181.fst bug184Eta.fst\
  bug184.fst bug185.fst bug187.fst bug190.fst bug195.fst bug195b.fst bug209.fst bug209b.fst bug212.fst\
  bug213.fst bug215.fst bug237b.fst bug238.fst bug244.fst bug251.fst bug252.fst bug254.fst bug256.fst\
  bug257.fst bug260.fst bug264.fst bug274.fst bug275.fst bug279.fst bug281.fst bug283.fst bug290.fst bug292.fst\
  bug293.fst bug311.fst bug316.fst bug363.fst bug375.fst bug397.fst bug398.fst bug399.fst bug405.fst\
  bug413.fst bug416.fst bug417.fst bug422.fst bug424.fst bug433.fst bug445.fst bug463b.fst bug482.fst bug493.fst\
  bug516.fst bug516b.fst bug517.fst bug540.fst bug552.fst bug566.fst bug574.fst bug577.fst bug579.fst bug581.fst\
  bug590.fst bug601.fst bug605.fst bug609.fst bug613.fst bug686.fst bug705.fst bug706.fst bug707.fst bug709.fst\
  bug710.fst bug712.fst bug713.fst bug736.fst bug765.fst bug769c.fst bug786.fst bug836.fst bug844.fst bug985.fst \
	bug989.fst\
  BugWildcardTelescopes.fst NormalizingGhostSubterms.fst UnificationCrash.fst bug1150.fst bug1076.fst\
  bug1121.fst bug1341.fst bug1345.fst bug1345b.fst bug1345c.fst bug1346.fst bug1348.fst bug1362.fst \
  bug1347b.fst bug1206.fst bug1271.fst bug1305.fst bug1361.fst bug1383.fst bug1414.fst \
  unfold.fst bug1091.fst BugUnfoldAbstractEquational.fst Bug1449.fst Bug1427.fst Bug1423.fst Bug1352.fst Bug1123.fst ScopeOfBinderGuard.fst \
  bug1319a.fst bug1319b.fst bug1319c.fst bug1319d.fst bug1319e.fst bug1319f.fst bug807a.fst bug807b.fst bug807c.fst bug807d.fst bug807e.fst \
  Bug1502.fst \
  Bug1488.fst bug607.fst bug466.fst bug400.fst bug1470.fst bug1481.fst Bug1506.fst bug606.fst bug543.fst bug1521.fst \
  Bug1533.fst bug1535a.fst bug1535b.fst Bug1536.fst bug1370a.fst bug1370b.fst bug1534.fst bug575.fst \
  bug1443a.fst bug1443b.fst bug1443c.fst bug1443d.fst bug1443e.fst bug1523.fst bug1141a.fst bug1141b.fst bug1141c.fst bug1141d.fst \
  bug1561a.fst bug1561b.fst bug1065a.fst bug1065b.fst bug1065c.fst bug1568.fst Bug1571.fst Bug1572.fst Bug1592.fst \
  Bug1595.fst Bug1601.fst Bug1602.fst Bug1604.fst Bug1605.fst Bug1621.fst Bug1680.fst

SHOULD_VERIFY_INTERFACE_CLOSED=bug771.fsti bug771b.fsti
SHOULD_VERIFY_AND_WARN_CLOSED=bug016.fst

# These will not be checked, but the SHOULD_VERIFY_BROKEN examples are expected to work since their corresponding
# GitHub issue is closed. Consider re-opening.
SHOULD_VERIFY_BROKEN=bug092.fst bug170b.fst bug192.fst bug210.fst bug210b.fst bug210c.fst bug312.fst\
  bug818.fst bug818b.fst
SHOULD_VERIFY_OPEN=bug045.fst bug057.fst bug064.fst bug065.fst bug071.fst bug121.fst bug131.fst bug171.fst\
  bug171b.fst bug171c.fst bug258.fst bug259.fst bug282.fst bug291.fst bug419.fst bug442.fst\
  bug442b.fst bug484.fst bug542.fst bug543.fst bug554.fst bug604.fst bug606.fst\
  bug626.fst bug682.fst bug715.fst bug739.fst bug815.fst bug815b.fst bug851.fst bug933.fst bug933b.fst\
  bug1038.fst bug1055b.fst bug1091.fst bug1390.fst bug807d.fst bug1486.fst bug1392.fst

# These examples go through but their corresponding GitHub issue is still open. Consider closing and adding them
# to SHOULD_VERIFY_CLOSED.
SHOULD_VERIFY_MAYBE_CLOSE=bug121b.fst bug351.fst bug351b.fst bug812.fst bug853.fst bug1042.fst bug1360.fst

# These examples cannot be verified with the current version of F* because of problems unrelated to those
# described in their corresponding GitHub issue.
SHOULD_VERIFY_NOT_WORKING=bug015.fst bug021.fst bug023.fst  bug060.fst bug062.fst bug029.fst bug096.fst bug097a.fst\
  bug100.fst bug101.fst bug111.fst bug117.fst bug148.fst bug179.fst bug184b.fst bug185.fst bug189.fst bug203.fst\
  bug237.fst bug295.fst bug377.fst bug389.fst bug422.fst bug463a.fst bug713.fst bug974.fst \
  bug1287.fst bug1291.fst bug1347.fst


##################
# Negative tests #
##################

# These will be checked as part of the F* regressions.
SHOULD_NOT_VERIFY_CLOSED=bug035.fst bug043.fst bug044.fst bug063.fst bug120.fst bug154.fst bug154b.fst bug154c.fst\
  bug156.fst bug163.fst bug176.fst bug177.fst bug183.fst bug250.fst bug253.fst bug253b.fst bug262.fst bug284.fst\
  bug319.fst bug320.fst bug362.fst bug379.fst bug406.fst bug446.fst bug612.fst bug623.fst bug655.fst\
  bug769.fst bug769b.fst bug769d.fst bug1017.fst bug1043.fst bug1043b.fst bug1106.fst bug1106b.fst bug174.fst\
  bug193.fst bug208.fst bug208.fst bug378.fst bug696.fst bug1090.fst bug1187.fst bug380_1.fst bug380_2.fst \
  bug1404.fst bug367.fst bug1389a.fst bug1389b.fst bug1389c.fst Bug1441.fst bug1029.fst bug1029b.fst

# These will not be checked, but the SHOULD_NOT_VERIFY_BROKEN examples are expected to work since their
# corresponding GitHub issue is closed. Consider re-opening.
SHOULD_NOT_VERIFY_BROKEN=
SHOULD_NOT_VERIFY_OPEN=bug151.fst bug1041.fst bug1056.fst bug1368.fst

# These examples go through but their corresponding GitHub issue is still open. Consider closing and adding them
# to SHOULD_NOT_VERIFY_CLOSED.
SHOULD_NOT_VERIFY_MAYBE_CLOSE=

# These examples cannot be verified with the current version of F* because of problems unrelated to those
# described in their corresponding GitHub issue.
SHOULD_NOT_VERIFY_NOT_WORKING=bug186.fst bug397b.fst


####################
# Extraction tests #
####################

# These will be checked as part of the F* regressions.
SHOULD_EXTRACT_CLOSED=bug086.fst bug314.fst bug540.fst bug541.fst bug589.fst ExtractionBug2.fst bug1101.fst bug1485.fst bug734.fst
#ExtractionBug03.fst

# bug1479.fst Crashes when in CI with "Error: Unbound module FStar_Tactics_Effect"


# These will not be checked, but the SHOULD_NOT_VERIFY_BROKEN examples are expected to work since their
# corresponding GitHub issue is closed. Consider re-opening.
SHOULD_EXTRACT_BROKEN=
SHOULD_EXTRACT_OPEN=

# These examples go through but their corresponding GitHub issue is still open. Consider closing and adding them
# to SHOULD_EXTRACT_CLOSED.
SHOULD_EXTRACT_MAYBE_CLOSE=

# These examples cannot be verified with the current version of F* because of problems unrelated to those
# described in their corresponding GitHub issue
SHOULD_EXTRACT_NOT_WORKING=bug383.fst bug450.fst bug460.fst bug490.fst


# To obtain module name from file name
CAPPED=$(subst bug,Bug,$*)


%.verify: %.fst
	$(FSTAR) $^

bug1383.verify: OTHERFLAGS += --warn_error @275 #Z3 warnings are fatal
verify: $(subst .fst,.verify,$(SHOULD_VERIFY_CLOSED))

%.iverify: %.fsti
	$(FSTAR) $^

iverify: $(subst .fsti,.iverify,$(SHOULD_VERIFY_INTERFACE_CLOSED))

verify-maybe-close: $(subst .fst,.verify,$(SHOULD_VERIFY_MAYBE_CLOSE))


%.not-verify: %.fst
	(! $(FSTAR) $^ >/dev/null 2>&1) || (echo "Negative test failed ($@)!" ; false)

not-verify: $(subst .fst,.not-verify,$(SHOULD_NOT_VERIFY_CLOSED))

%.extract: %.fst
	mkdir -p out_$*
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out_$* --codegen OCaml $^
	$(OCAMLOPT) out_$*/$(CAPPED).ml -o $(CAPPED).exe
	./$(CAPPED).exe

extract: $(subst .fst,.extract,$(SHOULD_EXTRACT_CLOSED))

clean:
	rm -rf out*
	rm -rf Bug*.exe
