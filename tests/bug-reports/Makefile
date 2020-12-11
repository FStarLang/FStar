FSTAR_HOME=../..
include $(FSTAR_HOME)/examples/Makefile.include
include $(FSTAR_HOME)/ulib/ml/Makefile.include

all: verify iverify not-verify extract

##################
# Positive tests #
##################

# These will be checked as part of the F* regressions.
SHOULD_VERIFY_CLOSED=Bug022.fst Bug024.fst Bug025.fst Bug026.fst Bug026b.fst Bug028.fst Bug046.fst Bug052.fst\
  Bug056.fst Bug058.fst Bug058b.fst Bug067.fst Bug069.fst Bug077.fst Bug097b.fst Bug102.fst Bug103.fst\
  Bug111.fst Bug116.fst Bug122.fst Bug124.fst Bug125.fst Bug126.fst Bug128.fst Bug138.fst Bug139.fst Bug152.fst\
  Bug155.fst Bug161.fst Bug162.fst Bug170.fst Bug173.fst Bug175.fst Bug178.fst Bug181.fst Bug184Eta.fst\
  Bug184.fst Bug185.fst Bug187.fst Bug190.fst Bug195.fst Bug195b.fst Bug209.fst Bug209b.fst Bug212.fst\
  Bug213.fst Bug215.fst Bug237b.fst Bug238.fst Bug244.fst Bug251.fst Bug252.fst Bug254.fst Bug256.fst\
  Bug257.fst Bug260.fst Bug264.fst Bug274.fst Bug275.fst Bug279.fst Bug281.fst Bug283.fst Bug290.fst Bug292.fst\
  Bug293.fst Bug311.fst Bug316.fst Bug363.fst Bug375.fst Bug397.fst Bug398.fst Bug399.fst Bug405.fst\
  Bug413.fst Bug416.fst Bug417.fst Bug422.fst Bug424.fst Bug433.fst Bug445.fst Bug463b.fst Bug482.fst Bug493.fst\
  Bug516.fst Bug516b.fst Bug517.fst Bug540.fst Bug552.fst Bug566.fst Bug574.fst Bug577.fst Bug579.fst Bug581.fst\
  Bug590.fst Bug601.fst Bug605.fst Bug609.fst Bug613.fst Bug686.fst Bug705.fst Bug706.fst Bug707.fst Bug709.fst\
  Bug710.fst Bug712.fst Bug713.fst Bug736.fst Bug765.fst Bug769c.fst Bug786.fst Bug836.fst Bug844.fst Bug985.fst \
	Bug989.fst\
  BugWildcardTelescopes.fst NormalizingGhostSubterms.fst UnificationCrash.fst Bug1150.fst Bug1076.fst\
  Bug1341.fst Bug1345.fst Bug1345b.fst Bug1345c.fst Bug1346.fst Bug1348.fst Bug1362.fst \
  Bug1347b.fst Bug1206.fst Bug1271.fst Bug1305.fst Bug1361.fst Bug1383.fst Bug1414.fst \
  unfold.fst Bug1091.fst Bug1449.fst Bug1427.fst Bug1423.fst Bug1352.fst Bug1123.fst ScopeOfBinderGuard.fst \
  Bug1319a.fst Bug1319b.fst Bug1319c.fst Bug1319d.fst Bug1319e.fst Bug1319f.fst Bug807a.fst Bug807b.fst Bug807c.fst Bug807d.fst Bug807e.fst \
  Bug1502.fst \
  Bug1488.fst Bug607.fst Bug466.fst Bug400.fst Bug1470.fst Bug1481.fst Bug1506.fst Bug606.fst Bug543.fst Bug1521.fst \
  Bug1533.fst Bug1535a.fst Bug1535b.fst Bug1536.fst Bug1370a.fst Bug1370b.fst Bug1534.fst Bug575.fst \
  Bug1443a.fst Bug1443b.fst Bug1443c.fst Bug1443d.fst Bug1443e.fst Bug1523.fst Bug1141a.fst Bug1141b.fst Bug1141c.fst Bug1141d.fst \
  Bug1561a.fst Bug1561b.fst Bug1065a.fst Bug1065b.fst Bug1065c.fst Bug1568.fst Bug1571.fst Bug1572.fst Bug1592.fst \
  Bug1595.fst Bug1601.fst Bug1602.fst Bug1604.fst Bug1605.fst Bug1621.fst Bug1680.fst Bug1682.fst Bug1694.fst \
  Bug1730b.fst Bug1612.fst Bug1614a.fst Bug1614b.fst Bug1614c.fst Bug1614d.fst Bug1614e.fst Bug1750.fst Bug1750.Aux.fst \
  Bug1622.fst Bug1540.fst Bug1784.fst Bug1802.fst Bug1055.fst Bug1818.fst Bug1640.fst Bug1243.fst Bug1841.fst \
  Bug1847.fst Bug1855.fst Bug1812.fst Bug1840.fst Bug1866.fst Bug811.fst Bug841.fst Bug1060.fst Bug1070.fst \
  Bug1130.fst Bug1170.fst Bug1191.fst Bug1799.fst Bug1900.fst Bug1908.fst Bug1913.fst BugLexTop.fst Bug1940a.fst \
  Bug1940b.fst Bug1940c.fst Bug1936.fst Bug1952a.fst Bug1952b.fst Bug1953.fst Bug1074.fst Bug442.fst Bug1954.fst \
  Bug1903.fst Bug1121a.fst Bug1121b.fst Bug1956.fst Bug1228.fst Bug829.fst Bug451.fst Bug1966a.fst Bug1966b.fst Bug1976.fst \
  Bug1986.fst Bug1995.fst Bug1507.fst Bug2001.fst Bug2004.fst Bug855a.fst Bug855b.fst Bug1097.fst Bug1918.fst Bug1390.fst Bug2031.fst \
  Bug379.fst Bug1182a.fst Bug1182b.fst Bug1901.fst Bug1902.fst Bug258.fst Bug2055.fst Bug2081.fst Bug2099.fst Bug2106.fst Bug2132.fst \
  Bug2138.fst Bug2146.fst Bug2074.fst Bug2125a.fst Bug2125b.fst Bug2167.fst Bug2169.fst Bug2169b.fst Bug2066.fst Bug2189.fst Bug2184.fst \
  Bug2193.fst

SHOULD_VERIFY_INTERFACE_CLOSED=Bug771.fsti Bug771b.fsti
SHOULD_VERIFY_AND_WARN_CLOSED=Bug016.fst

# These will not be checked, but the SHOULD_VERIFY_BROKEN examples are expected to work since their corresponding
# GitHub issue is closed. Consider re-opening.
SHOULD_VERIFY_BROKEN=Bug092.fst Bug170b.fst Bug192.fst Bug210.fst Bug210b.fst Bug210c.fst Bug312.fst\
  Bug818.fst Bug818b.fst
SHOULD_VERIFY_OPEN=Bug045.fst Bug057.fst Bug064.fst Bug065.fst Bug071.fst Bug121.fst Bug131.fst Bug171.fst\
  Bug171b.fst Bug171c.fst Bug259.fst Bug282.fst Bug291.fst Bug419.fst \
  Bug442b.fst Bug484.fst Bug542.fst Bug543.fst Bug554.fst Bug604.fst Bug606.fst\
  Bug626.fst Bug682.fst Bug715.fst Bug739.fst Bug815.fst Bug815b.fst Bug851.fst Bug933.fst Bug933b.fst\
  Bug1038.fst Bug1091.fst Bug807d.fst Bug1486.fst Bug1392.fst Bug1867.fst

# These examples go through but their corresponding GitHub issue is still open. Consider closing and adding them
# to SHOULD_VERIFY_CLOSED.
SHOULD_VERIFY_MAYBE_CLOSE=Bug121b.fst Bug351.fst Bug351b.fst Bug812.fst Bug853.fst Bug1042.fst Bug1360.fst

# These examples cannot be verified with the current version of F* because of problems unrelated to those
# described in their corresponding GitHub issue.
SHOULD_VERIFY_NOT_WORKING=Bug015.fst Bug021.fst Bug023.fst  Bug060.fst Bug062.fst Bug029.fst Bug096.fst Bug097a.fst\
  Bug100.fst Bug101.fst Bug111.fst Bug117.fst Bug148.fst Bug179.fst Bug184b.fst Bug185.fst Bug189.fst Bug203.fst\
  Bug237.fst Bug295.fst Bug377.fst Bug389.fst Bug422.fst Bug463a.fst Bug713.fst Bug974.fst \
  Bug1287.fst Bug1291.fst Bug1347.fst Bug2014.fst


##################
# Negative tests #
##################

# These will be checked as part of the F* regressions.
SHOULD_NOT_VERIFY_CLOSED=Bug035.fst Bug043.fst Bug044.fst Bug063.fst Bug120.fst Bug154.fst Bug154b.fst Bug154c.fst\
  Bug156.fst Bug163.fst Bug176.fst Bug177.fst Bug183.fst Bug250.fst Bug253.fst Bug253b.fst Bug262.fst Bug284.fst\
  Bug319.fst Bug320.fst Bug362.fst Bug406.fst Bug446.fst Bug612.fst Bug623.fst Bug655.fst\
  Bug769.fst Bug769b.fst Bug769d.fst Bug1017.fst Bug1043.fst Bug1043b.fst Bug1106.fst Bug1106b.fst Bug174.fst\
  Bug193.fst Bug208.fst Bug208.fst Bug378.fst Bug696.fst Bug1090.fst Bug1187.fst Bug380_1.fst Bug380_2.fst \
  Bug1404.fst Bug367.fst Bug1389a.fst Bug1389b.fst Bug1389c.fst Bug1441.fst Bug1029.fst Bug1029b.fst \
  Bug1863.fst

# These will not be checked, but the SHOULD_NOT_VERIFY_BROKEN examples are expected to work since their
# corresponding GitHub issue is closed. Consider re-opening.
SHOULD_NOT_VERIFY_BROKEN=
SHOULD_NOT_VERIFY_OPEN=Bug151.fst Bug1041.fst Bug1056.fst Bug1368.fst

# These examples go through but their corresponding GitHub issue is still open. Consider closing and adding them
# to SHOULD_NOT_VERIFY_CLOSED.
SHOULD_NOT_VERIFY_MAYBE_CLOSE=

# These examples cannot be verified with the current version of F* because of problems unrelated to those
# described in their corresponding GitHub issue.
SHOULD_NOT_VERIFY_NOT_WORKING=Bug186.fst Bug397b.fst


####################
# Extraction tests #
####################

# These will be checked as part of the F* regressions.
SHOULD_EXTRACT_CLOSED=Bug086.fst Bug314.fst Bug540.fst Bug541.fst Bug589.fst \
	ExtractionBug2.fst Bug1101.fst Bug1485.fst Bug734.fst Bug310.fst \
	Bug2058.fst RemoveUnusedTypars.B.fst RemoveUnusedTyparsIFace.B.fst \
	PushPopProjectors.fst
#ExtractionBug03.fst

# Bug1479.fst Crashes when in CI with "Error: Unbound module FStar_Tactics_Effect"


# These will not be checked, but the SHOULD_NOT_VERIFY_BROKEN examples are expected to work since their
# corresponding GitHub issue is closed. Consider re-opening.
SHOULD_EXTRACT_BROKEN=
SHOULD_EXTRACT_OPEN=

# These examples go through but their corresponding GitHub issue is still open. Consider closing and adding them
# to SHOULD_EXTRACT_CLOSED.
SHOULD_EXTRACT_MAYBE_CLOSE=

# These examples cannot be verified with the current version of F* because of problems unrelated to those
# described in their corresponding GitHub issue
SHOULD_EXTRACT_NOT_WORKING=Bug383.fst Bug450.fst Bug460.fst Bug490.fst


# To obtain module name from file name
CAPPED=$(subst Bug,Bug,$*)


%.verify: %.fst
	$(FSTAR) $^

Bug1383.verify: OTHERFLAGS += --warn_error @275 #Z3 warnings are fatal
Bug1694.verify: OTHERFLAGS += --codegen OCaml


verify: $(subst .fst,.verify,$(SHOULD_VERIFY_CLOSED))

%.iverify: %.fsti
	$(FSTAR) $^

iverify: $(subst .fsti,.iverify,$(SHOULD_VERIFY_INTERFACE_CLOSED))

verify-maybe-close: $(subst .fst,.verify,$(SHOULD_VERIFY_MAYBE_CLOSE))


%.not-verify: %.fst
	(! $(FSTAR) $^ >/dev/null 2>&1) || (echo "Negative test failed ($@)!" ; false)

not-verify: $(subst .fst,.not-verify,$(SHOULD_NOT_VERIFY_CLOSED))

Bug310.ml:
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --extract Bug310 --codegen OCaml Bug310.fst

Bug310.extract: Bug310.ml
	diff -u --strip-trailing-cr Bug310.ml Bug310.ml.expected

Bug2058.ml:
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --extract Bug2058 --codegen OCaml Bug2058.fst

Bug2058.extract: Bug2058.ml
	diff -u --strip-trailing-cr Bug2058.ml Bug2058.ml.expected

output-accept: Bug310.ml Bug2058.ml
	cp Bug310.ml Bug310.ml.expected
	cp Bug2058.ml Bug2058.ml.expected

RemoveUnusedTypars.B.extract: RemoveUnusedTypars.A.fst RemoveUnusedTypars.B.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --cache_checked_modules RemoveUnusedTypars.A.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --cache_checked_modules RemoveUnusedTypars.B.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --extract RemoveUnusedTypars.A --codegen FSharp RemoveUnusedTypars.A.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --extract RemoveUnusedTypars.B --codegen FSharp RemoveUnusedTypars.B.fst
	diff -u --strip-trailing-cr RemoveUnusedTypars_A.fs RemoveUnusedTypars_A.fs.expected
	diff -u --strip-trailing-cr RemoveUnusedTypars_B.fs RemoveUnusedTypars_B.fs.expected

RemoveUnusedTyparsIFace.B.extract: RemoveUnusedTyparsIFace.A.fst RemoveUnusedTyparsIFace.B.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --cache_checked_modules RemoveUnusedTyparsIFace.A.fsti --warn_error -333
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --cache_checked_modules RemoveUnusedTyparsIFace.A.fst --warn_error -333
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --cache_checked_modules RemoveUnusedTyparsIFace.B.fst --warn_error -333
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --extract RemoveUnusedTyparsIFace.A --codegen FSharp RemoveUnusedTyparsIFace.A.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --extract RemoveUnusedTyparsIFace.B --codegen FSharp RemoveUnusedTyparsIFace.B.fst
	diff -u --strip-trailing-cr RemoveUnusedTyparsIFace_A.fs RemoveUnusedTyparsIFace_A.fs.expected
	diff -u --strip-trailing-cr RemoveUnusedTyparsIFace_B.fs RemoveUnusedTyparsIFace_B.fs.expected

PushPopProjectors.extract: PushPopProjectors.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out_$* --codegen FSharp $^

output-accept: Bug310.ml Bug2058.ml
	cp Bug310.ml Bug310.ml.expected
	cp Bug2058.ml Bug2058.ml.expected

%.extract: %.fst
	mkdir -p out_$*
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --odir out_$* --codegen OCaml $^
	$(OCAMLOPT) out_$*/$(CAPPED).ml -o $(CAPPED).exe
	./$(CAPPED).exe

extract: $(subst .fst,.extract,$(SHOULD_EXTRACT_CLOSED))

clean:
	rm -rf out*
	rm -rf Bug*.exe
