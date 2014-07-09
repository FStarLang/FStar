TRACE=
ifeq ($(TRACE), true)
override OTHERFLAGS += --trace_error --prn
endif
PRN=
ifeq ($(PRN), true)
override OTHERFLAGS += --prn
endif

FSTAR=mono ../../bin/FStar.exe --fstar_home ../../ $(OTHERFLAGS)

ALLFILES=utils list tuple rec pat letrec termination skel 

prims: 
	$(FSTAR) --pretype --prims prims.fst 

utils:
	$(FSTAR) --pretype --codegen OCaml --prims prims.fst utils.fst

list:
	$(FSTAR) --pretype --codegen OCaml  --prims prims.fst list.fst


STDFILES=list.fst string.fst
BASICFILES=bytes.fst util.fst getoptsimple.fst options.fs range.fst unionfind.fst
BASIC=$(addprefix ../../src/basic/, $(BASICFILES))
SYNTAXFILES=syntax.fs const.fs visit.fs util.fs print.fs
SYNTAX=$(addprefix ../../src/absyn/, $(SYNTAXFILES))
PARSERFILES=ast.fs dsenv.fsi dsenv.fs desugar.fsi desugar.fs parse.fst lexhelp.fs parseit.fst driver.fs 
PARSER=$(addprefix ../../src/parser/, $(PARSERFILES))
TCFILES=errors.fs tcenv.fsi tcenv.fs normalize.fsi normalize.fs rel.fsi rel.fs tcutil.fsi tcutil.fs tc.fs
TC=$(addprefix ../../src/tc/, $(TCFILES))
MAINFILES=fstar.fs
MAIN=$(addprefix ../../src/, $(MAINFILES))
ALL=prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC) $(MAIN)

pt-compiler:
	$(FSTAR) --pretype --prims prims.fst st.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) $(TC)

compiler:
	$(FSTAR) --prims prims.fst $(STDFILES) $(BASIC) $(SYNTAX) $(PARSER) backends.fsi $(MAIN)


wc: $(ALL)

# # Change the following line to the location of the top MITLS directory "lang-sec/msrc/cvk/samples/protocols/tls"
MITLS=./mitls-copy/

PDIR=$(MITLS)Platform/
PLATFORM=$(PDIR)Bytes.fsi $(PDIR)Date.fsi $(PDIR)Error.fsi $(PDIR)List.fsi $(PDIR)Tcp.fsi

CDIR=$(MITLS)CoreCrypto/
CRYPTO=$(CDIR)CoreKeys.fsi $(CDIR)CoreACiphers.fsi $(CDIR)CoreHMac.fsi $(CDIR)CoreRandom.fsi $(CDIR)CoreCiphers.fsi $(CDIR)CoreHash.fsi $(CDIR)CoreSig.fsi $(CDIR)CoreDH.fsi $(CDIR)DER.fsi

TDIR=$(MITLS)lib/
TLSI=$(TDIR)TLSError.fsi $(TDIR)Nonce.fsi $(TDIR)TLSConstants.fsi $(TDIR)RSAKey.fsi $(TDIR)DHGroup.fsi $(TDIR)PMS.fsi $(TDIR)HASH.fsi $(TDIR)HMAC.fsi $(TDIR)Sig.fsi $(TDIR)Cert.fsi $(TDIR)TLSInfo.fsi $(TDIR)TLSExtensions.fsi $(TDIR)TLSPRF.fsi $(TDIR)Range.fsi $(TDIR)DataStream.fsi $(TDIR)AppFragment.fsi $(TDIR)HSFragment.fsi $(TDIR)TLSFragment.fsi $(TDIR)StatefulPlain.fsi $(TDIR)LHAEPlain.fsi $(TDIR)MAC_SHA256.fsi $(TDIR)MAC_SHA1.fsi $(TDIR)MAC.fsi $(TDIR)Encode.fsi $(TDIR)ENC.fsi $(TDIR)AEAD_GCM.fsi $(TDIR)LHAE.fsi $(TDIR)StatefulLHAE.fsi $(TDIR)Record.fsi $(TDIR)Alert.fsi $(TDIR)PRF.fsi $(TDIR)KEF.fsi $(TDIR)DH.fsi $(TDIR)RSA.fsi $(TDIR)SessionDB.fsi $(TDIR)Handshake.fsi $(TDIR)AppData.fsi $(TDIR)Dispatch.fsi $(TDIR)TLS.fsi 

TLS=$(TDIR)TLSError.fs $(TDIR)Nonce.fs $(TDIR)TLSConstants.fs $(TDIR)RSAKey.fs $(TDIR)DHGroup.fs $(TDIR)PMS.fs $(TDIR)HASH.fs $(TDIR)HMAC.fs $(TDIR)Sig.fs $(TDIR)Cert.fsi $(TDIR)TLSInfo.fs $(TDIR)TLSExtensions.fs #$(TDIR)TLSPRF.fs $(TDIR)Range.fs $(TDIR)DataStream.fs $(TDIR)AppFragment.fs $(TDIR)HSFragment.fs $(TDIR)TLSFragment.fs $(TDIR)StatefulPlain.fs $(TDIR)LHAEPlain.fs $(TDIR)MAC_SHA256.fs $(TDIR)MAC_SHA1.fs $(TDIR)MAC.fs $(TDIR)Encode.fs $(TDIR)ENC.fs $(TDIR)AEAD_GCM.fs $(TDIR)LHAE.fs $(TDIR)StatefulLHAE.fs $(TDIR)Record.fs $(TDIR)Alert.fs $(TDIR)PRF.fs $(TDIR)KEF.fs $(TDIR)DH.fs $(TDIR)RSA.fs $(TDIR)SessionDB.fsi # $(TDIR)HandshakeMessages.fs $(TDIR)Handshake.fs $(TDIR)AppData.fs $(TDIR)Dispatch.fs $(TDIR)TLS.fs $(TDIR)TLS.fs

mitls:
	$(FSTAR) --pretype --codegen OCaml --prims prims.fst st.fst array.fst $(PLATFORM) $(CRYPTO) $(TLS)


wc: prims.fst $(ALL)
	wc -l $^

clean:
	rm *~ 
