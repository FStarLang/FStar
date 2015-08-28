FINE=../../bin/fine --z3timeout 60000 --fine_home ../.. --prims primsf7.f9 --prooflibvals noplv.f9 --f7 
all:acls

acls: acls.fs7 acls.fs
	$(FINE) $^

crypto: pi.fs7 data.fs7 prim-crypto.fs7 crypto.fs7 crypto.ml
	$(FINE) $^

principals: pi.fs7 db.fs7 data.fs7 prim-crypto.fs7 crypto.fs7 principals.fs7 principals.fs
	$(FINE) $^

cryptoPatterns: pi.fs7 db.fs7 data.fs7 prim-crypto.fs7 crypto.fs7 principals.fs7 cryptoPatterns.fs7
	$(FINE) $^

rpc: pi.fs7 db.fs7 data.fs7 prim-crypto.fs7 crypto.fs7 net.fs7 rpc.fs7 rpc.fs
	$(FINE) $^

asks: pi.fs7 data.fs7 prim-crypto.fs7 crypto.fs7 
	$(FINE) --profile $^

askmin: pi.fs7
	$(FINE) --logQueries $^

askmin2: pi.fs7 data-min.fs7 crypto-min.fs7
	$(FINE) --logQueries $^


commit: pi.fs7 data.fs7 db.fs7 prim-crypto.fs7 crypto.fs7 principals.fs7 global.fs7 sessions.fs7 Commit_protocol.fs7 
	$(FINE) $^
