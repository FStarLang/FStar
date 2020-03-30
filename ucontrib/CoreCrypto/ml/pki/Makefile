# -*- Makefile -*-

# --------------------------------------------------------------------
# Available modes: rsa, dsa, ecdsa
MODE ?= rsa

# --------------------------------------------------------------------
C  = CC
ST = State
L  = Location
O  = Organization
OU = 
CN = mitls.org
EA = root@mitls.org

# --------------------------------------------------------------------
export PKI := $(CURDIR)/$(MODE)

CASUBJECT=/C=$(C)/ST=$(ST)/L=$(L)/O=$(O)/OU=$(OU)/CN=$(MODE).$(CN)/emailAddress=$(EA)

# --------------------------------------------------------------------
uname_S := $(shell sh -c 'uname -s 2>/dev/null || echo not')
uname_M := $(shell sh -c 'uname -m 2>/dev/null || echo not')
uname_O := $(shell sh -c 'uname -o 2>/dev/null || echo not')
uname_R := $(shell sh -c 'uname -r 2>/dev/null || echo not')
uname_P := $(shell sh -c 'uname -p 2>/dev/null || echo not')
uname_V := $(shell sh -c 'uname -v 2>/dev/null || echo not')

# --------------------------------------------------------------------
define layout
	if [ ! -d $(PKI) ]; then \
	    mkdir -p $(PKI);     \
	fi

	if [ ! -d $(PKI)/db ]; then             \
		mkdir $(PKI)/db;                    \
		mkdir $(PKI)/db/ca.db.certs;        \
		touch $(PKI)/db/ca.db.serial;       \
		touch $(PKI)/db/ca.db.index;        \
		echo '01' > $(PKI)/db/ca.db.serial; \
	fi

	if [ ! -d $(PKI)/certificates ]; then \
		mkdir $(PKI)/certificates;        \
	fi
endef

# --------------------------------------------------------------------
.PHONY: ca dh dsap layout clean hash
.PHONY: cert!% 

.PRECIOUS: $(MODE)/certificates/%.p12
.PRECIOUS: $(MODE)/certificates/%.key
.PRECIOUS: $(MODE)/certificates/%.crt
.PRECIOUS: $(MODE)/certificates/%.csr
.PRECIOUS: $(MODE)/certificates/ca.key
.PRECIOUS: $(MODE)/certificates/ca.crt

# --------------------------------------------------------------------
all:
	@echo "No default rule" >&2

# --------------------------------------------------------------------
cert!%: $(MODE)/certificates/%.p12
	@true

# --------------------------------------------------------------------
ca: layout $(MODE)/certificates/ca.crt

$(MODE)/certificates/ca.crt: $(MODE)/certificates/ca.key
	openssl req -new -x509 -batch          \
	    -subj   "$(CASUBJECT)"             \
	    -config $(CURDIR)/config/ca.config \
	    -key    $<                         \
	    -out    $@
	openssl x509 -in $@ -noout -text

# --------------------------------------------------------------------
dh: layout $(MODE)/certificates/dh.pem

$(MODE)/certificates/dh.pem:
	openssl dhparam -out $@ 1024

# --------------------------------------------------------------------
dsap: layout $(MODE)/certificates/dsap.pem

$(MODE)/certificates/dsap.pem:
	openssl dsaparam -out $@ 1024

# --------------------------------------------------------------------
ifeq ($(MODE),rsa)
$(MODE)/certificates/%.key:
	openssl genrsa -out $@ 1024
endif

ifeq ($(MODE),ecdsa)
$(MODE)/certificates/%.key:
	openssl ecparam -genkey -name prime256v1 -out $@
endif

ifeq ($(MODE),dsa)
$(MODE)/certificates/%.key: $(MODE)/certificates/dsap.pem
	openssl gendsa -out $@ $(MODE)/certificates/dsap.pem
endif

$(MODE)/certificates/%.p12: $(MODE)/certificates/%.crt $(MODE)/certificates/ca.crt
	echo | openssl pkcs12 -export -password stdin \
	    -in       $(PKI)/certificates/$*.crt   \
	    -inkey    $(PKI)/certificates/$*.key   \
	    -name     "uTLS PKI ($*)" \
	    -out      $(PKI)/certificates/$*.p12

$(MODE)/certificates/%.csr: $(MODE)/certificates/%.key
	openssl req -new -batch \
	    -subj   "/C=$(C)/ST=$(ST)/L=$(L)/O=$(O)/OU=$(OU)/CN=$*/emailAddress=$(EA)" \
	    -config config/ca.config \
	    -key    $< \
	    -out    $@

$(MODE)/certificates/%.crt: $(MODE)/certificates/%.csr $(MODE)/certificates/ca.crt
	openssl ca -batch -config config/ca.config -in $< -out $@
	openssl x509 -in $@ -noout -text

# --------------------------------------------------------------------
hash:
	cd $(MODE)/db/ca.db.certs && c_rehash .

# --------------------------------------------------------------------
layout:
	@$(call layout)

# --------------------------------------------------------------------
clean:
	rm -rf $(PKI)/certificates
	rm -rf $(PKI)/db
	if [ -d $(PKI) ]; then rmdir $(PKI); fi

# --------------------------------------------------------------------
define pki
  +$(MAKE) MODE=$(1) clean
  +$(MAKE) MODE=$(1) dh dsap ca
  +$(MAKE) MODE=$(1) '$(1)/certificates/$(1).cert.mitls.org.p12'
  +$(MAKE) MODE=$(1) hash
endef

pki.built:
	$(call pki,rsa)
	$(call pki,dsa)
	$(call pki,ecdsa)
	touch $@

pki.clean:
	+$(MAKE) MODE=rsa clean
	+$(MAKE) MODE=dsa clean
	+$(MAKE) MODE=ecdsa clean
	rm pki.built
