# Enable hierarchical namespaces. The file A/B/C.fst is known under its
# path-derived long name A.B.C, NOT as the short name C. Since A/B/C.fst
# declares [module C] and Test.fst does [open C], resolution must fail.
OTHERFLAGS += --hierarchical_namespaces
include ../Makefile.sub
