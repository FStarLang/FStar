FSTAR_OPTIONS += --ext optimize_let_vc

# Checking a library, make sure to not use the parent lib.
FSTAR_OPTIONS += --no_default_includes
FSTAR_OPTIONS += --include $(SRC)

EXTRACT_NS :=
EXTRACT_NS += -FStar.Buffer
EXTRACT_NS += -FStar.Bytes
EXTRACT_NS += -FStar.Char
EXTRACT_NS += -FStar.CommonST
EXTRACT_NS += -FStar.Constructive
EXTRACT_NS += -FStar.Dyn
EXTRACT_NS += -FStar.Float
EXTRACT_NS += -FStar.Ghost
EXTRACT_NS += -FStar.Heap
EXTRACT_NS += -FStar.Monotonic.Heap
EXTRACT_NS += -FStar.HyperStack.All
EXTRACT_NS += -FStar.HyperStack.ST
EXTRACT_NS += -FStar.HyperStack.IO
EXTRACT_NS += -FStar.Int16
EXTRACT_NS += -FStar.Int32
EXTRACT_NS += -FStar.Int64
EXTRACT_NS += -FStar.Int8
EXTRACT_NS += -FStar.IO
EXTRACT_NS += -FStar.List
EXTRACT_NS += -FStar.List.Tot.Base
EXTRACT_NS += -FStar.Option
EXTRACT_NS += -FStar.Pervasives.Native
EXTRACT_NS += -FStar.ST
EXTRACT_NS += -FStar.Exn
EXTRACT_NS += -FStar.String
EXTRACT_NS += -FStar.UInt16
EXTRACT_NS += -FStar.UInt32
EXTRACT_NS += -FStar.UInt64
EXTRACT_NS += -FStar.UInt8
EXTRACT_NS += -FStar.Pointer.Derived1
EXTRACT_NS += -FStar.Pointer.Derived2
EXTRACT_NS += -FStar.Pointer.Derived3
EXTRACT_NS += -FStar.BufferNG
EXTRACT_NS += -FStar.TaggedUnion
EXTRACT_NS += -FStar.Bytes
EXTRACT_NS += -FStar.Util
EXTRACT_NS += -FStar.InteractiveHelpers
EXTRACT_NS += -FStar.Class.Embeddable
EXTRACT_NS += -FStar.Vector.Base
EXTRACT_NS += -FStar.Vector.Properties
EXTRACT_NS += -FStar.Vector
EXTRACT_NS += -FStar.TSet
EXTRACT_NS += -FStar.MSTTotal
EXTRACT_NS += -FStar.MST
EXTRACT_NS += -FStar.NMSTTotal
EXTRACT_NS += -FStar.NMST
EXTRACT_NS += -FStar.Printf
EXTRACT_NS += -FStar.ModifiesGen
EXTRACT_NS += -LowStar.Printf
EXTRACT_NS += -FStar.Sealed
EXTRACT_NS += +FStar.List.Pure.Base
EXTRACT_NS += +FStar.List.Tot.Properties
EXTRACT_NS += +FStar.Int.Cast.Full

# Note: the pluginlib rules will enable these.
EXTRACT_NS += -FStar.Tactics
EXTRACT_NS += -FStar.Reflection

EXTRACT := --extract '* $(EXTRACT_NS)'

# Leaving this empty, F* will scan the include path for all fst/fsti
# files. This will read fstar.include and follow it too.
# ROOTS :=
# No! If we do that, we will pick up files from the current directory
# (the root of the repo) since that is implicitly included in F*'s
# search path. So instead, be explicit about scanning over all the files
# in $(SRC) (i.e. ulib). Note that there is a still a problem if there is a
# file in the cwd named like a file in ulib/, F* may prefer the former.
#
# Update: generic.mk will now complain too.
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')

include mk/generic-1.mk
