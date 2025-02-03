#!/bin/bash

# This scripts builds a "standalone" package with F* and Pulse. It
# does not include karamel as there is no way to install it and use it
# without setting a KRML_HOME, which I would like to avoid. This will be
# fixed soon.

set -eux

if [ "$(uname -s)" = "Darwin" ]; then
MAKE="gmake -ksj$(nproc)"
else
MAKE="make -ksj$(nproc)"
fi

if ! [ -d FStar ]; then
  git clone https://github.com/FStarLang/FStar --depth 1
fi

$MAKE -C FStar ADMIT=1
export FSTAR_EXE=$(pwd)/FStar/bin/fstar.exe

$MAKE ADMIT=1

rm -rf _pak
mkdir -p _pak/pulse
$MAKE -C FStar install PREFIX=$(pwd)/_pak/pulse

$MAKE install PREFIX=$(pwd)/_pak/pulse

cat >_pak/pulse/bin/pulse << EOF
#!/bin/bash

# Pulse is really just F* + an include path. The pulse plugin
# is loaded automatically by F* when needed (e.g. when processing
# a #lang-pulse declaration).

D=\$(dirname "\$0")

exec \$D/fstar.exe --include "\$D/../lib/pulse" "\$@"
EOF

chmod +x _pak/pulse/bin/pulse

KERNEL=$(uname -s)
ARCH=$(uname -m)
PAK=pulse-$KERNEL-$ARCH.tar.gz

tar czf $PAK -C _pak .

echo Done
ls -l $PAK
