#!/usr/bin/bash

#rename every A.fst to B.fst for every pair A,B in $ALL 
ALL="ext,FStar.FunctionalExtensionality arr,FStar.Array bytes,FStar.Bytes char,FStar.Char classical,FStar.Classical constr,FStar.Constructive crypto,FStar.Crypto elogic,FStar.ErasedLogic ghost,FStar.Ghost hyperHeap,FStar.HyperHeap int16,FStar.Int16 int31,FStar.Int31 int32,FStar.Int32 int64,FStar.Int64 int8,FStar.Int8 list,FStar.List listproperties,FStar.ListProperties map,FStar.Map matrix2,FStar.Matrix2 mref,FStar.MRef option,FStar.Option ordmap,FStar.OrdMap ordmapproperties,FStar.OrdMapProps ordset,FStar.OrdSet ordsetproperties,FStar.OrdSetProps pext,FStar.PredicateExtensionality seq,FStar.Seq seqproperties,FStar.SeqProperties squash,FStar.Squash squash_effect,SquashEffect squashproperties,FStar.SquashProperties st2,FStar.Relational string,FStar.String tcp,FStar.Tcp twoLevelHeap,FStar.TwoLevelHeap util,FStar.Util"

for i in $ALL; do
    KEY=`echo $i | sed 's/\(.*\),.*/\1/g'`
    VALUE=`echo $i | sed 's/[^,]*,\(.*\)/\1/g'`
    echo $KEY
    echo $VALUE
    ./rename.sh $KEY $VALUE
    echo "******************"
done

#test that it didn't break the regressions
make -C src regressions OTHERFLAGS=--lax
