#!/bin/bash

## This script applies the renamings described above to all *fst and
## *fsti files in the current directory.

## The script is meant to be idempotent. The first run of the script
## should print diagnostics describing what was changed. The second
## run of the script should print no diagnostic output.

## All the rewrites are done in two stages,
##   first checking if the phrase to be rewritten is present in a file
##   and only then rewriting that file with sed
## This ensures that the timestamps of unchanged files are preserved
## allowing incremental checking / extraction to work in the presence
## of these renamings.

## It relies on the following abbreviations:
##   module HS  = FStar.HyperStack
##   module HST = FStar.HyperStack.ST
## If these are not already present in a file,
## it will add them on the lines immediately following the module name

## replaces $1 with $2
## in every .fst and .fsti file
## that contains $3
replace() {
    FILES_WITH_OPEN=`grep -l "$3" *fst *fsti`
    if [ -n "$FILES_WITH_OPEN" ]; then
        FILES=`grep -l "$1" $FILES_WITH_OPEN`
        if [ -n "$FILES" ]; then
            echo "replacing $1 with $2 in $FILES"
            sed -i "s/$1/$2/g" $FILES
        fi
    fi
}

##adds module $1 = $2
##to every file that has an occurrence of $1\.
##but lacks an occurrence of module $1 =
add_module_abbrev()
{
    FILES_WITH_USES=`grep -l "$1\." *fst *fsti`
    FILES_WITH_USES_BUT_WITHOUT_MODULE_ABBREV=`grep -L "module $1\s*=" $FILES_WITH_USES`
    if [ -n "$FILES_WITH_USES_BUT_WITHOUT_MODULE_ABBREV" ]; then
        echo "adding 'module $1 = $2' to $FILES_WITH_USES_BUT_WITHOUT_MODULE_ABBREV"
        sed -i "s/^module \([^=]*\)$/module \1\nmodule $1 = $2 \/\/Added automatically/" $FILES_WITH_USES_BUT_WITHOUT_MODULE_ABBREV
    fi
}

# renamings for FStar.HyperHeap
rename_hyperheap()
{
    replace 'HyperHeap\.'                     'HH\.'
    replace 'HH\.contains_ref'                'HS\.contains'
    replace 'HH\.fresh_rref'                  'HS\.fresh_ref'
    replace 'HH\.fresh_region'                'HS\.fresh_region'
    replace 'HH\.modifies_one'                'HS\.modifies_one'
    replace 'HH\.modifies_just'               'HS\.modifies'
    replace 'HH\.modifies_rref'               'HS\.modifies_ref'
    replace 'modifies_rref'                   'HS\.modifies_ref'
    replace 'HH\.modifies'                    'HS\.modifies_transitively'
    replace 'HH\.color'                       'HS\.color'
    replace 'HH\.rid'                         'HS\.rid'
    replace 'HH\.root'                        'HS\.root'
    replace 'HH\.parent'                      'HS\.parent'
    replace 'HH\.extends'                     'HS\.extends'
    replace 'HH\.disjoint'                    'HS\.disjoint'
    replace 'HH\.equal_on'                    'HS\.equal_on'
    replace 'HS\.HS?\.h'                      ''
    replace 'HST\.stronger_fresh_region'      'HS\.fresh_region'
    replace 'stronger_fresh_region'           'HS\.fresh_region'
    replace 'open \s*FStar.HyperHeap'         ''
    replace 'module HH\s*=\s*FStar.HyperHeap' ''
}

#renamings for FStar.Monotonic.RRef
rename_mrref()
{
    replace 'MR\.reln'                               'Preorder\.preorder'
    replace 'MR\.monotonic'                          'Preorder\.preorder_rel'
    replace 'MR\.m_rref'                             'HST\.m_rref'
    replace 'MR\.as_hsref'                           ''
    replace 'MR\.as_hsref'                           ''                          "open FStar.Monotonic.RRef"
    # can't be done automatically
    # 5.  `MR.m_contains r m` --> `HS.contains m r`
    replace 'MR\.m_fresh'                            'HS\.fresh_ref'
    replace 'MR\.m_sel'                              'HS\.sel'
    replace 'm_sel'                                  'sel'                       "open FStar.Monotonic.RRef"
    replace 'MR\.m_alloc'                            'HST\.ralloc'
    replace 'm_alloc'                                'HST\.ralloc'               "open FStar.Monotonic.RRef"
    replace 'MR\.m_read'                             'HST\.op_Bang'
    replace 'm_read'                                 'HST\.op_Bang'              "open FStar.Monotonic.RRef"
    replace 'MR\.m_write'                            'HST\.op_Colon_Equals'
    replace 'm_write'                                'HST\.op_Colon_Equals'      "open FStar.Monotonic.RRef"
    replace 'MR\.witnessed'                          'HST\.witnessed'
    replace 'MR\.m_recall'                           'HST\.recall'
    replace 'm_recall'                               'HST\.recall'               "open FStar.Monotonic.RRef"
    replace 'MR\.rid_exists'                         'HST\.region_contains_pred'
    replace 'MR\.rid'                                'HST\.erid'
    replace 'MR\.witness'                            'HST\.mr_witness'
    replace 'MR\.testify_forall'                     'HST\.testify_forall'
    replace 'MR\.testify'                            'HST\.testify'
    replace 'MR\.ex_rid_of_rid'                      'HST\.witness_region'
    replace 'MR\.ex_rid'                             'HST\.ex_rid'
    replace 'MR\.stable_on_t'                        'HST\.stable_on_t'
    replace 'open \s*FStar.Monotonic.RRef'           ''
    replace 'module MR\s*=\s*FStar.Monotonic.RRef'   ''
}

add_hs_and_hst()
{
    add_module_abbrev 'HST' 'FStar.HyperStack.ST'
    add_module_abbrev 'HS'  'FStar.HyperStack'
}

replace_hs_mem_projectors()
{
    FILES=`ls *fst *fsti`
    sed -i "s/\([^ \(]*\)\.HS\.h\([\ \)\n\r\t]\)/\(HS\.get_hmap\ \1\)\2/g" $FILES
    sed -i "s/\([^ \(]*\)\.HS\.tip\([\ \)\n\r\t]\)/\(HS\.get_tip\ \1)\2/g" $FILES
    sed -i "s/\([^ \(]*\)\.h\([\ \)\n\r\t]\)/\(HS\.get_hmap\ \1\)\2/g" $FILES
    sed -i "s/\([^ \(]*\)\.tip\([\ \)\n\r\t]\)/\(HS\.get_tip\ \1\)\2/g" $FILES
}

help()
{
    echo "Usage: renamings.sh <rename_hyperheap | rename_mrref | add_hs_and_hst | replace_hs_mem_projectors | replace <arg1> <arg2> | all>, where all is for applying all known upgrades"
}

if [ "$#" -eq 0 ]; then
    help
    exit 0
fi

CMD="$1"

case $CMD in
    rename_hyperheap)
	rename_hyperheap
	exit 0
	;;
    rename_mrref)
	rename_mrref
	exit 0
	;;
    add_hs_and_hst)
	add_hs_and_hst
	exit 0
	;;
    replace)
	if [ "$#" -ne 3 ]; then
	    help
	    exit 1
	fi
	replace $2 $3
	;;
    replace_hs_mem_projectors)
	replace_hs_mem_projectors
	;;
    all)
	echo "renaming hyperheap"
	rename_hyperheap
	echo "renaming mrref"
	rename_mrref
	# echo "adding hs and hst"
	# add_hs_and_hst
	echo "replacing HS.is_eternal_region"
	replace "HS\.is_eternal_region" "is_eternal_region"
	exit 0
	;;
    *)
	help
	exit 1
	;;
esac
