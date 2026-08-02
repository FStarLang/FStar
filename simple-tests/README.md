# simple-tests

Acceptance tests for the simplified (name + precondition + postcondition) effect
system.  They are checked by the *stage1* compiler against `simple-lib/`, not
against `ulib/`:

    make -f mk/simple.mk test

Each file documents the property it pins down.  Files whose name starts with
`Neg` are expected to *fail*, and the expected error is recorded in a
corresponding `.expected` file.
