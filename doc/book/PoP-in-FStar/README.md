# PoP-in-FStar
The Proof-oriented Programming in F* Book


# Build

To set up an environment to build the book, you will need python3, sphinx, and the sphinx_rtd_theme.

Once you have python3, on Ubuntu-24, install using:

* sudo apt install python3-sphinx
* sudo apt install python3-sphinx_rtd_theme

Then, see book/Makefile:

- set FSTAR_HOME, if the default is not correct
- likewise, set PULSE_HOME

Then,

* make -C book prep #to copy source files from F* and Pulse into the book build folders
* make -C book html
* make -C book pdf

You should have book/_build/html/index.html


# Deploy


Set FSTARLANG_ORG_ROOT in book/Makefile

* make deploy
