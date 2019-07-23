FROM fstarlang/fstar

MAINTAINER Daniel Fabian <daniel.fabian@integral-it.ch>; Benjamin Beurdouche <benjamin.beurdouche@inria.fr>

# Install required packages
RUN sudo apt-get install -y emacs libglu1-mesa xfonts-terminus fonts-symbola

ENV LANG C.UTF-8
RUN emacs --batch \
	--eval "(require 'package)" \
	--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
	--eval "(package-initialize)" \
	--eval "(package-refresh-contents)" \
	--eval "(package-install 'fstar-mode)" \
	--eval "(package-install 'flycheck)"

ADD .emacs .emacs
RUN sudo chown build:build .emacs
