FROM fstar-base

MAINTAINER Daniel Fabian <daniel.fabian@integral-it.ch>; Benjamin Beurdouche <benjamin.beurdouche@inria.fr>

# Install required packages
RUN sudo apt-get install -y emacs libglu1-mesa xfonts-terminus
RUN echo "(require 'package)" > .emacs
RUN echo "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" >> .emacs
RUN echo "(package-initialize)" >> .emacs
RUN echo "(set-default 'fstar-executable \"~/FStar/bin/fstar.exe\")" >> .emacs
RUN echo "(global-flycheck-mode)" >> .emacs
RUN echo "(add-to-list 'default-frame-alist '(font . \"Terminus-14\"))" >> .emacs

ENV LANG C.UTF-8
RUN emacs --batch \
	--eval "(require 'package)" \
	--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
	--eval "(package-initialize)" \
	--eval "(package-refresh-contents)" \
	--eval "(package-install 'fstar-mode)" \
	--eval "(package-install 'flycheck)"