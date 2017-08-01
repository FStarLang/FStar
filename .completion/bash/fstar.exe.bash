__get_options() {
  fstar.exe --help |& grep -Eo -- "--[^=,;#/ ]*"
}

__complete_fstar () {
  local cur
  if [ -z "$_fstar_options" ]; then
    _fstar_options=$(__get_options)
  fi

  COMPREPLY=()
  cur=${COMP_WORDS[COMP_CWORD]}

  if [[ "$cur" == -* ]]; then
    COMPREPLY=( $(compgen -W "$_fstar_options" -- "$cur") )
  else
    COMPREPLY=( $(compgen -f -- "$cur") )
  fi
}

complete -o filenames -F __complete_fstar fstar.exe
