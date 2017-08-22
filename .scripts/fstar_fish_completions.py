#!/usr/bin/env python3

import re

OPT_RE = re.compile(
    r"""\s*--(?P<name>[a-zA-Z0-9-_.]*) """ +
    r"""(\[(?P<arg>.*)\] )?""" +
    r"""(?P<desc>.*)""")


class Option:
    def __init__(self, name, arg_name, desc):
        self.name = name
        self.arg_name = arg_name
        self.desc = desc

    @classmethod
    def from_line(cls, line):
        m = OPT_RE.match(line.strip())
        if m is None:
            return None
        return cls(m.group("name"),
                   m.group("arg"),
                   m.group("desc").strip())

    def to_fish_complete(self):
        completion = ["complete", "-c", "fstar.exe"]
        completion.extend(["-l", self.name])
        if self.arg_name:
            # takes parameters
            completion.append("-r")
        completion.extend(["--description", '"{}"'.format(self.desc)])
        return " ".join(completion)


if __name__ == "__main__":
    import sys

    import argparse
    parser = argparse.ArgumentParser(description="""
Generate completions for the fish shell from fstar.exe --help

fstar.exe --help | fstar_fish_completions.py > \\
    ~/.completion/fish/fstar.exe.fish """,
formatter_class=argparse.RawDescriptionHelpFormatter)
    args = parser.parse_args()

    help_line = sys.stdin.readline()
    if not help_line.startswith("fstar.exe "):
        parser.print_help()
        sys.exit(1)

    print("# fstar.exe")
    print("# auto-generated from output of `fstar.exe --help`")
    print("# using FStar/.scripts/fstar_fish_completions.py")
    for line in sys.stdin:
        opt = Option.from_line(line)
        if opt:
            print(opt.to_fish_complete())
