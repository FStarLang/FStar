import sys
import subprocess

result=subprocess.check_output("grep -or 'is_[A-Z]\w*' .", shell=True)
lines=[ l for l in str(result).splitlines() if l.find('.fst') != -1]
for l in lines:
    content = l.split(':')
    constr=content[1].strip()[0:-1]
    print("sed -i -e 's/%s[.]/%s?./g' %s" % (constr, constr, content[0]))
    subprocess.call("sed -i -e 's/%s[.]/%s?./g' %s" % (constr, constr, content[0]), shell=True)
