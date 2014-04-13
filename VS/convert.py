#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, lxml.etree as xml

WHEREIAM = os.path.realpath(os.path.dirname(__file__))
FSPROJ   = os.path.join(WHEREIAM, 'FStar.sln')

# --------------------------------------------------------------------
def name10(x):
    base, ext = os.path.splitext(x)
    return ('%s-10' % (base,)) + ext

# --------------------------------------------------------------------
def _main():
    NS = dict(m = 'http://schemas.microsoft.com/developer/msbuild/2003')

    with open(FSPROJ, 'rb') as stream:
        contents = stream.read()
    projects = re.findall(r'"([^"]*\.fsproj\b)"', contents)
    contents = re.sub(r'\.fsproj\b', r'-10.fsproj', contents)
    with open(name10(FSPROJ), 'w') as stream:
        stream.write(contents)

    projects = ['\\'.join(re.split(r'\\+', x)) for x in projects]
    paths    = [os.path.join(*x.split('\\')) for x in projects]
    paths    = [os.path.join(WHEREIAM, x) for x in paths]
    paths    = [os.path.realpath(x) for x in paths]

    for project in paths:
        with open(project, 'r') as stream:
            doc = xml.fromstring(stream.read())
        for node in doc.xpath('//m:MinimumVisualStudioVersion', namespaces = NS):
            if node.text == '11':
                node.text = '10'
        for node in doc.xpath('//m:*[@Include]', namespaces = NS):
            ref = node.get('Include')
            ref = os.path.join(*ref.split('\\'))
            ref = os.path.join(os.path.dirname(project), ref)

            if os.path.realpath(ref) in paths:
                node.set('Include', name10(node.get('Include')))

        with open(name10(project), 'w') as stream:
            stream.write(xml.tostring(doc))

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
