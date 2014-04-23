#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, optparse as opt, lxml.etree as xml

WHEREIAM = os.path.realpath(os.path.dirname(__file__))

# --------------------------------------------------------------------
class VersionSpec(object):
    def __init__(self, version, postfix = ''):
        self._version = version
        self._postfix = postfix

    version = property(lambda self : self._version)
    postfix = property(lambda self : self._postfix)

# --------------------------------------------------------------------
class Converter(object):
    NS = dict(m = 'http://schemas.microsoft.com/developer/msbuild/2003')

    def __init__(self, new, old):
        self._new = VersionSpec(**new)
        self._old = VersionSpec(**old)

    new = property(lambda self : self._new)
    old = property(lambda self : self._old)

    def _real_filename(filename, postfix, strip = ''):
        filename, ext = os.path.splitext(filename)
        if len(strip) > 0 and filename.endswith(strip):
            filename = filename[:-len(strip)]
        return '%s%s%s' % (filename, postfix, ext)
    _real_filename = staticmethod(_real_filename)

    def _read(cls, filename, postfix = '', strip = ''):
        path = cls._real_filename(filename, postfix, strip)
        with open(path, 'r') as stream:
            return stream.read()
    _read = classmethod(_read)

    def _write(cls, filename, contents, postfix = '', strip = ''):
        path = cls._real_filename(filename, postfix, strip)
        print path
        with open(path, 'w') as stream:
            stream.write(contents)
    _write = classmethod(_write)

    def convert(self, filename):
        reproject = r'"([^"]*%s\.fsproj\b)"' % re.escape(self.old.postfix)
        repfrom   = r'%s\.fsproj\b' % re.escape(self.old.postfix)
        repto     = r'%s.fsproj'    % self.new.postfix

        contents = self._read(filename, self.old.postfix)
        projects = re.findall(reproject, contents)
        contents = re.sub(repfrom, repto, contents)

        self._write(filename, contents, self.new.postfix)

        projects = ['\\'.join(re.split(r'\\+', x)) for x in projects]
        paths    = [os.path.join(*x.split('\\')) for x in projects]
        paths    = [os.path.join(WHEREIAM, x) for x in paths]
        paths    = [os.path.realpath(x) for x in paths]

        for project in paths:
            doc   = xml.fromstring(self._read(project))
            ns    = dict(namespaces = self.NS)
            nodes = doc.xpath('//m:MinimumVisualStudioVersion', **ns)

            for node in nodes:
                if node.text == self.old.version:
                    node.text = self.new.version

            for node in doc.xpath('//m:*[@Include]', **ns):
                ref = node.get('Include')
                ref = os.path.join(*ref.split('\\'))
                ref = os.path.join(os.path.dirname(project), ref)
                new = self._real_filename(node.get('Include'),
                                          postfix = self.new.postfix,
                                          strip   = self.old.postfix)
    
                if os.path.realpath(ref) in paths:
                    node.set('Include', new)

            doc = xml.tostring(doc, xml_declaration = True, encoding = 'utf-8')
            doc = doc.rstrip('\n').replace('\n', '\r\n')

            self._write(project, doc,
                        postfix = self.new.postfix,
                        strip   = self.old.postfix)

# --------------------------------------------------------------------
def _main():
    parser = opt.OptionParser()
    parser.add_option('-r', '--revert',
                      dest    = 'revert',
                      default = False,
                      action  = 'store_true',
                      help    = 'revert conversion')

    (options, args) = parser.parse_args()
    if len(args) > 0:
        parser.error('this script doesn\'t take arguments')

    v11 = dict(version = '11', postfix = '')
    v10 = dict(version = '10', postfix = '-10')

    if options.revert:
        converter = Converter(new = v11, old = v10)
    else:
        converter = Converter(new = v10, old = v11)

    converter.convert(os.path.join(WHEREIAM, 'FStar.sln'))

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
