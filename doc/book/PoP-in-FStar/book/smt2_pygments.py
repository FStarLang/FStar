from pygments.lexer import RegexLexer, words
from pygments.token import *

# very rough lexer; not 100% precise
class CustomLexer(RegexLexer):
    name = 'SMT2'
    aliases = ['smt2']
    filenames = ['*.smt2']
    keywords = (
        'assert'      ,
        'declare-datatypes',
        'declare-fun' ,
        'declare-sort',
        'define-fun'  ,        
        'set-option'  ,
        'pattern'     ,
        'weight'      ,        
        'qid'         ,
        'check-sat'   ,
        'named'       ,
    )
    tokens = {
        'root': [
            (r' ', Text),
            (r'\n', Text),
            (r'\r', Text),
            (r';.*\n', Comment),
            (words(keywords, suffix=r'\b'), Keyword),
            (r'0x[0-9a-fA-F_]+', Literal.Number),
            (r'[0-9_]+', Literal.Number),
            (r'[a-zA-Z_]+', Text),
            (r'.', Text),
        ]
    }

#class CustomFormatter:
