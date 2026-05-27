from pygments.lexer import RegexLexer, words
from pygments.token import *

fstar_keywords = (
    'attributes' ,
    'noeq'       ,
    'unopteq'    ,
    'and'        ,
    'assert'     ,
    'assert_norm' ,        
    'assume'     ,
    'begin'      ,
    'by'         ,
    'calc'       ,
    'class'      ,
    'decreases'  ,
    'Dv'         ,
    'effect'     ,
    'eliminate'  ,
    'else'       ,
    'end'        ,
    'ensures'    ,
    'exception'  ,
    'exists'     ,
    'false'      ,
    'friend'     ,
    'forall'     ,
    'fun'        ,
    'function'   ,
    'GTot'       ,
    'if'         ,
    'in'         ,
    'include'    ,
    'inline'     ,
    'inline_for_extraction'     ,
    'instance'   ,
    'introduce'  ,
    'irreducible',
    'let'        ,
    'logic'      ,
    'match'      ,
    'module'     ,
    'new'        ,
    'new_effect' ,
    'layered_effect'            ,
    'polymonadic_bind'          ,
    'polymonadic_subcomp'       ,
    'SMTPat'     ,        
    'noextract',
    'of'         ,
    'open'       ,
    'opaque'     ,
    'private'    ,
    'range_of'   ,
    'rec'        ,
    'reifiable'  ,
    'reify'      ,
    'reflectable',
    'requires'   ,
    'returns'    ,
    'set_range_of',
    'sub_effect' ,
    'synth'      ,
    'then'       ,
    'total'      ,
    'Tot'        ,
    'true'       ,
    'try'        ,
    'type'       ,
    'unfold'     ,
    'unfoldable' ,
    'val'        ,
    'when'       ,
    'with'       ,
    '_'          ,
    'Lemma'      ,
)

# very rough lexer; not 100% precise
class CustomLexer(RegexLexer):
    name = 'FStar'
    aliases = ['fstar']
    filenames = ['*.fst', '*.fsti']
    tokens = {
        'root': [
            (r' ', Text),
            (r'\n', Text),
            (r'\r', Text),
            (r'//.*\n', Comment),
            (r'\([*]([^*]|[*]+[^)])*[*]+\)', Comment),
            (words(fstar_keywords, suffix=r'\b'), Keyword),
            (r'[a-zA-Z_0-9]+', Text),
            (r'.', Text),
        ]
    }

pulse_keywords = (
    "fn",
    "fold",
    "rewrite",
    "each",
    "mut",
    "ghost",
    "atomic",
    "show_proof_state",
    "while",
    "invariant",
    "with_invariants",
    "opens",
    "parallel"
)

class PulseLexer(RegexLexer):
    name = 'Pulse'
    aliases = ['pulse']
    filenames = ['*.fst', '*.fsti']
    tokens = {
        'root': [
            (r' ', Text),
            (r'\n', Text),
            (r'\r', Text),
            (r'//.*\n', Comment),
            (r'\([*]([^*]|[*]+[^)])*[*]+\)', Comment),
            (words(fstar_keywords, suffix=r'\b'), Keyword),
            (words(pulse_keywords, suffix=r'\b'), Keyword),            
            (r'[a-zA-Z_]+', Text),
            (r'.', Text),
        ]
    }
    
#class CustomFormatter:
