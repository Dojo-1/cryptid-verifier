"""Proposed contextual nesting identity, justified in NESTING.md."""
from extend import Word

U='01'*8+'1'
T='01'*7+'111'


def nest(a,n,v=Word()):
    if type(a) is not int or type(n) is not int or a<7 or n<0:
        raise ValueError('a>=7 and n>=0 must be integers')
    return {'word':v.prepend(('1',2*a-12),(T,n+1)),
            'steps':4*a+74*n+50,'shift':-2}


def a_nest(n,v=Word()):
    if type(n) is not int or n<0:raise ValueError('n>=0 must be an integer')
    return {'word':v.prepend(('11',1),(T,n+1)),
            'steps':60+74*n,'shift':-16}
