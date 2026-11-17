"""Exact guarded compositions. No execution or writes on import."""

MACHINE = '1RB0RE_1LC0RA_0LD1LB_1LA1LE_0LB0LF_1LD---'
RULES = {}


def bottom():
    return [('1', '2*p-10'), ('01', 7)]


def left(n):
    return [('10', 'p'), ('0', 1), ('10', 'c'), ('0', 1), ('10', 1), ('01', n)]


def suffix(kind, n):
    if kind == 'zero':
        return bottom() + [('1', '2*c-3'), ('010', 1), ('1', f'2*({n})+1')]
    if kind == '111':
        return [('1', '2*p-6'), ('01', f'c+({n})+6'), ('0', 1)]
    if kind == '1100_n5':
        return bottom() + [('1', '2*c-9'), ('01', 10), ('111', 1)]
    if kind == '1100_n6':
        return bottom() + [('1', '2*c-13'), ('01', 6), ('0011', 1), ('01', 5), ('111', 1)]
    if kind == '1100_n7':
        return bottom() + [('1', '2*c-3'), ('01', 9), ('111', 1)]
    if kind == '1100_large':
        return bottom() + [('1', '2*c-3'), ('010', 1), ('1', f'2*({n})-13'), ('01', 7), ('111', 1)]
    if kind == '1101':
        return left(f'({n})-2') + [('00', 1), ('10', 3)]
    if kind == '110100_n5':
        return bottom() + [('1', '2*c-9'), ('01', 9), ('0', 1), ('1', 6)]
    if kind == '110100_n6':
        return bottom() + [('1', '2*c-13'), ('01', 6), ('0011', 1), ('01', 4), ('0', 1), ('1', 6)]
    if kind == '110100_n7':
        return bottom() + [('1', '2*c-3'), ('01', 8), ('0', 1), ('1', 6)]
    if kind == '110100_large':
        return bottom() + [('1', '2*c-3'), ('010', 1), ('1', f'2*({n})-13'), ('01', 6), ('0', 1), ('1', 6)]
    raise ValueError(kind)


def clock(kind, n):
    return {
        'zero': f'2*p+2*c+2*({n})+34',
        '111': f'2*p+4*c+4*({n})+28',
        '1100_n5': '2*p+2*c+98',
        '1100_n6': '2*p+2*c+114',
        '1100_n7': '2*p+2*c+94',
        '1100_large': f'2*p+2*c+2*({n})+80',
        '1101': '14',
        '110100_n5': '2*p+2*c+102',
        '110100_n6': '2*p+2*c+118',
        '110100_n7': '2*p+2*c+98',
        '110100_large': f'2*p+2*c+2*({n})+84',
    }[kind]


TERMINAL = {'zero': '0', '111': '111', '1100_n5': '1100', '1100_n6': '1100',
            '1100_n7': '1100', '1100_large': '1100', '1101': '1101'}

for kind in TERMINAL:
    fixed = {'1100_n5': 5, '1100_n6': 6, '1100_n7': 7}.get(kind)
    n = fixed if fixed is not None else 'n'
    guards = {'p': [6, None], 'c': [7, None]}
    if fixed is None:
        guards['n'] = [8 if kind == '1100_large' else 5, None]
    start = f'-2*p-2*c-2*({n})-4'
    RULES['B_' + kind] = dict(
        guards=guards, source=left(n) + [(TERMINAL[kind], 1), ('v', 1)],
        target=suffix(kind, n) + [('v', 1)], steps=clock(kind, n),
        source_start=start, target_start=start, shift=4 if kind == '1101' else start,
        source_q=1, target_q=0 if kind == '1101' else 2,
        read_bounds=[-4 if kind == '1101' else start, len(TERMINAL[kind]) - 1],
        terminal=TERMINAL[kind], kind=kind, n=n)


def composed(width, kind, j, minimum_j=None):
    r, s, base, entry = (2, 2, 5, 38) if width == 2 else (5, 3, 9, 62)
    n = f'{base}+({j})'
    guards = {'p': [6, None], 'c': [7, None]}
    if minimum_j is not None:
        guards['j'] = [minimum_j, None]
    start = f'-2*p-2*c-{2*base}'
    RULES[f'C{width}_' + kind] = dict(
        guards=guards,
        source=[('10', 'p'), ('0', 1), ('10', 'c'), ('0', 1), ('10', s),
                ('0', 1), ('10', r), ('111', 1), ('10', j), (TERMINAL[kind], 1), ('v', 1)],
        target=suffix(kind, n) + [('v', 1)],
        steps=f'{entry}+2*({j})+({clock(kind, n)})',
        source_start=start, target_start=start,
        shift=f'8+2*({j})' if kind == '1101' else start,
        source_q=2, target_q=0 if kind == '1101' else 2,
        read_bounds=[start, f'3+2*({j})+{len(TERMINAL[kind])}'],
        terminal=TERMINAL[kind], kind=kind, j=j, n=n)


for width in (2, 5):
    for kind in ('zero', '111', '1101'):
        composed(width, kind, 'j', 0)
    if width == 2:
        for j in range(3):
            composed(width, f'1100_n{5+j}', j)
        composed(width, '1100_large', 'j', 3)
    else:
        composed(width, '1100_large', 'j', 0)


# Secondary returns after the typed1101 exit, when its next two cells are00.
for kind, fixed in [('110100_n5', 5), ('110100_n6', 6), ('110100_n7', 7), ('110100_large', None)]:
    TERMINAL[kind] = '110100'
    n = fixed if fixed is not None else 'n'
    guards = {'p': [6, None], 'c': [7, None]}
    if fixed is None:
        guards['n'] = [8, None]
    start = f'-2*p-2*c-2*({n})-4'
    RULES['B_'+kind] = dict(
        guards=guards, source=left(n)+[('110100', 1), ('v', 1)],
        target=suffix(kind, n)+[('v', 1)], steps=clock(kind, n),
        source_start=start, target_start=start, shift=start,
        source_q=1, target_q=2, read_bounds=[start, 5], terminal='110100', kind=kind, n=n)
for j in range(3):
    composed(2, f'110100_n{5+j}', j)
composed(2, '110100_large', 'j', 3)
composed(5, '110100_large', 'j', 0)


# q, time, exit_q, exit_head, lo, input, output. Head0 at entry.
KERNELS = {
    'C2B': (2, 38, 1, 4, -6, '1001010111', '01'*5),
    'C5B': (2, 62, 1, 4, -14, '10'*2+'0'+'10'*5+'111', '01'*9),
    'B1100_n5': (1, 75, 2, -21, -20, '0'+'10'*3+'0'+'10'+'01'*5+'1100', '10'*10+'1111'),
    'B1100_n6': (1, 95, 2, -27, -26, '0'+'10'*5+'0'+'10'+'01'*6+'1100', '101010101010100110101010101111'),
    'B1100_n7': (1, 65, 2, -19, -18, '00'+'10'+'01'*7+'1100', '10'*9+'1111'),
    'B1101': (1, 14, 0, 4, -4, '01011101', '00101010'),
}


def classify(word):
    """Disjoint dispatch on a finite binary tape with zero exterior."""
    if not isinstance(word, str) or set(word) - {'0', '1'}:
        raise ValueError('finite binary word required')
    def bit(i):
        return word[i] if i < len(word) else '0'
    i = 0
    while bit(i) == '1' and bit(i+1) == '0':
        i += 2
    if bit(i) == '0':
        terminal = '0'
    elif bit(i+2) == '1':
        terminal = '111'
    else:
        terminal = '1100' if bit(i+3) == '0' else '1101'
    return dict(j=i//2, terminal=terminal, consumed=i+len(terminal),
                suffix=word[i+len(terminal):])
