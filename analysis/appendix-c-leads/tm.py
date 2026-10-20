"""Independent sparse-tape reference semantics and literal table conjugacies.

Undefined transitions halt without writing or moving. A step counts a defined
transition. State names and tape reflection may change; blank symbol 0 may not.
These conjugacies do not cover block encodings or behavioral equivalence.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from itertools import permutations


def parse(machine):
    rows = machine.split('_')
    if not rows or len(rows[0]) % 3:
        raise ValueError('invalid table')
    symbols = len(rows[0]) // 3
    if not 1 <= symbols <= 10 or not 1 <= len(rows) <= 26:
        raise ValueError('invalid dimensions')
    table = []
    for row in rows:
        if len(row) != symbols * 3:
            raise ValueError('nonrectangular table')
        ops = []
        for k in range(symbols):
            token = row[3*k:3*k+3]
            if token == '---':
                ops.append(None)
                continue
            if (not token[0].isdigit() or int(token[0]) >= symbols
                    or token[1] not in 'LR' or not 'A' <= token[2] < chr(65+len(rows))):
                raise ValueError('invalid transition')
            ops.append((int(token[0]), 1 if token[1] == 'R' else -1, ord(token[2])-65))
        table.append(tuple(ops))
    return tuple(table)


def serialize(table):
    return '_'.join(''.join('---' if op is None else
                           f'{op[0]}{"R" if op[1] == 1 else "L"}{chr(op[2]+65)}'
                           for op in row) for row in table)


@dataclass
class Config:
    tape: dict[int, int] = field(default_factory=dict)
    head: int = 0
    q: int = 0
    t: int = 0

    def step(self, table):
        op = table[self.q][self.tape.get(self.head, 0)]
        if op is None:
            return False
        write, move, nxt = op
        if write:
            self.tape[self.head] = write
        else:
            self.tape.pop(self.head, None)
        self.head += move
        self.q = nxt
        self.t += 1
        return True

    def normalized(self):
        """Entire finite nonzero tape, translated so the head is at zero."""
        return self.q, tuple(sorted((p-self.head, v) for p,v in self.tape.items()))


def relabel(table, mapping, reflected=False):
    result = [None] * len(table)
    for old, row in enumerate(table):
        result[mapping[old]] = tuple(None if op is None else
                                    (op[0], -op[1] if reflected else op[1], mapping[op[2]])
                                    for op in row)
    return tuple(result)


def rooted_form(table, start=0, reflected=False):
    """Canonical ordered transition graph, including unreachable states.

    Ordered BFS fixes every state reachable from start. Enumerating only the
    remaining states completes a full state permutation when necessary.
    """
    order, seen = [start], {start}
    for q in order:
        for op in table[q]:
            if op is not None and op[2] not in seen:
                seen.add(op[2]); order.append(op[2])
    remaining = [q for q in range(len(table)) if q not in seen]
    best = None
    for tail in permutations(remaining):
        mapping = {old:new for new,old in enumerate(order + list(tail))}
        code = serialize(relabel(table, mapping, reflected))
        item = code, tuple(mapping[q] for q in range(len(table))), reflected
        if best is None or item < best:
            best = item
    return best


def canonical(table, rooted=True):
    roots = [0] if rooted else range(len(table))
    code, mapping, reflected = min(rooted_form(table, q, reflected)
                                   for q in roots for reflected in (False, True))
    return code, mapping, reflected


def certificate(source, target, rooted=True):
    """Return a checked table isomorphism, or None. Unrooted permits A to move."""
    a, ma, ra = canonical(source, rooted)
    b, mb, rb = canonical(target, rooted)
    if a != b:
        return None
    inverse_b = {v:q for q,v in enumerate(mb)}
    mapping = tuple(inverse_b[v] for v in ma)
    reflected = bool(ra != rb)
    if relabel(source, mapping, reflected) != target:
        raise AssertionError('invalid conjugacy witness')
    if rooted and mapping[0] != 0:
        raise AssertionError('initial state changed')
    return {'state_map': ''.join(chr(65+q) for q in mapping),
            'reflected': reflected, 'source_start_maps_to': chr(65+mapping[0]),
            'preserves_blank_start': mapping[0] == 0,
            'all_transitions_checked': True}
