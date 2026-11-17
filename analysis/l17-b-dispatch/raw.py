"""Literal Python replay; no dispatcher or counter-rule import."""
from paths import HERE  # installs the frozen OPS path
from reference import OPS


def replay(req):
    ones = set(req['ones'])
    q, h, t = req['q'], req['head'], 0
    reads = []
    while t < req['limit']:
        b = int(h in ones)
        op = OPS[q][b]
        if op is None:
            break
        reads.append([q, h, b])
        value, direction, q = op
        if value:
            ones.add(h)
        else:
            ones.discard(h)
        h += direction
        t += 1
    return dict(q=q, head=h, steps=t, halted=OPS[q][int(h in ones)] is None,
                ones=sorted(ones), reads=reads,
                read_min=min((x[1] for x in reads), default=None),
                read_max=max((x[1] for x in reads), default=None))
