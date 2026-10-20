"""Compare two exact repeated-block parsers on identical bounded snapshots.

The summaries are representation diagnostics, never hardness or novelty scores.
Reservoir snapshots are not consecutive return events: no transition map is
inferred merely by joining adjacent saved snapshots.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from functools import lru_cache
import json
from pathlib import Path


@lru_cache(maxsize=200000)
def primitive(word):
    return (word + word).find(word, 1) == len(word)


def best_block(s, pos, max_block):
    winner, count = s[pos], 1
    for size in range(1, min(max_block, (len(s) - pos) // 2) + 1):
        word = s[pos:pos+size]
        if not primitive(word) or not s.startswith(word, pos+size):
            continue
        n = 2
        while s.startswith(word, pos+n*size):
            n += 1
        if n * len(winner) > count * size or count == 1:
            winner, count = word, n
    return winner, count


def compress(s, max_block=8):
    result, pos = [], 0
    while pos < len(s):
        word, count = best_block(s, pos, max_block)
        end = pos + len(word)*count
        if count >= 2 and end < len(s):
            nxt, n = best_block(s, end, max_block)
            full = end + len(nxt)*n
            short = end-len(word)
            nxt, n = best_block(s, short, max_block)
            if short + len(nxt)*n > full:
                count -= 1
        result.append((word,count))
        pos += len(word)*count
    assert ''.join(w*n for w,n in result) == s
    return result


def encode(snap, max_block=8):
    left = compress(snap['left'], max_block)
    # Both sides are parsed from their outer boundary toward the head.
    right = [(w[::-1], n) for w,n in compress(snap['right'][::-1],max_block)[::-1]]
    assert ''.join(w*n for w,n in right) == snap['right']
    return left,right


def summarize(record, max_block):
    families=defaultdict(list); block_counts=[]
    for s in record['snapshots']:
        left,right=encode(s,max_block)
        key=(s['q'],tuple(w for w,n in left),tuple(w for w,n in right))
        families[key].append({'t':s['t'],'section':s['section'],
                              'counts':[n for w,n in left+right]})
        block_counts.append(len(left)+len(right))
    rows=[]
    for (q,left,right),samples in families.items():
        if len(samples)<3:continue
        variables=[i for i in range(len(left)+len(right))
                   if len({s['counts'][i] for s in samples})>1]
        rows.append({'q':q,'left_blocks':left,'right_blocks':right,
                     'samples':len(samples),'varying_counts':variables,
                     'sections':sorted({s['section'] for s in samples}),
                     'examples':samples[:6]})
    rows.sort(key=lambda r:(len(r['left_blocks'])+len(r['right_blocks']),-r['samples']))
    return {'max_block':max_block,'snapshots':len(block_counts),
            'mean_blocks':sum(block_counts)/len(block_counts) if block_counts else None,
            'distinct_families':len(families),'recurrent_families':len(rows),'families':rows}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('traces',type=Path);p.add_argument('output',type=Path)
    args=p.parse_args()
    records=[json.loads(line) for line in args.traces.read_text().splitlines()]
    result=[]
    for r in records:
        row={k:v for k,v in r.items() if k!='snapshots'}
        row['baseline']=summarize(r,8);row['long_blocks']=summarize(r,32)
        result.append(row)
        print(r['id'], 'samples',len(r['snapshots']), 'families',
              row['baseline']['distinct_families'],row['long_blocks']['distinct_families'],
              'mean blocks',round(row['baseline']['mean_blocks'],2),round(row['long_blocks']['mean_blocks'],2),flush=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
