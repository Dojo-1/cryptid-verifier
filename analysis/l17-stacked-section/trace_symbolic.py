"""Reproduce the frozen symbolic extension; do not overwrite the historical result."""
from __future__ import annotations
import json
from pathlib import Path
from rules import trajectory
from words import Word


def main():
    root=Path(__file__).resolve().parent
    protocol=json.loads((root/'symbolic-extension-protocol.json').read_text())
    limit=protocol['maximum_contextual_rewrites']
    actual=trajectory(6575648756,Word.literal('1'),limit)
    expected=json.loads((root/'symbolic-extension.json').read_text())['trace']
    assert actual==expected,'Frozen symbolic trace differs'
    print('Exact symbolic trace reproduced:',len(actual['records']),'rewrites')
    print('Stop:',actual['stop']['budget'],'limit',actual['stop']['limit'])
    print('Final pair counter digits:',len(str(actual['stop']['a'])))
    print('Derived cumulative transition-count digits:',len(str(actual['steps'])))
    print('No raw simulation or Lean verification is claimed by this arithmetic check.')


if __name__=='__main__':main()
