"""Refresh literal status, and check state renaming/reflection with witnesses."""
from __future__ import annotations
import csv
from collections import defaultdict
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
from tm import parse, canonical, certificate

ROOT = Path(__file__).resolve().parent
SHEET = 'https://docs.google.com/spreadsheets/d/1mMp8bAcTFT91j7azn72liX8NSTwc2E_ozKnOGTfRCfw/edit?gid=1330361301'
SOURCES = {
    'bb6': 'https://wiki.bbchallenge.org/w/images/6/69/BB6_holdouts_663.txt',
    'bb2x5': 'https://wiki.bbchallenge.org/w/images/9/9b/Bb2x5_informalLast37.txt',
    'annotated': SHEET,
    'upstream': 'https://github.com/google-deepmind/cryptids/tree/a0c1f56af53a76e985a656032b48015f7e48921b',
    'known_family': 'https://wiki.bbchallenge.org/wiki/1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA',
    'bb2x5_status': 'https://wiki.bbchallenge.org/wiki/BB(2,5)'
}
KNOWN = '1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA'


def main():
    leads = json.loads((ROOT/'leads.json').read_text())
    collections = {
        'bb6_663': (ROOT/'holdouts-663.txt').read_text().split(),
        'bb2x5_37': (ROOT/'holdouts-2x5-37.txt').read_text().split(),
        'upstream_modules': json.loads((ROOT/'upstream-inventory.json').read_text())['machines'],
        'lead': [r['machine'] for r in leads],
        'known_family': [KNOWN]
    }
    indexes = {}
    for name,machines in collections.items():
        for machine in machines:
            table = parse(machine)
            for rooted in (True, False):
                code = canonical(table, rooted)[0]
                indexes.setdefault((name,rooted,code),[]).append(machine)
    rows = list(csv.DictReader((ROOT/'bb6-annotated.csv').open()))
    result = []
    for lead in leads:
        machine = lead['machine']; table = parse(machine)
        item = dict(lead)
        item['literal_membership'] = {k:machine in v for k,v in collections.items() if k != 'lead'}
        item['annotated_rows'] = [dict(row=i+2, **r) for i,r in enumerate(rows)
                                  if r['Holdouts (From the 1534 list)'] == machine]
        matches = []
        for rooted in (True,False):
            code = canonical(table, rooted)[0]
            for name in collections:
                for target in indexes.get((name,rooted,code),[]):
                    if target == machine:
                        continue
                    witness = certificate(table, parse(target), rooted)
                    matches.append({'collection':name,'target':target,'rooted':rooted,'witness':witness})
        item['table_matches'] = matches
        item['prior_analysis'] = []
        if lead['id']=='L13':
            item['prior_analysis'] = [
                'Public annotation sheet already describes this as a probable halter.',
                'https://wiki.bbchallenge.org/wiki/User:RobinCodes/Machines_at_the_Edge',
                'https://github.com/Laturas/mildly_upsetting_tm_simulator']
        if lead['id']=='L22':
            item['prior_analysis'] = [
                'The annotation sheet links analysis of a closely related table. No behavioral equivalence to that table is established here.']
        if lead['id'] == 'L25':
            item['assessment'] = 'Reported solved with moderate rigor; wiki says independent verification pending. Exact outcome not independently checked here.'
        elif any(m['collection']=='known_family' for m in matches):
            item['assessment'] = 'Already documented Racheline2024 family; differing start states are not assumed to give the same blank orbit.'
        elif item['literal_membership']['bb6_663']:
            item['assessment'] = 'Listed BB(6) holdout; no proof of novelty or new cryptid status.'
        else:
            item['assessment'] = 'Absent literally from 663 representatives; resolution is not implied. Inspect witnessed matches and annotations.'
        result.append(item)
    inputs = ['leads.json','holdouts-663.txt','holdouts-2x5-37.txt','bb6-annotated.csv','upstream-inventory.json']
    groups = defaultdict(list)
    for lead in leads:
        groups[canonical(parse(lead['machine']),False)[0]].append(lead['id'])
    output = {'refreshed_at_utc':datetime.now(timezone.utc).isoformat(),
              'scope':'Literal membership, public annotations, state renaming and tape reflection. No complete behavioral-equivalence or literature search.',
              'sources':SOURCES,
              'input_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in inputs},
              'collection_sizes':{k:len(v) for k,v in collections.items()},
              'table_families_ignoring_initial_state':list(groups.values()),'leads':result}
    (ROOT/'census.json').write_text(json.dumps(output,indent=2)+'\n')
    for item in result:
        matches = [(m['collection'],m['rooted'],m['witness']['source_start_maps_to'])
                   for m in item['table_matches']]
        print(item['id'],item['literal_membership']['bb6_663'],matches)


if __name__ == '__main__':
    main()
