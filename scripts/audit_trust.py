"""Conservative source policy and explicit public-theorem axiom-output coverage.

This lexical/build-log check does not replace Lean's kernel or sandbox hostile
metaprograms. Comments and string literals are excluded from the source policy.
Every inventoried #print command and its output is required; extra output records
are also checked against the permitted axioms.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = {'axiom', 'sorry', 'admit', 'native_decide', 'sorryAx'}
IDENTIFIER = re.compile(r"[^\W\d][\w']*", re.UNICODE)
RAW_STRING = re.compile(r'r(#{0,})"')
CHAR_LITERAL = re.compile(r"'(?:\\.|[^'\\\n])'")
AXIOM_OUTPUT = re.compile(r"'([^\r\n]+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
REPOSITORY = Path(__file__).resolve().parent.parent


@dataclass(frozen=True)
class Token:
    value: str
    line: int


def lean_tokens(source: str) -> list[Token]:
    """Handle nested comments, escaped/raw strings and quoted identifiers."""
    tokens = []
    i, line, length = 0, 1, len(source)
    while i < length:
        start, first_line = i, line
        if source.startswith('--', i):
            end = source.find('\n', i)
            i = length if end < 0 else end
        elif source.startswith('/-', i):
            depth, i = 1, i + 2
            while i < length and depth:
                if source.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif source.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError(f'line {first_line}: unterminated block comment')
        elif source[i] == '"':
            i += 1
            while i < length and source[i] != '"':
                i += 2 if source[i] == '\\' else 1
            if i >= length:
                raise ValueError(f'line {first_line}: unterminated string')
            i += 1
        elif source[i] == '«':
            end = source.find('»', i + 1)
            if end < 0:
                raise ValueError(f'line {first_line}: unterminated quoted identifier')
            tokens.append(Token(source[i + 1:end], line))
            i = end + 1
        elif (raw := RAW_STRING.match(source, i)) is not None:
            closing = '"' + raw.group(1)
            end = source.find(closing, raw.end())
            if end < 0:
                raise ValueError(f'line {first_line}: unterminated raw string')
            i = end + len(closing)
        elif (identifier := IDENTIFIER.match(source, i)) is not None:
            tokens.append(Token(identifier.group(), line))
            i = identifier.end()
        else:
            # Identifier apostrophes were consumed above; skip character literals.
            char = CHAR_LITERAL.match(source, i)
            if char is not None:
                i += len(char.group())
            else:
                if source[i] in '#.':
                    tokens.append(Token(source[i], line))
                i += 1
        line += source.count('\n', start, i)
    return tokens


def printed_theorems(tokens: list[Token]) -> set[str]:
    names = set()
    for i in range(len(tokens) - 3):
        if [t.value for t in tokens[i:i + 3]] != ['#', 'print', 'axioms']:
            continue
        name, j = tokens[i + 3].value, i + 4
        while j + 1 < len(tokens) and tokens[j].value == '.':
            name += '.' + tokens[j + 1].value
            j += 2
        names.add(name)
    return names


def audit(root: Path, log: str, project: str, inventory: dict) -> tuple[list[str], int, int]:
    root = root.resolve()
    errors, source_tokens = [], {}
    files = sorted(p for p in root.rglob('*.lean') if '.lake' not in p.relative_to(root).parts)
    for path in files:
        try:
            tokens = lean_tokens(path.read_text(encoding='utf-8'))
        except (OSError, ValueError) as error:
            errors.append(f'{path.relative_to(root)}: {error}')
            continue
        source_tokens[path] = tokens
        for token in tokens:
            if token.value in FORBIDDEN:
                errors.append(f'{path.relative_to(root)}:{token.line}: forbidden {token.value}')
    try:
        entry = inventory['projects'][project]
        names, sources = entry['theorems'], entry['sources']
        if (not isinstance(names, list) or not names or
                not all(isinstance(n, str) and n for n in names) or len(set(names)) != len(names) or
                not isinstance(sources, list) or not sources or
                not all(isinstance(p, str) and p for p in sources)):
            raise ValueError('nonempty unique theorem names and source paths are required')
        expected, source_prints = set(names), set()
        for relative in sources:
            path = (root / relative).resolve()
            if not path.is_relative_to(root) or not path.exists():
                raise ValueError(f'missing/outside inventory source: {relative}')
            selected = [path] if path.is_file() else sorted(path.rglob('*.lean'))
            if not selected:
                raise ValueError(f'inventory source contains no Lean files: {relative}')
            for selected_path in selected:
                if selected_path not in source_tokens:
                    raise ValueError(f'inventory source was not scanned: {relative}')
                source_prints.update(printed_theorems(source_tokens[selected_path]))
        for name in sorted(expected - source_prints):
            errors.append(f'{project}: inventoried theorem has no #print axioms command: {name}')
        for name in sorted(source_prints - expected):
            errors.append(f'{project}: register #print axioms command in trust_inventory.json: {name}')
    except (KeyError, TypeError, ValueError) as error:
        return errors + [f'invalid trust inventory for {project}: {error}'], len(files), 0
    records = list(AXIOM_OUTPUT.finditer(log))
    if not records:
        errors.append('build log has no #print axioms output')
    observed = set()
    for match in records:
        name, axioms = match.groups()
        observed.add(name)
        extra = {a.strip() for a in (axioms or '').split(',') if a.strip()} - ALLOWED
        if extra:
            errors.append(f'{name}: non-standard axioms {sorted(extra)}')
    for name in sorted(expected - observed):
        errors.append(f'{project}: missing axiom output for inventoried theorem: {name}')
    return errors, len(files), len(expected & observed)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log', type=Path)
    parser.add_argument('--project', choices=('core', 'mathlib', 'link'))
    parser.add_argument('--root', type=Path, default=REPOSITORY)
    parser.add_argument('--inventory', type=Path, default=REPOSITORY / 'scripts/trust_inventory.json')
    args = parser.parse_args()
    project = args.project or (Path.cwd().name if Path.cwd().name in ('mathlib', 'link') else 'core')
    try:
        inventory = json.loads(args.inventory.read_text(encoding='utf-8'))
        errors, files, theorems = audit(args.root, args.log.read_text(encoding='utf-8'), project, inventory)
    except (OSError, ValueError) as error:
        print(f'trust audit failed: {error}')
        return 1
    if errors:
        print('\n'.join(errors))
        return 1
    print(f'trust audit OK: {files} Lean files scanned, {theorems} inventoried theorems covered, standard axioms only')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
