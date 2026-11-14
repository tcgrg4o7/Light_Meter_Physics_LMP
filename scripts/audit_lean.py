#!/usr/bin/env python3
"""Conservative checks for this repository's simple Lean companion format.

This is a repository lint, not a Lean parser or an adversarial sandbox. Lean's
kernel and dependency reports check proofs; review checks statement fidelity.
Unsupported declaration/scope syntax fails rather than silently losing coverage.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

ALLOWED_AXIOMS = frozenset({'propext', 'Classical.choice', 'Quot.sound'})
NAME = r'[A-Za-z_][A-Za-z0-9_\']*(?:\.[A-Za-z_][A-Za-z0-9_\']*)*'
FORBIDDEN = re.compile(r'\b(?:sorry|admit|sorryAx|axiom|axioms|constant|constants|unsafe|native_decide|implemented_by|extern|macro|elab|syntax|initialize|run_elab)\b')


class AuditError(ValueError):
    pass


def strip_comments_strings(source: str) -> str:
    """Mask nested block comments, line comments and strings; retain newlines."""
    out = list(source)
    i = 0
    depth = 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif source.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if source[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if source[i] == '\\':
                out[i] = ' '; i += 1
                if i < len(source):
                    if source[i] != '\n': out[i] = ' '
                    i += 1
            else:
                ch = source[i]
                if ch != '\n': out[i] = ' '
                i += 1
                if ch == '"': string = False
        elif source.startswith('--', i):
            while i < len(source) and source[i] != '\n':
                out[i] = ' '; i += 1
        elif source.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif source[i] == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise AuditError('Unterminated comment or string')
    return ''.join(out)


def qualified(name: str, scopes: list[tuple[str, str]]) -> str:
    namespace = '.'.join(n for kind, n in scopes if kind == 'namespace')
    # Fully qualified audit names are accepted when rooted in the active namespace.
    if namespace and not name.startswith(namespace + '.'):
        return namespace + '.' + name
    return name


def inspect_source(path: Path) -> set[str]:
    code = strip_comments_strings(path.read_text(encoding='utf-8'))
    scopes: list[tuple[str, str]] = []
    declarations: set[str] = set()
    audits: set[str] = set()
    for line_no, line in enumerate(code.splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        where = f'{path}:{line_no}'
        audit = re.fullmatch(r'#print\s+axioms\s+(' + NAME + r')', line)
        if audit:
            name = qualified(audit[1], scopes)
            if name in audits:
                raise AuditError(f'{where}: duplicate axiom audit for {name}')
            audits.add(name)
            continue
        if re.search(r'#print\s+axioms', line):
            raise AuditError(f'{where}: unsupported axiom-audit syntax')
        bad = FORBIDDEN.search(line)
        if bad:
            raise AuditError(f'{where}: disallowed token {bad[0]}')
        if line.startswith('#'):
            raise AuditError(f'{where}: unsupported command; only #print axioms is permitted')
        namespace = re.fullmatch(r'namespace\s+(' + NAME + r')', line)
        section = re.fullmatch(r'(?:noncomputable\s+)?section(?:\s+(' + NAME + r'))?', line)
        end = re.fullmatch(r'end(?:\s+(' + NAME + r'))?', line)
        if namespace:
            scopes.append(('namespace', namespace[1])); continue
        if section:
            scopes.append(('section', section[1] or '')); continue
        if end:
            if not scopes:
                raise AuditError(f'{where}: unmatched end')
            _, name = scopes.pop()
            if end[1] and end[1] != name:
                raise AuditError(f'{where}: mismatched end {end[1]} (expected {name})')
            continue
        if re.match(r'(?:namespace|section|end|noncomputable\s+section)\b', line):
            raise AuditError(f'{where}: unsupported scope syntax')
        decl = re.match(r'^(?:theorem|lemma)\s+(' + NAME + r')(?=\s|\(|\{|:|$)', line)
        if re.search(r'\b(?:theorem|lemma)\b', line):
            if not decl or len(re.findall(r'\b(?:theorem|lemma)\b', line)) != 1:
                raise AuditError(f'{where}: unsupported theorem/lemma syntax')
            name = qualified(decl[1], scopes)
            if name in declarations:
                raise AuditError(f'{where}: duplicate declaration {name}')
            declarations.add(name)
    if scopes:
        raise AuditError(f'{path}: unclosed namespace/section')
    if declarations != audits:
        raise AuditError(f'{path}: audit mismatch; missing={sorted(declarations-audits)}, '
                         f'unexpected={sorted(audits-declarations)}')
    return declarations


def inspect_project(project: Path) -> set[str]:
    if not project.is_dir():
        raise AuditError(f'Not a project directory: {project}')
    # Ignore downloaded/build dependencies, and reject source symlinks.
    files = sorted(p for p in project.rglob('*.lean')
                   if not any(part.startswith('.') for part in p.relative_to(project).parts))
    if not files:
        raise AuditError(f'{project}: no Lean source files')
    names: set[str] = set()
    for path in files:
        if path.is_symlink():
            raise AuditError(f'Source symlinks are unsupported: {path}')
        found = inspect_source(path)
        if names & found:
            raise AuditError(f'Duplicate declarations across modules: {sorted(names & found)}')
        names |= found
    if not names:
        raise AuditError(f'{project}: no theorem/lemma declarations')
    return names


def inspect_log(log: str, expected: set[str]) -> None:
    reports: set[str] = set()
    # Direct `lake env lean` output, optionally with normal Lean info prefixes.
    pattern = re.compile(r"'(" + NAME + r")' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$")
    for line in log.splitlines():
        if 'sorryAx' in line or re.search(r'\berror:', line):
            raise AuditError('Lean log contains an error or sorryAx')
        match = pattern.search(line)
        if not match:
            if 'depends on axioms:' in line or 'does not depend on any axioms' in line:
                raise AuditError(f'Unrecognized axiom report: {line}')
            continue
        name = match[1]
        axioms = {a.strip() for a in (match[2] or '').split(',') if a.strip()}
        if axioms - ALLOWED_AXIOMS:
            raise AuditError(f'{name}: unapproved axioms {sorted(axioms-ALLOWED_AXIOMS)}')
        if name not in expected:
            raise AuditError(f'Unexpected axiom report for {name}')
        reports.add(name)
    if reports != expected:
        raise AuditError(f'Missing Lean axiom reports: {sorted(expected-reports)}')


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    source = sub.add_parser('source', help='check source declarations and audit coverage')
    source.add_argument('project', type=Path)
    log = sub.add_parser('log', help='check source and captured Lean axiom output')
    log.add_argument('project', type=Path)
    log.add_argument('log', type=Path)
    args = parser.parse_args()
    try:
        names = inspect_project(args.project)
        if args.mode == 'log':
            inspect_log(args.log.read_text(encoding='utf-8'), names)
        print(f'Audit passed: {len(names)} theorem/lemma declarations in {args.project}'
              + ('; all axiom reports approved' if args.mode == 'log' else ''))
        return 0
    except (AuditError, OSError) as exc:
        print(f'Audit failed: {exc}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
