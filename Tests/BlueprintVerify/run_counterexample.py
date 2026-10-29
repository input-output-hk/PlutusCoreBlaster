#!/usr/bin/env python3
"""Exercise typed SMT -> ToCEX -> Plinth counterexamples using compiled outbids.

The generator is reused unchanged. Only a copied PROPERTY annotation is mutated;
no verification evidence is attached to the original, correct Haskell source.
"""
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

from runtime import lean_command


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def run(command, cwd, log, expected=0):
    result = subprocess.run(list(map(str, command)), cwd=cwd, text=True,
                            capture_output=True, timeout=180)
    log.write_text(result.stdout + result.stderr)
    if result.returncode != expected:
        raise RuntimeError(f'{log}: expected exit {expected}, got {result.returncode}\n'
                           + result.stdout + result.stderr)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generator', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True,
                        help='Auction FormalSpec.hs containing outbids_exact')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--z3', type=Path, required=True)
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=True)
    args.generator = args.generator.resolve(strict=True)
    args.source = args.source.resolve(strict=True)
    os.environ['PATH'] = str(args.z3.resolve(strict=True).parent) + os.pathsep + os.environ['PATH']
    core = Path(__file__).resolve().parents[2]
    lean = lean_command()
    header = 'import PlutusCore.UPLC.BlueprintEncoding.Assurance\n'
    driver = args.output / 'Environment.lean'
    environment = args.output / 'environment.json'
    driver.write_text(header + '#write_checking_environment ' + json.dumps(str(environment)) + '\n')
    run(lean + [driver], core, args.output / 'environment.log')
    run([args.generator, environment.name], args.output, args.output / 'generator.log')
    assurance = json.loads((args.output / 'assurance.json').read_text())
    selected = [p for p in assurance['properties'] if p['id'] == 'outbids_exact']
    if len(selected) != 1:
        raise RuntimeError('Expected exactly one compiled outbids_exact property')
    assurance['properties'] = selected
    # The helper claim needs only its generated UPLC wrapper. Other Auction
    # properties use V3 fragments; none is needed by this isolated helper test.
    selected[0]['statement']['formal']['uses'] = []
    assurance['formalFragments'] = []
    assurance['functions'] = {'outbids': assurance['functions']['outbids']}
    original = args.source.read_text()
    block = re.search(r'\{-@\s*PROPERTY\s+\[scope:\s*outbids\]\s+outbids_exact\b[\s\S]*?@-\}', original)
    if not block or block.group().count('old < proposed') != 1:
        raise RuntimeError('Unexpected outbids source annotation')
    false_block = block.group().replace('old < proposed', 'old > proposed')
    mutated = original[:block.start()] + false_block + original[block.end():]
    source = args.output / 'FormalSpec.hs'
    source.write_text(mutated)

    for label in ['correct', 'false']:
        claim = copy.deepcopy(assurance)
        formal = claim['properties'][0]['statement']['formal']
        if label == 'false':
            if formal['source'].count('old < proposed') != 1:
                raise RuntimeError('Unexpected generated formal proposition')
            formal['source'] = formal['source'].replace('old < proposed', 'old > proposed')
        claim_file = args.output / f'{label}.json'
        report_file = args.output / f'{label}-report.json'
        report_file.unlink(missing_ok=True)
        write(claim_file, claim)
        driver = args.output / f'{label.capitalize()}.lean'
        driver.write_text(header + '#verify_blueprint Cex ' + json.dumps(str(claim_file))
                          + ' cex_report ' + json.dumps(str(report_file)) + '\n')
        run(lean + [driver], core, args.output / f'{label}.log', 0 if label == 'correct' else 1)
        report = json.loads(report_file.read_text())
        if report['assuranceSha256'] != sha256(claim_file):
            raise RuntimeError('Report does not bind to the checked claim')
        if report['blueprintSha256'] != sha256(args.output / 'plutus.json'):
            raise RuntimeError('Report does not bind to the compiled blueprint')
        result = report['results'][0]
        if result['outcome'] != ('verified' if label == 'correct' else 'falsified'):
            raise RuntimeError(f'Unexpected verdict: {result}')
        if label == 'false':
            replay = result['counterexample']['replay']
            if replay['status'] != 'confirmed' or replay['propertyHolds']:
                raise RuntimeError(f'Counterexample did not replay: {replay}')
            bindings = result['counterexample']['model']['bindings']
            values = {}
            for binding in bindings:
                if binding['error'] or binding['value']['kind'] != 'integer':
                    raise RuntimeError(f'Incomplete reconstruction: {binding}')
                values[binding['name']] = binding['value']['value']
            if set(values) != {'old', 'proposed'}:
                raise RuntimeError(f'Unexpected helper inputs: {values}')
            execution = replay['execution']
            if execution['state'] != 'Halt' or execution['actual'] == execution['expected']:
                raise RuntimeError(f'Compiled helper execution does not contradict the claim: {execution}')
            haskell = '\n'.join(f'{name} = ({values[name]} :: Integer)' for name in ['old', 'proposed'])
            haskell += '\n\n-- Compiled outbids: ' + str(execution['actual'])
            haskell += '\n-- Property expected: ' + str(execution['expected']) + '\n'
            (args.output / 'counterexample.hs').write_text(haskell)
            result.update({'source': str(source), 'sourceSha256': sha256(source),
                           'originalSource': str(args.source), 'originalSourceSha256': sha256(args.source),
                           'generatorSha256': sha256(args.generator),
                           'report': str(report_file), 'reportSha256': sha256(report_file),
                           'haskell': haskell})
            write(args.output / 'counterexample.json', result)
            write(args.output / 'property-result.json', {
                'property': 'outbids_exact', 'outcome': 'falsified',
                'source': str(source), 'sourceSha256': sha256(source),
                'method': 'Blaster SMT with typed reconstruction and confirmed CEK replay',
                'counterexample': {name: f'{value} :: Integer' for name, value in values.items()},
                'structuredCounterexample': result['counterexample'],
                'haskell': haskell, 'log': str(args.output / 'false.log'),
            })
            print(haskell)
    print('PASS correct claim, falsified mutation, typed reconstruction and compiled-helper replay')
    print('Artifact:', args.output / 'counterexample.json')


if __name__ == '__main__':
    main()
