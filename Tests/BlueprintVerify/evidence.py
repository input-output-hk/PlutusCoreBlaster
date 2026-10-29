"""Publish fresh evidence only after a runner's positive and negative checks pass."""
import copy
from datetime import datetime, timezone
import hashlib
from pathlib import Path
import subprocess


def digest(path):
    return {'alg': 'sha256', 'digest': hashlib.sha256(Path(path).read_bytes()).hexdigest()}


def provenance(repo, generator, runner):
    """Bind source annotations as well as the exact executable checking inputs."""
    plutus = next((p for p in generator.parents if (p / 'plutus-tx').is_dir()), None)
    sources = [Path(runner), Path(__file__), Path(__file__).with_name("runtime.py")]
    sources += list((repo / 'PlutusCore/UPLC/BlueprintEncoding').glob('*.lean'))
    sources += list((repo / 'PlutusCore/UPLC/BlueprintEncoding').glob('*.schema.json'))
    repositories = {'checker': repo}
    if plutus:
        repositories['plutus'] = plutus
        example = generator.name.removeprefix('example-ual-').capitalize()
        sources += list((plutus / 'doc/docusaurus/static/code/Example/Ual' / example).glob('*.hs'))
        sources += [plutus / 'plutus-tx/src/PlutusTx/Assurance/Interface.hs']
    revisions = {}
    for name, root in repositories.items():
        commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
        patch = subprocess.check_output(['git', '-c', 'core.fsmonitor=false', 'diff', 'HEAD', '--binary'], cwd=root)
        revisions[name] = {'commit': commit, 'trackedDiffSha256': hashlib.sha256(patch).hexdigest()}
    return {'repositories': revisions, 'sources': {str(p): digest(p) for p in sources}}


def verified_document(doc, bp, report_hash, notes):
    verified = copy.deepcopy(doc)
    verified.setdefault('tools', {})['blaster'] = {'name': 'Blaster', 'version': 'loaded-environment'}
    validators = {v['id']: v for v in bp['validators']}
    for prop in verified['properties']:
        evidence = {'method': 'smt-check', 'verifier': 'Blaster', 'tool': 'blaster',
                    'outcome': 'verified', 'date': datetime.now(timezone.utc).date().isoformat(),
                    'checkingContextHash': doc['checkingContexts'][prop['checkingContext']]['hash'],
                    'artifact': {'uri': 'run-report.json', 'hash': report_hash}, 'notes': notes}
        targets = prop['scope'].get('validators', [])
        if targets:
            if len(targets) != 1:
                raise ValueError('This evidence writer requires one scoped validator per property')
            evidence['scriptHash'] = validators[targets[0]]['hash']
        functions = prop['scope'].get('functions', [])
        if functions:
            evidence['functionHashes'] = {name: doc['functions'][name]['hash'] for name in functions}
        prop['evidence'] = [evidence]
    return verified
