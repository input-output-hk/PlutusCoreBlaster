#!/usr/bin/env python3
"""Validate freshly generated example artifacts against local CIP schemas, offline."""
import argparse
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator, RefResolver


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cips', type=Path, required=True)
    parser.add_argument('examples', nargs='+', type=Path)
    args = parser.parse_args()
    store = {}
    for folder in ['CIP-0057/schemas', 'CIP-0057/extensions/compiled-interface/schemas',
                   'CIP-XXXX/schemas']:
        for path in (args.cips / folder).glob('*.json'):
            schema = json.loads(path.read_text())
            store[schema['$id']] = schema

    def reject_network(uri):
        raise ValueError('Unknown schema (network disabled): ' + uri)

    def load(path):
        doc = json.loads(path.read_text())
        if '$schema' in doc:
            schema = store[doc['$schema']]
            resolver = RefResolver.from_schema(
                schema, store=store, handlers={'http': reject_network, 'https': reject_network})
            Draft202012Validator(schema, resolver=resolver).validate(doc)
        return doc

    def artifact(folder, ref):
        path = (folder / ref['uri']).resolve()
        assert path.is_relative_to(folder.resolve()), 'Artifact escapes example directory'
        assert ref['hash']['alg'] == 'sha256'
        assert hashlib.sha256(path.read_bytes()).hexdigest() == ref['hash']['digest'], path
        return path

    for folder in args.examples:
        doc = load(folder / 'assurance.json')
        bp = load(artifact(folder, doc['blueprint']))
        validators = {v['id']: v for v in bp['validators']}
        for v in validators.values():
            tag = bytes([int(bp['preamble']['plutusVersion'][1:])])
            assert hashlib.blake2b(tag + bytes.fromhex(v['compiledCode']), digest_size=28).hexdigest() == v['hash']
        for fn in doc.get('functions', {}).values():
            assert fn['hash']['alg'] == 'sha256'
            assert hashlib.sha256(bytes.fromhex(fn['compiledCode'])).hexdigest() == fn['hash']['digest']
        for ref in doc['checkingContexts'].values():
            context = load(artifact(folder, ref))
            load(artifact(folder, context['environment']))
            for target in context['targets']:
                if 'function' in target:
                    fn = doc['functions'][target['function']]
                    interface = target['functionInterface']
                    assert target['functionHash'] == fn['hash']
                    for key in ['plutusVersion', 'serialization', 'arguments', 'result']:
                        assert interface[key] == fn[key], key
                    assert interface.get('definitions', {}) == doc.get('definitions', {})
                else:
                    assert target['validator'] in validators
                    parameters = target['parameters']
                    if parameters['mode'] == 'applied':
                        for value in parameters['values']:
                            artifact(folder, value['term'])
                        specialized = artifact(folder, parameters['appliedScript'])
                        tag = bytes([int(bp['preamble']['plutusVersion'][1:])])
                        assert hashlib.blake2b(tag + specialized.read_bytes(), digest_size=28).hexdigest() == parameters['appliedScriptHash']
        verified = folder / 'verified-assurance.json'
        if verified.exists():
            evidence_doc = load(verified)
            assert evidence_doc['blueprint'] == doc['blueprint']
            assert evidence_doc['checkingContexts'] == doc['checkingContexts']
            originals = {p['id']: p for p in doc['properties']}
            assert {p['id'] for p in evidence_doc['properties']} == set(originals)
            for prop in evidence_doc['properties']:
                original = originals[prop['id']]
                assert {k: v for k, v in prop.items() if k != 'evidence'} == {
                    k: v for k, v in original.items() if k != 'evidence'}
                for evidence in prop['evidence']:
                    assert evidence['checkingContextHash'] == doc['checkingContexts'][prop['checkingContext']]['hash']
                    artifact(folder, evidence['artifact'])
                    if 'scriptHash' in evidence:
                        assert evidence['scriptHash'] in [validators[v]['hash'] for v in prop['scope'].get('validators', [])]
                    for name, digest in evidence.get('functionHashes', {}).items():
                        assert digest == doc['functions'][name]['hash']
        print('PASS schemas and artifact bindings:', folder.name)


if __name__ == '__main__':
    main()
