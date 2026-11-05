import copy
import unittest

from counterexample_source import context_replay_source, haskell, plutus_data


def integer(n):
    return {'kind': 'integer', 'value': str(n)}


def node(name, **fields):
    return {'kind': 'constructor', 'type': 'PlutusCore.Data', 'constructor': name,
            'fields': [{'name': k, 'value': v} for k, v in fields.items()]}


class SourceTests(unittest.TestCase):
    def test_integer_precision_and_source_escaping(self):
        n = -(10 ** 100)
        self.assertEqual(haskell(integer(n)), f'({n} :: Integer)')
        self.assertEqual(haskell({'kind': 'string', 'value': '\x001f"\\'}), '"\\x0\\&1f\\"\\\\"')
        for raw in ['1); error "injected"', '1.0', '+1']:
            with self.assertRaises(ValueError):
                haskell({'kind': 'integer', 'value': raw})

    def test_plutus_data_preserves_map_order_and_bytes(self):
        pairs = [{'kind': 'constructor', 'type': 'Prod', 'constructor': 'Prod.mk',
                  'fields': [{'name': 'fst', 'value': node('I', value=integer(i))},
                             {'name': 'snd', 'value': node('B', value={'kind': 'bytes', 'hex': b})}]}
                 for i, b in [(2, '00e9ff'), (1, '')]]
        data = node('Map', entries={'kind': 'list', 'values': pairs})
        rendered = plutus_data(data)
        self.assertEqual(rendered, 'V3.Map [(V3.I (2), V3.B (BS.pack [0, 233, 255])), (V3.I (1), V3.B (BS.pack []))]')

    def test_source_context_must_match_replayed_wire_data(self):
        wire = node('I', value=integer(7))
        context = {'kind': 'encoded', 'type': 'PlutusLedgerApi.V3.ScriptContext',
                   'encoding': 'plutus-data', 'value': copy.deepcopy(wire)}
        self.assertIn('context :: V3.ScriptContext', context_replay_source(context, wire))
        context['value'] = node('I', value=integer(8))
        with self.assertRaisesRegex(ValueError, 'differs'):
            context_replay_source(context, wire)

    def test_unknown_codecs_and_constructors_never_generate_source(self):
        for value in [
            {'kind': 'unavailable', 'reason': 'unsupported'},
            {'kind': 'encoded', 'type': 'Unsafe.Unknown', 'encoding': 'plutus-data', 'value': node('I', value=integer(0))},
            {'kind': 'constructor', 'type': 'Unknown', 'constructor': 'mk', 'fields': []},
            {'kind': 'encoded', 'type': 'PlutusLedgerApi.V3.TxInfo', 'encoding': 'unknown', 'value': {}}]:
            with self.assertRaises(ValueError):
                haskell(value)
        with self.assertRaises(ValueError):
            plutus_data(node('Unknown'))


if __name__ == '__main__':
    unittest.main()
