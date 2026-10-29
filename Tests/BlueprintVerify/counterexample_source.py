"""Render the portable ToCEX tree as Haskell, preserving Plutus Data exactly.

Source type names are explicit codec hints, not inferred from display names.
Unknown types/constructors and incomplete values are rejected.
"""
import re

SOURCE_TYPES = {
    'PlutusLedgerApi.V3.ScriptContext': 'V3.ScriptContext',
    'PlutusLedgerApi.V3.TxInfo': 'V3.TxInfo',
    'PlutusLedgerApi.V3.ScriptInfo': 'V3.ScriptInfo',
}


def fields(value, names):
    fs = value.get('fields', [])
    if [f.get('name') for f in fs] != list(names):
        raise ValueError('Unexpected constructor fields')
    return [f['value'] for f in fs]


def integer(value):
    if value.get('kind') not in {'integer', 'natural'}:
        raise ValueError('Expected an integer value')
    raw = value.get('value')
    if not isinstance(raw, str) or not re.fullmatch(r'-?(0|[1-9][0-9]*)', raw):
        raise ValueError('Invalid integer literal')
    if value['kind'] == 'natural' and raw.startswith('-'):
        raise ValueError('Negative natural')
    return raw


def sequence(value):
    if value.get('kind') != 'list':
        raise ValueError('Expected a list')
    return value['values']


def bytes_literal(value):
    raw = value.get('hex')
    if value.get('kind') != 'bytes' or not isinstance(raw, str) or not re.fullmatch(r'(?:[0-9a-f]{2})*', raw):
        raise ValueError('Invalid byte encoding')
    return 'BS.pack [' + ', '.join(str(b) for b in bytes.fromhex(raw)) + ']'


def plutus_data(value):
    if value.get('kind') != 'constructor' or value.get('type') != 'PlutusCore.Data':
        raise ValueError('Expected canonical Plutus Data')
    ctor = value.get('constructor')
    if ctor == 'I':
        return 'V3.I (' + integer(fields(value, ['value'])[0]) + ')'
    if ctor == 'B':
        return 'V3.B (' + bytes_literal(fields(value, ['value'])[0]) + ')'
    if ctor == 'List':
        xs = sequence(fields(value, ['values'])[0])
        return 'V3.List [' + ', '.join(plutus_data(x) for x in xs) + ']'
    if ctor == 'Map':
        entries = sequence(fields(value, ['entries'])[0])
        pairs = []
        for pair in entries:
            if pair.get('type') != 'Prod' or pair.get('constructor') != 'Prod.mk':
                raise ValueError('Expected a map entry pair')
            k, v = fields(pair, ['fst', 'snd'])
            pairs.append('(' + plutus_data(k) + ', ' + plutus_data(v) + ')')
        return 'V3.Map [' + ', '.join(pairs) + ']'
    if ctor == 'Constr':
        tag, xs = fields(value, ['index', 'fields'])
        return 'V3.Constr (' + integer(tag) + ') [' + ', '.join(plutus_data(x) for x in sequence(xs)) + ']'
    raise ValueError('Unknown Plutus Data constructor')


def haskell_string(value):
    escapes = {'"': '\\"', '\\': '\\\\', '\n': '\\n', '\r': '\\r', '\t': '\\t'}
    return '"' + ''.join(escapes.get(c, c if 32 <= ord(c) <= 126 else f'\\x{ord(c):x}\\&') for c in value) + '"'


def haskell(value):
    kind = value.get('kind')
    if kind in {'integer', 'natural'}:
        return '(' + integer(value) + ' :: Integer)'
    if kind == 'boolean':
        if type(value['value']) is not bool:
            raise ValueError('Invalid Bool')
        return str(value['value'])
    if kind == 'string':
        return haskell_string(value['value'])
    if kind == 'unit':
        return '()'
    if kind == 'list':
        return '[' + ', '.join(haskell(v) for v in sequence(value)) + ']'
    if kind == 'encoded':
        if value.get('encoding') != 'plutus-data' or value.get('type') not in SOURCE_TYPES:
            raise ValueError('Unsupported source codec or source type')
        return '(decodeData @' + SOURCE_TYPES[value['type']] + ' (' + plutus_data(value['value']) + '))'
    if kind == 'constructor' and value.get('type') == 'Prod' and value.get('constructor') == 'Prod.mk':
        a, b = fields(value, ['fst', 'snd'])
        return '(' + haskell(a) + ', ' + haskell(b) + ')'
    if kind == 'constructor' and value.get('type') == 'Option':
        if value.get('constructor') == 'Option.none' and not value.get('fields'):
            return 'Nothing'
        if value.get('constructor') == 'Option.some':
            return '(Just ' + haskell(fields(value, ['value'])[0]) + ')'
    raise ValueError('No faithful Haskell constructor mapping for this value')


def context_replay_source(context, wire):
    if context.get('kind') != 'encoded' or context.get('type') != 'PlutusLedgerApi.V3.ScriptContext':
        raise ValueError('Expected a typed ScriptContext codec')
    # Compare canonical trees, not pretty-printed strings. A custom source codec
    # cannot describe a different script argument and still pass this check.
    if context.get('encoding') != 'plutus-data' or context['value'] != wire:
        raise ValueError('Source context differs from the replayed wire argument')
    return '''{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Main where
import Data.ByteString qualified as BS
import PlutusLedgerApi.V3 qualified as V3

-- Reconstructed with the real Haskell FromData instances; no guessed fields.
decodeData :: V3.FromData a => V3.Data -> a
decodeData d = case V3.fromData d of
  Just value -> value
  Nothing -> error "Counterexample source decode failed"

contextData :: V3.Data
contextData = ''' + plutus_data(wire) + '''

context :: V3.ScriptContext
context = ''' + haskell(context) + '''

main :: IO ()
main = if V3.toData context == contextData
  then do
    putStrLn "PASS Haskell ScriptContext decode and exact Data round trip"
    print context
  else error "Reconstructed Haskell context changed the script argument"
'''
