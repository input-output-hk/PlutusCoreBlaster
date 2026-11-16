#!/usr/bin/env python3
"""Compare unchanged preparation with the proof-producing fold rule."""
import argparse
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / 'context-corpus'))
import run as corpus


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--cases', nargs='+', default=['withdrawals_sum', 'proposals_deposit'])
    p.add_argument('--fuel', nargs='+', type=int, default=[1000, 10000])
    p.add_argument('--engines', nargs='+', default=['baseline', 'fold'])
    p.add_argument('--timeout', type=int, default=30)
    p.add_argument('--output', default='results.jsonl')
    p.add_argument('--trace', action='store_true')
    args = p.parse_args()
    work = HERE / '.work'
    work.mkdir(exist_ok=True)
    cases = json.loads((corpus.HERE / 'cases.json').read_text())
    corpus.WORK.mkdir(exist_ok=True)
    metadata = corpus.artifacts(cases)
    cases = [c for c in cases if c['id'] in args.cases]
    assert len(cases) == len(args.cases)
    output = HERE / args.output
    output.write_text('')
    for case in cases:
        for engine in args.engines:
            for fuel in args.fuel:
                src = corpus.source(case, 'view', 'generic' if engine == 'fold' else 'baseline', fuel)
                if engine == 'fold':
                    src = src.replace('import PlutusCore.UPLC.Optimize.Extension',
                                      'import PlutusCore.UPLC.Optimize.FoldExtension')
                src = src.replace('let result := Json.mkObj [',
                    'let folded := constants.any (fun n => n.toString.startsWith "PlutusCore.UPLC.Optimize.foldPlan" || n.toString.startsWith "PlutusCore.UPLC.Optimize.CompiledFold.dataSummary")\n    let result := Json.mkObj [("kernel_closed", toJson true), ("fold", toJson folded), ')
                src = src.replace('    let constants := out.getUsedConstants',
                    '    if out.hasFVar || out.hasMVar then throwError "optimized output is not closed"\n'
                    '    let outputType ← inferType out\n'
                    '    withOptions (fun opts => opts.setBool `Elab.async false) do\n'
                    '      Lean.addDecl (.defnDecl { name := `foldCompilerClosedOutput, levelParams := [], type := outputType, value := out, hints := .abbrev, safety := .safe })\n'
                    '    let constants := out.getUsedConstants')
                if args.trace:
                    src = src.replace('run_cmd do', 'set_option trace.Optimize.compiledFold true\nset_option trace.Optimize.callbackCompiler true\nrun_cmd do')
                path = work / f'{case["id"]}-{engine}-{fuel}.lean'
                path.write_text(src)
                start = time.monotonic()
                with path.with_suffix('.log').open('w') as log:
                    proc = subprocess.Popen(['lake', 'lean', str(path), '--', '--threads=1', '--tstack=16384'],
                        cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
                    try:
                        proc.wait(timeout=args.timeout)
                        status = 'ok' if proc.returncode == 0 else 'error'
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                        status = 'timeout'
                    except BaseException:
                        os.killpg(proc.pid, signal.SIGKILL)
                        proc.wait()
                        raise
                text = path.with_suffix('.log').read_text()
                row = dict(case=case['id'], engine=engine, fuel=fuel, status=status,
                    wall_seconds=round(time.monotonic()-start, 3),
                    compiled_sha256=metadata[case['id']]['compiled_sha256'])
                match = re.search(r'CORPUS_RESULT (\{[^\n]+\})', text)
                if match:
                    row.update(json.loads(match[1]))
                if status == 'error':
                    row['error'] = text[-1500:]
                with output.open('a') as log:
                    log.write(json.dumps(row, separators=(',', ':'))+'\n')
                print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
