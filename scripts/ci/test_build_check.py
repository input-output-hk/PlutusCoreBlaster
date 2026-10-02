#!/usr/bin/env python3
"""Exercise failure propagation and source selection without installing Lean."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

CHECKER = Path(__file__).resolve().parents[1] / 'check_lean_project_compilation.sh'


class BuildCheckTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'Tests/Conformance').mkdir(parents=True)
        for name in ['Tests.lean', 'Tests/Basic.lean', 'Tests/Orphan.lean',
                     'Tests/Conformance.lean', 'Tests/Conformance/Case.lean']:
            (self.root / name).write_text('-- fixture\n')
        (self.root / 'bin').mkdir()
        lake = self.root / 'bin/lake'
        lake.write_text('#!/usr/bin/env bash\nprintf "%s\\n" "$@" > invocation\n'
                        'echo "cached build output without a Built line"\n'
                        'exit "${LAKE_STATUS:-0}"\n')
        lake.chmod(0o755)
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + ':' + os.environ['PATH'])

    def run_check(self, *args, status=0):
        return subprocess.run(['bash', str(CHECKER), *args], cwd=self.root,
                              env=dict(self.env, LAKE_STATUS=str(status)),
                              capture_output=True, text=True)

    def test_cached_success_and_unimported_module(self):
        self.assertEqual(self.run_check('Tests').returncode, 0)
        invocation = (self.root / 'invocation').read_text().splitlines()
        self.assertIn('+Tests.Orphan', invocation)
        self.assertIn('+Tests', invocation)
        self.assertTrue((self.root / '.ci-results/build/Tests.log').exists())
        self.assertTrue((self.root / 'build.log').exists())

    def test_lake_failure_survives_successful_tee(self):
        self.assertNotEqual(self.run_check('Tests', status=37).returncode, 0)
        self.assertIn('cached build', (self.root / 'build.log').read_text())

    def test_excludes_subtree_and_barrel_but_not_similar_prefix(self):
        (self.root / 'Tests/ConformanceExtra.lean').write_text('-- fixture')
        self.assertEqual(self.run_check('Tests', './Tests/', './Tests/Conformance/').returncode, 0)
        invocation = (self.root / 'invocation').read_text().splitlines()
        self.assertNotIn('+Tests.Conformance', invocation)
        self.assertNotIn('+Tests.Conformance.Case', invocation)
        self.assertIn('+Tests.ConformanceExtra', invocation)

    def test_invalid_or_empty_selection_fails(self):
        for args in [(), ('Missing',), ('Tests', 'Tests', 'Tests'), ('Tests', 'Tests', '', 'extra')]:
            with self.subTest(args=args):
                self.assertNotEqual(self.run_check(*args).returncode, 0)

    def test_dotted_target_keeps_its_barrel(self):
        self.assertEqual(self.run_check('Tests.Conformance', 'Tests/Conformance').returncode, 0)
        self.assertIn('+Tests.Conformance', (self.root / 'invocation').read_text().splitlines())


if __name__ == '__main__':
    unittest.main()
