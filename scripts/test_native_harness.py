"""Source/product mutations must never reuse another native dependency build."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import native_harness as harness


class NativeHarness(unittest.TestCase):
    def test_binding_rejects_source_and_build_product_drift(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            package = root/'lean-kernel'
            package.mkdir()
            source = package/'QleisliKernel.lean'
            source.write_text('def x := 1')
            product = package/'.lake/build/lib/lean/QleisliKernel.olean'
            product.parent.mkdir(parents=True)
            product.write_bytes(b'compiled')
            library = package/'.lake/build/lib/kernel.a'
            library.write_bytes(b'native')
            binding = root/'build.json'
            with patch.multiple(harness, ROOT=root, PACKAGE=package, LIBRARY=library), patch.object(harness, 'run', return_value='Lean 4.30.0') as run, patch.object(harness.subprocess, 'check_output', return_value='Lean 4.30.0'):
                harness.prepare(binding, [])
                self.assertEqual(sum(call.args[0][:2] == ['lake','build'] for call in run.call_args_list), 1)
                harness.validate(binding)
                with self.assertRaisesRegex(ValueError, 'existing'):
                    harness.prepare(binding, [])
                for path in [source, product, library]:
                    original = path.read_bytes()
                    path.write_bytes(original + b'changed')
                    with self.assertRaises(ValueError):
                        harness.validate(binding)
                    path.write_bytes(original)
                extra = product.with_name('Injected.olean')
                extra.write_bytes(b'extra')
                with self.assertRaisesRegex(ValueError, 'products'):
                    harness.validate(binding)

    def test_bound_driver_compilation_does_not_rebuild_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            (project/'Main.lean').write_text('def main : IO Unit := pure ()')
            data = {'products': {str(harness.LIBRARY.relative_to(harness.ROOT)): 'hash'}}
            def run(command, *args):
                (project/'native-test').write_bytes(b'fresh driver')
                return ''
            with patch.dict('os.environ', {harness.BUILD_ENV: str(project/'binding.json')}), patch.object(harness, 'validate', return_value=data), patch.object(harness, 'run', side_effect=run) as commands:
                harness.build(project, [])
                self.assertFalse(any(call.args[0][:2] == ['lake','build'] for call in commands.call_args_list))
                self.assertEqual(len(commands.call_args_list), 2)


if __name__ == '__main__':
    unittest.main()
