#!/usr/bin/env python3
"""Regression and negative tests for the companion lint (no Lean needed)."""
import tempfile
import unittest
from pathlib import Path

from audit_lean import AuditError, inspect_log, inspect_project, inspect_source, strip_comments_strings

GOOD = '''import Mathlib
namespace Test
noncomputable section
theorem example_ok : True := by trivial
#print axioms example_ok
end
end Test
'''


class AuditTests(unittest.TestCase):
    def check_source(self, text):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Test.lean'
            path.write_text(text)
            return inspect_source(path)

    def test_source_success(self):
        self.assertEqual(self.check_source(GOOD), {'Test.example_ok'})

    def test_comments_nested_and_strings(self):
        self.assertEqual(self.check_source('/- sorry /- axiom fake -/ -/\n-- admit\n' + GOOD), {'Test.example_ok'})
        self.assertNotIn('sorry', strip_comments_strings('def label := "sorry \\" axioms"'))

    def test_unterminated(self):
        for text in ['/- no ending', 'def label := "oops']:
            with self.subTest(text=text), self.assertRaises(AuditError):
                self.check_source(text)

    def test_reject_unfinished_and_axioms(self):
        for word in ['sorry', 'admit', 'sorryAx', 'native_decide', 'unsafe', 'axiom', 'constant', 'macro', 'elab']:
            with self.subTest(word=word), self.assertRaises(AuditError):
                self.check_source(GOOD.replace('trivial', word))

    def test_missing_audit(self):
        with self.assertRaises(AuditError):
            self.check_source(GOOD.replace('#print axioms example_ok', ''))

    def test_unexpected_audit(self):
        with self.assertRaises(AuditError):
            self.check_source(GOOD.replace('#print axioms example_ok', '#print axioms other'))

    def test_lemma_supported(self):
        self.assertEqual(self.check_source(GOOD.replace('theorem', 'lemma')), {'Test.example_ok'})

    def test_unsupported_declaration_formats(self):
        for prefix in ['private theorem', '@[simp] theorem', 'theorem\n', 'protected theorem']:
            with self.subTest(prefix=prefix), self.assertRaises(AuditError):
                self.check_source(GOOD.replace('theorem', prefix))

    def test_unsupported_name(self):
        with self.assertRaises(AuditError):
            self.check_source(GOOD.replace('example_ok', '«special name»'))

    def test_bad_scope(self):
        for text in [GOOD.replace('end Test', 'end Wrong'), GOOD.replace('end Test', ''), 'end\n'+GOOD]:
            with self.subTest(text=text), self.assertRaises(AuditError):
                self.check_source(text)

    def test_duplicate_audit(self):
        with self.assertRaises(AuditError):
            self.check_source(GOOD.replace('#print axioms example_ok', '#print axioms example_ok\n#print axioms example_ok'))

    def test_log_success(self):
        inspect_log("'Test.example_ok' depends on axioms: [propext, Classical.choice, Quot.sound]\n", {'Test.example_ok'})
        inspect_log("'Test.example_ok' does not depend on any axioms\n", {'Test.example_ok'})

    def test_log_missing(self):
        with self.assertRaises(AuditError):
            inspect_log('Build completed successfully.', {'Test.example_ok'})

    def test_log_unapproved(self):
        for axiom in ['sorryAx', 'customAxiom', 'Lean.ofReduceBool']:
            with self.subTest(axiom=axiom), self.assertRaises(AuditError):
                inspect_log(f"'Test.example_ok' depends on axioms: [{axiom}]", {'Test.example_ok'})

    def test_log_error_even_if_audit_passes(self):
        with self.assertRaises(AuditError):
            inspect_log("error: failed\n'Test.example_ok' depends on axioms: []", {'Test.example_ok'})

    def test_log_unexpected_and_malformed(self):
        for text in ["'Other.x' depends on axioms: []", "'Test.example_ok' depends on axioms: [unterminated"]:
            with self.subTest(text=text), self.assertRaises(AuditError):
                inspect_log(text, {'Test.example_ok'})

    def test_project_empty(self):
        with tempfile.TemporaryDirectory() as tmp, self.assertRaises(AuditError):
            inspect_project(Path(tmp))

    def test_project_ignores_dependency_cache(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'Test.lean').write_text(GOOD)
            (root / '.lake').mkdir()
            (root / '.lake/Dependency.lean').write_text('axiom forbidden : False')
            self.assertEqual(inspect_project(root), {'Test.example_ok'})


if __name__ == '__main__':
    unittest.main()
