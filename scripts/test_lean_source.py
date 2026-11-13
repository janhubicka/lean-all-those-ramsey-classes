#!/usr/bin/env python3
"""Regressions for source-based import reachability and comment handling."""
import unittest

from lean_source import executable_text, imports_from_code, lean_imports


class LeanSourceTests(unittest.TestCase):
    def test_nested_comments_and_strings_are_not_imports(self):
        source = (
            "import Real.One Real.Two -- import Fake.Line\n"
            "/- import Fake.Block /- import Fake.Nested -/ -/\n"
            'def s := "import Fake.String"\n'
            "-- import Fake.Comment\n"
            "import Real.Three\n"
        )
        self.assertEqual(
            lean_imports(source),
            ["Real.One", "Real.Two", "Real.Three"],
        )

    def test_imports_follow_end_of_block_comment(self):
        self.assertEqual(
            lean_imports("/- inert -/ import Actual.Module\n"),
            ["Actual.Module"],
        )

    def test_escaped_quote_does_not_expose_import(self):
        self.assertEqual(
            lean_imports('def s := "text \\" import Fake.String"\nimport Real.Module\n'),
            ["Real.Module"],
        )

    def test_malformed_unclosed_source_rejected(self):
        with self.assertRaises(ValueError):
            executable_text("/- unfinished")
        with self.assertRaises(ValueError):
            executable_text('def s := "unfinished')

    def test_comment_cannot_forge_contract_hypothesis(self):
        header = (
            "theorem claimed\n"
            "  -- (hFreeK : GlobalCanonicalShadowFreeAmalgamation F K)\n"
            "  (hActual : True) : True := by\n"
        )
        self.assertNotIn(
            "hFreeK : GlobalCanonicalShadowFreeAmalgamation",
            executable_text(header),
        )

    def test_admission_words_in_comments_and_strings_are_inert(self):
        source = (
            "/- A proof explanation may admit that an argument is conditional. -/\n"
            "-- sorry is also harmless in a comment\n"
            'def commentText := "admit sorry axiom"\n'
            "theorem actualProof : True := by\n"
            "  trivial\n"
        )
        code = executable_text(source)
        self.assertNotIn("admit", code)
        self.assertNotIn("sorry", code)
        self.assertNotIn("axiom", code)
        self.assertIn("theorem actualProof", code)

    def test_unrecognised_import_syntax_rejected(self):
        with self.assertRaises(ValueError):
            imports_from_code("import Valid.Module (Invalid)")

    def test_plain_imports(self):
        self.assertEqual(
            lean_imports("import Alpha\nimport Beta.Gamma\n"),
            ["Alpha", "Beta.Gamma"],
        )


if __name__ == "__main__":
    unittest.main()
