#!/usr/bin/env python3

from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from summarize_terminal_causes import cause


class TerminalCauseTest(unittest.TestCase):
    def test_known_failures_are_distinguished(self) -> None:
        self.assertEqual(cause("error", "worker engine exited -1: \n"),
                         "route_no_retry_internal_cap")
        self.assertEqual(cause("error", "unsupported: DL-safe rule contains a complex class atom"),
                         "unsupported_complex_rule_atom")
        self.assertEqual(cause("error", "unsupported: named role expected, got ObjectInverseOf(x)"),
                         "unsupported_inverse_role_position")
        self.assertEqual(cause("timeout", ""), "timeout")


if __name__ == "__main__":
    unittest.main()
