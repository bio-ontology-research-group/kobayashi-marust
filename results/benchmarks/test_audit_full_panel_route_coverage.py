#!/usr/bin/env python3

import unittest
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from audit_full_panel_route_coverage import environment, parse_binary_routes


class RouteCoverageAuditTest(unittest.TestCase):
    def test_binary_route_descriptions_are_ignored(self):
        self.assertEqual(
            parse_binary_routes("auto\tdefault router\nmanual\nht_bridge\tfaithful\n"),
            ["auto", "manual", "ht_bridge"],
        )

    def test_binary_routes_reject_duplicates_and_whitespace(self):
        with self.assertRaises(ValueError):
            parse_binary_routes("auto\nauto\n")
        with self.assertRaises(ValueError):
            parse_binary_routes("not a route\n")

    def test_environment_is_order_independent_and_rejects_duplicates(self):
        self.assertEqual(
            environment(["KM_THREADS=16", "KM_ROUTE=manual"]),
            environment(["KM_ROUTE=manual", "KM_THREADS=16"]),
        )
        with self.assertRaises(ValueError):
            environment(["KM_ROUTE=auto", "KM_ROUTE=manual"])


if __name__ == "__main__":
    unittest.main()
