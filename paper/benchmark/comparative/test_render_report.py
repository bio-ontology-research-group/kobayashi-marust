import unittest
from render_report import validate_run_sets, PANEL_RUN_KEYS
from run_set import DEFAULT


class RunSelectionTests(unittest.TestCase):
    def reports(self):
        return {panel: {'run_set': dict(DEFAULT)} for panel in PANEL_RUN_KEYS}

    def test_mixed_runs_require_explicit_selection(self):
        reports = self.reports()
        reports['updates']['run_set']['retained_konclude'] = 'replacement'
        with self.assertRaises(AssertionError):
            validate_run_sets(reports)

    def test_replacing_updates_preserves_other_panels_historical_receipts(self):
        reports = self.reports()
        selected = dict(DEFAULT, retained_konclude='replacement')
        reports['updates']['run_set'] = dict(selected)
        self.assertEqual(validate_run_sets(reports, selected), selected)
        self.assertEqual(reports['classification']['run_set'], DEFAULT)

    def test_every_consumed_run_is_checked(self):
        for panel, keys in PANEL_RUN_KEYS.items():
            for key in keys:
                with self.subTest(panel=panel, key=key):
                    reports = self.reports()
                    reports[panel]['run_set'][key] = 'wrong'
                    with self.assertRaises(AssertionError):
                        validate_run_sets(reports, dict(DEFAULT))

    def test_partial_selection_rejected(self):
        with self.assertRaises(AssertionError):
            validate_run_sets(self.reports(), {'retained_konclude': 'replacement'})


if __name__ == '__main__':
    unittest.main()
