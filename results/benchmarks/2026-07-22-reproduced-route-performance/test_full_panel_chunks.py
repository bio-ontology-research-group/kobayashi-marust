#!/usr/bin/env python3

import importlib.util
from pathlib import Path
import unittest


MODULE_PATH = Path(__file__).with_name("full_panel_chunks.py")
SPEC = importlib.util.spec_from_file_location("full_panel_chunks", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
chunks = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(chunks)


class FullPanelChunksTest(unittest.TestCase):
    def test_ore_partition_has_exactly_thirty_balanced_chunks(self):
        ranges = [chunks.indices_for_chunk(592, 30, i) for i in range(30)]
        self.assertEqual([len(part) for part in ranges], [20] * 22 + [19] * 8)
        self.assertEqual([item for part in ranges for item in part], list(range(592)))

    def test_inverse_mapping(self):
        for chunk in range(30):
            for index in chunks.indices_for_chunk(592, 30, chunk):
                self.assertEqual(chunks.chunk_for_index(592, 30, index), chunk)

    def test_more_chunks_than_items(self):
        self.assertEqual(
            [list(chunks.indices_for_chunk(3, 5, chunk)) for chunk in range(5)],
            [[0], [1], [2], [], []],
        )
        self.assertEqual([chunks.chunk_for_index(3, 5, i) for i in range(3)], [0, 1, 2])

    def test_invalid_arguments_fail_closed(self):
        for arguments in ((-1, 1, 0), (1, 0, 0), (1, 1, -1), (1, 1, 1)):
            with self.subTest(arguments=arguments), self.assertRaises(ValueError):
                chunks.chunk_bounds(*arguments)
        with self.assertRaises(ValueError):
            chunks.chunk_for_index(1, 1, 1)


if __name__ == "__main__":
    unittest.main()
