"""Noncryptographic admission/count controls; does not import Sage."""

import unittest

from metadata import CapExceeded, Caps, bounded_staircase, exponent_vectors, shift_row_count


class MetadataControls(unittest.TestCase):
    def test_finite_staircase_is_counted_exactly_at_the_cap(self):
        values = bounded_staircase([(2, 0), (0, 3)], 2, 6)
        self.assertEqual(set(values), {(i, j) for i in range(2) for j in range(3)})
        with self.assertRaises(CapExceeded):
            bounded_staircase([(2, 0), (0, 3)], 2, 5)

    def test_infinite_staircase_does_not_pass_admission(self):
        with self.assertRaises(CapExceeded):
            bounded_staircase([(1, 0)], 2, 20)
        with self.assertRaises(CapExceeded):
            bounded_staircase([], 2, 20)

    def test_large_degree_is_not_trusted_as_a_wrapped_scalar(self):
        with self.assertRaises(CapExceeded):
            bounded_staircase([(2**32+3,)], 1, 8)

    def test_unit_ideal_and_invalid_exponents(self):
        self.assertEqual(bounded_staircase([(0, 0)], 2, 8), [])
        with self.assertRaises(ValueError):
            bounded_staircase([(-1, 2)], 2, 8)

    def test_full_family_count_and_lazy_exponents(self):
        self.assertEqual(shift_row_count(2, 2, 2, 1), 18)
        values = list(exponent_vectors(3, 2))
        self.assertEqual(len(values), 10)
        self.assertEqual(len(set(values)), 10)
        self.assertTrue(all(len(e) == 3 and min(e) >= 0 and sum(e) <= 2 for e in values))

    def test_invalid_caps_are_rejected_before_a_worker(self):
        for values in ({"wall_seconds": True}, {"wall_seconds": 0},
                       {"wall_seconds": 3601}, {"unknown": 3}):
            with self.assertRaises(ValueError):
                Caps.parse(values)


if __name__ == "__main__":
    unittest.main()
