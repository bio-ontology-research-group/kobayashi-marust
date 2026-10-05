import unittest
from external_deletion import minimize

class DeletionTests(unittest.TestCase):
    def test_alternative_support_is_subset_minimal(self):
        oracle=lambda ids: {0,1}.issubset(ids) or 2 in ids
        support,_=minimize(4,oracle)
        self.assertTrue(oracle(support))
        for index in support:self.assertFalse(oracle([i for i in support if i!=index]))

    def test_oracle_timeout_is_not_treated_as_nonentailment(self):
        def oracle(ids):
            if len(ids)==2:return True
            raise TimeoutError('oracle timed out')
        with self.assertRaises(TimeoutError):minimize(2,oracle)

    def test_unknown_answer_rejects_explanation(self):
        with self.assertRaises(ValueError):minimize(1,lambda ids:None)

if __name__=='__main__':unittest.main()
