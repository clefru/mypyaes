from tmath import *

import unittest

class TmathTests(unittest.TestCase):
  def test_self_inverse(self):
    # Residue class 2 field
    Z2 = Z(2)

    # Polynomial over field Z2
    POFZ2 = POF(Z2)
    # Reduction polynomial in POFZ2 as defined by Page 36 of the Rijndael book. MAGIC
    rp = L2POL([1, 1, 0, 1, 1, 0, 0, 0, 1], Z2)
  
    # Galois field over Z2 with reduction polynomial
    GFPOFZ2 = GFPOF(Z2, rp)

    for i in range(1, 256):
      inverse=fromBin(POL2L(ExtEuclidean(POFZ2, rp, L2POL(toBin(i), Z2))[2]))
      inverseinverse=fromBin(POL2L(
        ExtEuclidean(POFZ2, rp, L2POL(toBin(inverse), Z2))[2]))
      self.assertEqual(inverseinverse, i)

if __name__ == '__main__':
    unittest.main()
