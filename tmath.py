#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Copyright 2004, 2019, Clemens Fruhwirth <clemens@endorphin.org>


class Field(object):
  def plusID(self):
    raise NotImplementedError

  def plus(self, a, b):
    raise NotImplementedError

  def mulID(self):
    raise NotImplementedError

  def mul(self, a, b):
    raise NotImplementedError

  def longDiv(self, a, b):
    raise NotImplementedError

  def __str__(self):
    raise NotImplementedError

  def __repr__(self):
    raise NotImplementedError


class FieldElement(object):
  def __init__(self, field):
    self.field = field

  def isPlusID(self):
    return self == self.field.plusID()

  def isMulID(self):
    return self == self.field.mulID()

  def opN(self, n, neutral, op):
    """Applies op(self, op(self, ... op(self, neutral))) n-times"""

    # Assuming a binary operator "op", we create the operator lambda a: op1(self, a). Then we apply
    # op1 to neutral n-times as given by the scalar.
    #
    # The implementation here uses the double-and-add algorithm to optimize this to log_n steps.

    f = self.field
    res = neutral
    # This variable will double every step and whenever we hit a "true"-bit add itself to res.
    w = self
    while n:
      if n % 2:
        res = op(res, w)
      w = op(w, w)
      n = n/2
    return res

  def scalarMul(self, scalar):
    """Scalar multiplication"""
    return self.opN(scalar, self.field.plusID(), self.field.plus)

  def scalarPow(self, scalar):
    """Scalar power"""
    return self.opN(scalar, self.field.mulID(), self.field.mul)

  def __eq__(self, other):
    raise NotImplementedError


class Z(Field):
  """Implementation of the mathemical set Z/nZ."""
  def __init__(self, order):
    super(Z, self).__init__()
    self.order = order

  def getOrder(self):
    return order

  def plusID(self):
    return ZElement(0, self)

  def plus(self, a, b):
    if a.field == b.field:
      return ZElement(a.value + b.value, self)
    else:
      raise Error, 'Trying to add ZElements from different Z classes'

  def mulID(self):
    return ZElement(1, self)

  def mul(self, a, b):
    return ZElement(a.value * b.value, self)

  def __str__(self):
    return "Z(%d)" % self.order

  def __repr__(self):
    return "Z(%d)" % self.order

  def fromInt(self, i):
    return ZElement(i, self)


class ZElement(FieldElement):
  def __init__(self, value, field):
    super(ZElement, self).__init__(field)
    self.value = value % field.order

  def __str__(self):
    return "%(v)d" % {'v':self.value, 's':self.field }

  def __repr__(self):
    return "%(v)d" % {'v':self.value, 's':self.field }

  def setValue(self, value):
    self.value = value % self.field.order
    return self

  def plusInv(self):
    return ZElement(self.field.order - self.value, self.field)

  def mulInv(self):
    return ZElement(self.value ** (self.field.order - 2), self.field)

  def clone(self):
    return ZElement(self.value, self.field)

  def __eq__(self, a):
    return self.value == a.value


class POF(Field):
  """Implementation of a polynomial over an arbitrary field.

  POF=PolynomialOverField
  """
  def __init__(self, field):
    super(POF, self).__init__()
    self.field = field

  def plus(self, a, b):
    newp = a.clone()
    for i in b.nonZeroCoefficients():
      newp.addToCoefficient(i, b.getCoefficient(i))
    return newp

  def mul(self, a, b):
    # Get new result polynomial with all zero coefficients.
    newp = self.plusID()
    for k1 in a.nonZeroCoefficients():
      for k2 in b.nonZeroCoefficients():
        newp.addToCoefficient(
          k1 + k2, self.field.mul(
            a.getCoefficient(k1),
            b.getCoefficient(k2)))
    return newp

  def longDiv(self, dividend, divisor):
    """Divides dividend by divisor."""

    # Divides
    #   a_n x^n + a_n-1 x^n-1 + a_n-2 x^n-2 + ... + a_1 x + a_0
    # by
    #   b_m x^m + b_m-1 x^m-1 + b_m-2 x^m-2 + ... + b_1 x + b_0
    # This works as long as n >= m
    #
    # Let's assume that we want to divide
    # 6 x^4 + 2 x^3 + 9 x^2 + x + 3    by
    #                 2 x^2 +   + 7
    # The difference in the highest degrees (x^4 vs x^2). So the quotient
    # polynomial will have a coefficient for x^2. To find out what coefficient
    # it is, we do a field division and find that have 6/2 = 3. We multiply
    # the rest of the division polynomial by 3 and subtract it.
    # We end up at up:
    #   6 x^4 + 2 x^3 +  9 x^2 + x + 3 (original polynomial)
    # subtracted by
    #   6 x^4 +       + 21 x^2         (divisor multiplied by 3 x^2)
    # ending in:
    #   2 x^3 - 12 x^2 + x + 3         (potential reminder)
    # and we accumulate 3 x^2 in the quotient polynomial.
    #
    # We repeat the game, find that the highest degree difference has
    # shrunk to 1 (x^3 vs x^2) multiply the divisor by 3/2 and
    # subtract again. Once the potential reminder has a lower degree
    # than the divisor, we stop.
    #
    # The algorithm below is built on that illustration. xtimes is the
    # difference in the polynomial degree, while q is the quotient
    # between the coefficients of the highest degrees.
    #
    # We start off with the whole dividend as potential reminder
    reminder = dividend.clone()
    quotient = self.plusID()

    while not (reminder.getDegree() < divisor.getDegree()):
      xtimes = reminder.getDegree() - divisor.getDegree()
      q = self.field.mul(divisor.getCoefficient(divisor.getDegree()).mulInv(),
                         reminder.getCoefficient(reminder.getDegree()))
      # Accumulate coefficient in quotient.
      quotient.setCoefficient(xtimes, q)
      for k in divisor.nonZeroCoefficients():
        # Subtract shifted divisor polynomial
        reminder.addToCoefficient(
          k + xtimes,
          self.field.mul(divisor.getCoefficient(k), q).plusInv())
    return (quotient, reminder)

  def plusID(self):
    return POFElement(self)

  def mulID(self):
    return self.plusID().setCoefficient(0, self.field.mulID())

  def fromEL(self, lst):
    """Create polynomial from field coefficient list."""
    pofi = self.plusID()
    for i in range(0, len(lst)):
      pofi.setCoefficient(i, lst[i])
    return pofi

class POFElement(FieldElement):
  def __init__(self, pof):
    super(POFElement, self).__init__(pof)
    self.pof = pof
    self.c = {}

  def setCoefficient(self, n, c):
    """Sets coefficient of x^n."""
    if c.isPlusID():
      if n in self.c:
        self.c.pop(n)
    else:
      self.c[n] = c
    return self

  def getCoefficient(self, n):
    return self.c.get(n, self.pof.field.plusID())

  def addToCoefficient(self, n, i):
    return self.setCoefficient(n, self.pof.field.plus(self.getCoefficient(n), i))

  def getDegree(self):
    max = None
    for k in self.c.keys():
      if k > max:
        max = k
    return max

  def nonZeroCoefficients(self):
    return self.c.keys()

  def plusInv(self):
    newp = self.pof.plusID()
    for i in self.nonZeroCoefficients():
      newp.setCoefficient(i, self.getCoefficient(i).plusInv())
    return newp

  def __str__(self):
    return self.__repr__()

  def __repr__(self):
    es = ""
    keys = self.c.keys()
    keys.sort()
    for k in keys:
      cof = self.getCoefficient(k)
      if not cof.isMulID() or k == 0 :
        es = es + cof.__str__()
      if(k > 0):
        es = es + " x"
        if(k > 1):
          es = es + "^" + k.__str__()
      es = es + " + "
    if es == "":
      return self.pof.field.plusID().__str__()
    else:
      return es[:-3]

  def clone(self):
    clone = self.pof.plusID()
    for i in self.nonZeroCoefficients():
      clone.setCoefficient(i, self.getCoefficient(i).clone())
    return clone

  def __eq__(self, other):
    return self.c == other.c

  def toEL(self):
    """Get coefficient list in underlying field from polynomial."""
    # FIXME: This seems horribly complicated.
    list = []
    if self.getDegree() == None:
      return list
    for i in range(0, self.getDegree() + 1):
      list.append(self.pof.field.plusID())
    for i in self.nonZeroCoefficients():
      list[i] = self.getCoefficient(i)
    return list

class GFPOF(POF):
  """Implementation of a Galois field."""
  def __init__(self, field, rp):
    # Field is coefficent field.
    super(GFPOF, self).__init__(field)
    self.rp = rp

  def plusID(self):
    return GFPOFElement(self)

  def mul(self, a, b):
    """Multiplies two polynomials and applies the reduction polynomial."""

    # We classically think about polynomial multiplication as:
    #
    # (a_3 x^3 + a_2 x^2 + a_1 x + a_0) * (b_3 x^3 + b_2 x^2 + b_1 x + b_0) as
    # (a_3 x^3 + a_2 x^2 + a_1 x + a_0) *  b_3 x^3 +
    # (a_3 x^3 + a_2 x^2 + a_1 x + a_0) *  b_2 x^2 +
    # (a_3 x^3 + a_2 x^2 + a_1 x + a_0) *  b_1 x   +
    # (a_3 x^3 + a_2 x^2 + a_1 x + a_0) *  b_0
    #
    # As the A-polynomial does not change in this, let's abbreviate it with A:
    #
    # A * b_3 x^3 +
    # A * b_2 x^2 +
    # A * b_1 x   +
    # A * b_0
    #
    # An equivalent from is:
    #
    # (((0 * x + A * b_3) * x + A * b_2) * x + A * b_1) * x + A * b_0)
    #
    # Writing this as lisp S-expression makes the bracketing structure more
    # visible:
    #
    # (+ (* x (+ (* x (+ (* x (+ (* x 0)
    #                            (* A b_3))
    #                    (* A b_2))
    #            (* A b_1))
    #    (* A b_0))
    #
    # The recursive nature of this expression becomes visible, and it is
    # generated by the following
    #
    # T = (+ (* x T')
    #        (* A b_n)
    #
    # where T' is the previous iteration starting with off with 0.
    #
    # The multiplication with of T' with x is the xtime algorithm, which takes
    # care of polynomial reduction. The multiplication with a coefficient of b
    # and the addition can not cause the polynomial to shift to a higher degree.
    #
    # The following algorithm implements this idea.
    #
    # FIXME: Lift this into the superclass POF and give the superclass an xtime
    #        implementation, as this algorithm is not GF specific.

    result = self.plusID()
    for b_p in range(b.getDegree(), -1, -1):
      result = self.xtime(result)
      for a_p in a.nonZeroCoefficients():
        result.addToCoefficient(
          a_p,
          self.field.mul(b.getCoefficient(b_p),
                         a.getCoefficient(a_p)))
    return result

  def xtime(self, a):
    """Multiplies the polynomial by x.

    It is a building block of the multiplication algorithm mul.
    """
    result = self.plusID()

    # The polynomial
    #   a_n x^n     + a_{n-1} x^{n-1} + ... + a_1 x   + a_0
    # gets multiplied by x resulting in
    #   a_n x^{n+1} + a_{n-1} x^n     + ... + a_1 x^2 + a_0 x
    # ... essentially shifting the coefficients by one index higher.
    #
    # The resulting polynomial needs to be reduced by the reduction
    # polynomial. The following loop subtracts the reduction
    # polynomial a_n times from the result, and also shifts the
    # indices.

    # Get the highest coefficient of the reduction polynomial, and
    # subtract the reduction polynomial a_n times from a.
    a_n = a.getCoefficient(self.rp.getDegree()-1)
    for i in range(0, self.rp.getDegree()):
      result.setCoefficient(
        i,
        self.field.plus(
          # Get plusID from the underlying field for the lowest
          # coefficient
          a.getCoefficient(i-1) if i else self.field.plusID(),
          self.field.mul(a_n,
                         self.rp.getCoefficient(i)).plusInv()))
    return result


class GFPOFElement(POFElement):
  def __init__(self, pof):
    super(GFPOFElement, self).__init__(pof)
    self.pof = pof
    self.c = {}

  def setCoefficient(self, n, c):
    if n >= self.pof.rp.getDegree():
      raise ValueError("can't set coefficient larger than the reduction polynomial's degree.")
    return super(GFPOFElement, self).setCoefficient(n, c)

  def mulInv(self):
    return ExtEuclidean(POF(self.pof.field), self.pof.rp, self)[2]


def ExtEuclidean(field, a, b):
  """Extended Euclidean algorithm."""
  n1 = a
  n2 = b
  (q, r) = field.longDiv(n1, n2)
  x0 = field.mulID()
  x1 = field.plusID()
  y0 = field.plusID()
  y1 = field.mulID()
#  print "n1:",n1," n2:",n2," q:",q," r:",r
  while not r.isPlusID():
    n1 = n2
    n2 = r
#    print "x1:", x1, "q:", q, "x0:", x0, "qx1: ", field.mul(q,x1)
    x2 = field.plus(x0, (field.mul(q, x1).plusInv()))
    y2 = field.plus(y0, (field.mul(q, y1).plusInv()))
    x0 = x1
    x1 = x2
    y0 = y1
    y1 = y2
    (q, r) = field.longDiv(n1, n2)
#    print "n1:",n1," n2:",n2," q:",q," r:",r, " x2: ", x2 #, " y2:",y2
  return [n2, x1, y1];

def toBin(a):
  """Integer to list of binary values."""
  r = []
  for i in range(0, 8):
    r.append(a%2)
    a = a/2
  return r

def fromBin(a):
  """List of binary values to integer."""
  r = 0
  try:
    while True:
      r = r*2
      r = r+a.pop()
  except IndexError:
    pass
  return r/2

def L2EL(lst, field):
  """List of raw values to a list of field elements."""
  return [field.fromInt(x) for x in lst]

def L2POL(a, field):
  """Create polynomial from raw coefficient list in field."""
  return POF(field).fromEL(L2EL(a, field))

def EL2L(lst):
  """List of field elements to list of raw values."""
  return [x.value for x in lst]

def POL2L(pofi):
  """Polynomial to list of raw values of its coefficients."""
  return EL2L(pofi.toEL())

