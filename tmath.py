#!/usr/bin/python
# -*- coding: utf-8 -*-
# Implementation of the mathemical set Q

class Q:
	def __init__(self):
		pass
	def plusID(self):
		return QElement(0,self)
	def plus(self,a,b):
		return QElement(a.value+b.value,self)
	def mulID(self):
		return QElement(1,self)
	def mul(self,a,b):
		return QElement(a.value*b.value,self)
	def longDiv(self,a,b):
		return [QElement(a.value/b.value,self),QElement(a.value%b.value,self)]
	def __str__(self):
		return "Q"
	def __repr__(self):
		return "Q"
	def newInstance(self):
		return self.plusID()

class QElement:
	def __init__(self,value,set):
		self.set=set
		self.value=value
	def __str__(self):
		return "%(v)f e %(s)s" % {'v':self.value, 's':self.set }
	def __repr__(self):
		return "%(v)f e %(s)s" % {'v':self.value, 's':self.set }
	def setValue(self, value):
		self.value = value
	def isPlusID(self):
		return self.value == 0
	def isMulID(self):
		return self.value == 1
	def plusInv(self):
		return QElement(-self.value,self.set)
	def mulInv(self):
		return QElement(float(1)/float(self.value),self.set)
	def clone(self):
		return QElement(self.value,self.set)

# Implementation of the mathemical set Z

class Z:
	def __init__(self,order):
		self.order = order
	def getOrder(self):
		return order
	def plusID(self):
		return ZElement(0,self)
	def plus(self,a,b):
		if a.set == b.set:
			return ZElement(a.value+b.value,self)
		else:
			raise Error, 'Trying to add ZElements from different Z classes'
	def mulID(self):
		return ZElement(1,self)
	def mul(self,a,b):
		return ZElement(a.value*b.value,self)
	def __str__(self):
		return "Z(%d)" % self.order
	def __repr__(self):
		return "Z(%d)" % self.order
	def newInstance(self):
		return self.plusID()

class ZElement:
	def __init__(self,value,set):
		self.set=set
#		self.value=type("",(object,),{'__set__': lambda self, obj, val: self.val = val%
		self.value=(value%set.order)
	def __str__(self):
		return "%(v)d" % {'v':self.value, 's':self.set }
#		return "%(v)d e %(s)s" % {'v':self.value, 's':self.set }
	def __repr__(self):
#		return "%(v)d e %(s)s" % {'v':self.value, 's':self.set }
		return "%(v)d" % {'v':self.value, 's':self.set }
	def setValue(self, value):
		self.value = (value%self.set.order)
	def isPlusID(self):
		return self.value == 0
	def isMulID(self):
		return self.value == 1
	def plusInv(self):
		return ZElement(self.set.order-self.value,self.set)
	def mulInv(self):
		return ZElement(self.value**(self.set.order-2),self.set)
	def clone(self):
		return ZElement(self.value,self.set)

# Implementation of a polynomial over an arbitrary field 
# POF=PolynomialOverField
class POF: 
	def __init__(self,field):
		self.field=field
	def plus(self,a,b):
		newp = a.clone()
		for i in b.nonZeroCoefficients():
			newp.setCoefficient(i,self.field.plus(newp.getCoefficient(i),b.getCoefficient(i)))
		return newp
	def mul(self,a,b):
                # Get new result polynomial with all zero coefficients.
		newp = self.newInstance()
		for k1 in a.nonZeroCoefficients():
			for k2 in b.nonZeroCoefficients():
				newp.setCoefficient(k1+k2,
                                                    # Add the existing value at this coefficient.
                                                    self.field.plus(
                                                            newp.getCoefficient(k1+k2),
					                    self.field.mul(
                                                                    a.getCoefficient(k1),
                                                                    b.getCoefficient(k2))))
		return newp
	def longDiv(self,a,b):
		reminder = a.clone()
		quotient = self.newInstance()
		field = self.field
		while not (reminder.getDegree() < b.getDegree()):
			q = field.mul(
                                b.getCoefficient(b.getDegree()).mulInv(),
                                reminder.getCoefficient(reminder.getDegree()))
			xtimes = reminder.getDegree() - b.getDegree()
			quotient.setCoefficient(xtimes, q)
			for k in b.nonZeroCoefficients():
				reminder.setCoefficient(k+xtimes,
                                                        field.plus(reminder.getCoefficient(k+xtimes),
                                                                   field.mul(b.getCoefficient(k),q).plusInv()))
		return [quotient, reminder]
	def newInstance(self):
		return POFElement(self)
	def plusID(self):
		return self.newInstance()
	def mulID(self):
		pofi = self.newInstance()
		pofi.setCoefficient(0, self.field.mulID())
		return pofi
		
class POFElement:
	def __init__(self,pof):
		self.pof=pof
		self.c = {}
	def setCoefficient(self,n,fieldinstance):
		if fieldinstance.isPlusID():
			if n in self.c:
				self.c.pop(n)
		else:
			self.c[n] = fieldinstance
	def getCoefficient(self,n):
		return self.c.get(n, self.pof.field.plusID())
	def getDegree(self):
		max = None
		for k in self.c.keys():
			if k > max:
				max = k
		return max
	def nonZeroCoefficients(self):
		return self.c.keys()
	def plusInv(self):
		newp = self.pof.newInstance()
		for i in self.nonZeroCoefficients():
			newp.setCoefficient(i,self.getCoefficient(i).plusInv())
		return newp
	def isPlusID(self):
		return self.nonZeroCoefficients() == []
	def isMulID(self):
		return self.nonZeroCoefficients() == [0]
	def __str__(self):
		return self.__repr__();
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
		clone=self.pof.newInstance()
		for i in self.nonZeroCoefficients():
			clone.setCoefficient(i,self.getCoefficient(i).clone())
		return clone

# Implementation of a Galious field 
		
class GFPOF(POF):
	def __init__(self,field,rp):
		POF.__init__(self,field)
		self.rp=rp
	def newInstance(self):
		return GFPOFElement(self)
	def mul(self,a,b):
		result = self.newInstance()
		field = self.field
		for b_p in range(b.getDegree(),-1,-1):
			result = self.xtime(result)
			for a_p in a.nonZeroCoefficients():
				result.setCoefficient(a_p,field.plus(result.getCoefficient(a_p),(field.mul(b.getCoefficient(b_p),a.getCoefficient(a_p)))))
#			for a_p in range(0, a.getDegree()+1):
#				result.setCoefficient(a_p,field.plus(result.getCoefficient(a_p),(field.mul(b.getCoefficient(b_p),a.getCoefficient(a_p)))))
		return result
	def xtime(self,a):
		result = self.newInstance()
		rp = self.rp
		downfactor = a.getCoefficient(rp.getDegree()-1)
		result.setCoefficient(0,self.field.mul(downfactor,rp.getCoefficient(0).plusInv()))
		for i in range(1,rp.getDegree()):
			result.setCoefficient(i,self.field.plus(a.getCoefficient(i-1),self.field.mul(downfactor,rp.getCoefficient(i)).plusInv()))
		return result
		
class GFPOFElement(POFElement):
	def __init__(self,pof):
		self.pof=pof
		self.c = {}
	def mulInv(self):
		return ExtEuclidean(POF(self.pof.field),self.pof.rp,self)[2]

def ExtEuclidean(field,a,b):
	n1 = a
	n2 = b
	[q,r]=field.longDiv(n1,n2)
	x0 = field.mulID()
	x1 = field.plusID()
	y0 = field.plusID()
	y1 = field.mulID()
#	print "n1:",n1," n2:",n2," q:",q," r:",r
	while not r.isPlusID():
		n1=n2
		n2=r
#		print "x1:", x1, "q:", q, "x0:", x0, "qx1: ", field.mul(q,x1)
		x2 = field.plus(x0,(field.mul(q,x1).plusInv()))
		y2 = field.plus(y0,(field.mul(q,y1).plusInv()))
		x0 = x1
		x1 = x2
		y0 = y1
		y1 = y2
		[q,r]=field.longDiv(n1,n2)
#		print "n1:",n1," n2:",n2," q:",q," r:",r, " x2: ", x2 #, " y2:",y2
	return [n2, x1, y1];

def toBin(a):
	r = []
	for i in range(0,8):
		r.append(a%2)
		a=a/2
	return r
def fromBin(a):
	r = 0
	try: 
		while True:
			r=r*2
			r=r+a.pop()
	except IndexError:
		pass
	return r/2
	
def EL2POL(a,pof):
	pofi=pof.newInstance()
	for i in range(0,len(a)):
		pofi.setCoefficient(i,a[i])
	return pofi
	
def L2EL(list,set):
	r = []
	for i in list:
		seti=set.newInstance()
		seti.setValue(i)
		r.append(seti)
	return r

def L2POL(a,set):
	return EL2POL(L2EL(a,set),POF(set))
	
def POL2EL(pofi):
	list = []
	if pofi.getDegree() == None:
		return list
	for i in range(0,pofi.getDegree()+1):
		list.append(pofi.pof.field.plusID())
	for i in pofi.nonZeroCoefficients():
		list[i] = pofi.getCoefficient(i)
	return list
	
def EL2L(list):
	newlist = []
	for i in range(0,len(list)):
		newlist.append(list[i].value)
	return newlist

def POL2L(pofi):
	return EL2L(POL2EL(pofi))

#if __name__ == '__main__':
#	for i in range(1,256):
#		inverse=fromBin(POL2L(ExtEuclidean(POFZ2,rps,L2POL(toBin(i),Z2))[2]))
#		inverseinverse=fromBin(POL2L(ExtEuclidean(POFZ2,rps,L2POL(toBin(inverse),Z2))[2]))
#		if not (inverseinverse == i):
#			print i, "not self inverse!"
