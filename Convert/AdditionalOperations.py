import cvc5
from cvc5 import Kind

from Tools.Check import TypeCheck
from Tools.ColorPrint import colorPrint, COLOR


class ExpandedCVC5:
    prime_dic = {'bn128': 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001,
                 'bls12381': 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001,
                 'goldilocks': 0xffffffff00000001,
                 'grumpkin': 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47,
                 'secq256r1': 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff,
                 'pallas': 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001,
                 'vesta': 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001}

    def __init__(self, prime_name):
        TypeCheck(str, prime_name)
        prime = ExpandedCVC5.prime_dic[prime_name]
        self.__prime = prime
        self.__slv = cvc5.Solver()
        self.__slv.setOption("produce-models", "true")
        self.__F = self.__slv.mkFiniteFieldSort(prime)
        self.__B = self.__slv.getBooleanSort()
        self.__FF_zero = self.FF_number(0)
        self.__FF_one = self.FF_number(1)
        self.__FFS_Compare = self.__slv.mkFunctionSort([self.__F, self.__F], self.__B)      # 比较元素
        self.__FFF_Gt = self.__slv.mkConst(self.__FFS_Compare, 'FFF_Gt')

    def prime(self):
        return self.__prime

    def slv(self):
        return self.__slv

    def F(self):
        return self.__F

    def B(self):
        return self.__B

    def FF_number(self, num):   # num : int or String
        return self.__slv.mkFiniteFieldElem(num, self.__F)

    def FF_zero(self):
        return self.__FF_zero

    def FF_one(self):
        return self.__FF_one

    def Boolean_True(self):
        return self.__slv.mkTrue()

    def Boolean_False(self):
        return self.__slv.mkFalse()

    def FF_const(self, name):
        TypeCheck(str, name)
        return self.__slv.mkConst(self.__F, name)

    def Bool_const(self, name):
        TypeCheck(str, name)
        return self.__slv.mkConst(self.__B, name)

    def mkTerm(self, kind_or_op, *args):
        return self.__slv.mkTerm(kind_or_op, *args)

    def mkConst(self, Sort_sort, symbol=None):
        return self.__slv.mkConst(Sort_sort, symbol)

    def mkFiniteFieldElem(self, value, Sort_sort, int_base=10):
        return self.__slv.mkFiniteFieldElem(value, Sort_sort, int_base)

    def assertFormula(self, Term_term):
        self.__slv.assertFormula(Term_term)

    def push(self):
        self.__slv.push()

    def pop(self):
        self.__slv.pop()

    def checkSat(self):
        return self.__slv.checkSat()

    def getValue(self, term_or_list):
        return self.__slv.getValue(term_or_list)

    def mkFFTerm_Eq(self, a, b):
        return self.mkTerm(Kind.EQUAL, a, b)

    def mkFFTerm_Neq(self, a, b):
        Eq = self.mkFFTerm_Eq(a, b)
        return self.mkTerm(Kind.NOT, Eq)

    def mkFFTerm_Gt(self, a, b):
        Neq = self.mkFFTerm_Neq(a, b)
        raw_gt = self.mkTerm(Kind.APPLY_UF, self.__FFF_Gt, a, b)
        return self.mkTerm(Kind.AND, Neq, raw_gt)

    def mkFFTerm_Ge(self, a, b):
        Gt = self.mkFFTerm_Gt(a, b)
        Eq = self.mkFFTerm_Eq(a, b)
        return self.mkTerm(Kind.OR, Gt, Eq)

    def mkFFTerm_Lt(self, a, b):
        Ge = self.mkFFTerm_Ge(a, b)
        return self.mkTerm(Kind.NOT, Ge)

    def mkFFTerm_Le(self, a, b):
        Gt = self.mkFFTerm_Gt(a, b)
        return self.mkTerm(Kind.NOT, Gt)

    def get_model(self, signals, show=False):
        r = self.__slv.checkSat()
        outcome = list()
        if not r.isSat():
            if show:
                colorPrint('UNSAT', COLOR.RED)
            return ('UNSAT', outcome)
        else:
            if show:
                colorPrint('SAT', COLOR.GREEN)
            for signal in signals:
                value = self.getValue(signal.toSmt())
                item = f'{signal.id_name} == {value}'
                outcome.append(item)
                if show:
                    colorPrint(item)
            return ('SAT', outcome)

    # 考察两个式子的等价性
    def check_equality(self, terms_A, terms_B, signals=None):
        self.push()
        if len(terms_A) > 1:
            exp_A = self.mkTerm(Kind.AND, *terms_A)
        else:
            exp_A = terms_A[0]

        if len(terms_B) > 1:
            exp_B = self.mkTerm(Kind.AND, *terms_B)
        else:
            exp_B = terms_B[0]
        aim_property = self.mkTerm(Kind.AND,
                                   self.mkTerm(Kind.IMPLIES, exp_A, exp_B),
                                   self.mkTerm(Kind.IMPLIES, exp_B, exp_A))
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and signals != None:
            self.get_model(signals, True)
        self.pop()
        return outcome

    # 考察两个式子的等价性
    def check_equality_with_settings(self, terms_A, terms_B, setting_terms, signals=None):
        self.push()
        if len(terms_A) > 1:
            exp_A = self.mkTerm(Kind.AND, *terms_A)
        else:
            exp_A = terms_A[0]

        if len(terms_B) > 1:
            exp_B = self.mkTerm(Kind.AND, *terms_B)
        else:
            exp_B = terms_B[0]
        aim_property = self.mkTerm(Kind.AND,
                                   self.mkTerm(Kind.IMPLIES, exp_A, exp_B),
                                   self.mkTerm(Kind.IMPLIES, exp_B, exp_A))
        for term in setting_terms:
            self.assertFormula(term)
        neg_property = self.mkTerm(Kind.NOT, aim_property)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and signals != None:
            self.get_model(signals, True)
        self.pop()
        return outcome

# 考察两个式子的等价性
    def check_satisfy_with_settings(self, terms, setting_terms, signals=None):
        self.push()
        if len(terms) > 1:
            exp = self.mkTerm(Kind.AND, *terms)
        else:
            exp = terms[0]
        for term in setting_terms:
            self.assertFormula(term)
        neg_property = self.mkTerm(Kind.NOT, exp)
        self.assertFormula(neg_property)
        outcome = not self.checkSat().isSat()
        if not outcome and signals != None:
            self.get_model(signals, True)
        self.pop()
        return outcome
