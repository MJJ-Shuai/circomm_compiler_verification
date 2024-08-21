import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    # 创建一个 Solver 对象
    slv = cvc5.Solver()
    slv.setOption("produce-models", "true")
    intSort = slv.getIntegerSort()
    F = slv.mkFiniteFieldSort('29')
    F_array = slv.mkArraySort(intSort, F)
    temp = slv.mkConst(F_array, 'temp')
    zero = slv.mkConst(intSort, 'zero')
    a = slv.mkConst(F, 'a')
    b = slv.mkConst(F, 'b')
    term = slv.mkTerm(Kind.EQUAL, a, b)
    slv.assertFormula(term)
    result = slv.checkSat()
    print(slv.getValue(a))



