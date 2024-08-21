import cvc5
from cvc5 import Kind

if __name__ == "__main__":
    # 创建一个 Solver 对象
    slv = cvc5.Solver()
    slv.setOption("produce-models", "true")
    intSort = slv.getIntegerSort()
    boolSort = slv.getBooleanSort()
    F = slv.mkFiniteFieldSort("5")

    # 声明两个整数变量和一个布尔变量
    x = slv.mkConst(F, "x")
    y = slv.mkConst(F, "y")
    z = slv.mkConst(F, "z")
    ret_x = slv.mkConst(boolSort, "ret_x")
    ret_y = slv.mkConst(boolSort, "ret_y")

    compare = slv.mkFunctionSort([F, F], boolSort)

    # 声明未定义函数，接受两个整数参数，返回一个布尔值
    f = slv.mkConst(compare, 'f')

    f_x = slv.mkTerm(Kind.APPLY_UF, f, x, z)
    f_y = slv.mkTerm(Kind.APPLY_UF, f, y, z)

    slv.assertFormula(slv.mkTerm(Kind.EQUAL, f_x, ret_x))
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, f_y, ret_y))
    slv.assertFormula(slv.mkTerm(Kind.EQUAL, x, y))

    target = slv.mkTerm(Kind.EQUAL, ret_x, ret_y)
    not_target = slv.mkTerm(Kind.NOT, target)

    slv.assertFormula(target)

    # 检查是否有解
    r = slv.checkSat()
    print(r)

    # 获取解决方案（如果有）
    if r.isSat():
        print(f'x == {slv.getValue(x)}')
        print(f'y == {slv.getValue(y)}')
        print(f'f_x == {slv.getValue(f_x)}')
        print(f'f_y == {slv.getValue(f_y)}')

    R2 = 0x0216d0b17f4e44a58c49833d53bb808553fe3ab1e35c59e31bb8e645ae216da7
    half = 0x183227397098d014dc2822db40c0ac2e9419f4243cdcb848a1f0fac9f8000000
    R3 = 0x0cf8594b7fcc657c893cc664a19fcfed2a489cbe1cfbb6b85e94d8e1b4bf0040
    q = 0x30644e72e131a029b85045b68181585d2833e84879b9709143e1f593f0000001
    lboMask = 0x3fffffffffffffff
    np = 0xc2e1f593efffffff

    print((R2 * R2 * R2) % q - (R3 * R3) % q)
    print((half + half + 1) % q)
    print((R2 * np) % q)
    print(q)
    print(q - 21888242871839275222246405745257275088548364400416034343698204186575808495616)
