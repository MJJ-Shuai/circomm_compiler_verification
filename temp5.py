import re

from z3 import *

if __name__ == '__main__':

    for i in range(5):
        print(i)
    pass
    # # 创建一个Z3求解器实例
    # solver = Solver()
    #
    # # 定义两个BitVec变量
    # a = BitVec('a', 256)  # 32位的位向量
    # b = BitVec('b', 256)  # 32位的位向量
    # r = BitVec('r', 256)  # 32位的位向量
    # p = 11
    #
    # # setting
    # Setting = And {0 <= f_a < p, 0 <= f_b < p, a,b}
    #
    # # FF
    # FF_constranits = r_1 == (f_a + f_b) % p
    #
    # # property
    # Fr_constraints = And{
    #     (a + b >= p) => r_2 == (a + b) - p,
    #     (a + b) => r_2 == a + b
    # }
    #
    # # 目标
    # target = And(a % p == f_a, b % p == f_b, (r_1 == r_2 % p))
    #
    # term = Setting and FF_constraints and Fr_constraints and Not(target)
    # unsat
    #
    # FF_a + FF_b
    # # 检查约束的可满足性
    # if solver.check() == sat:
    #     model = solver.model()
    #     print(model)
    # else:
    #     print("约束不可满足")