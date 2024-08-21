from Convert.AdditionalOperations import ExpandedCVC5
from Tools.Check import TypeCheck
from Tools.Errors import MyNoneError


class FrElement:
    def __init__(self, name, s_v, l_v, is_l, is_m):
        self.name = name
        self.s_v = s_v
        self.l_v = l_v
        self.is_l = is_l
        self.is_m = is_m

    __initiated = False
    __exp_slv = None
    FF_0 = None
    FF_1 = None

    @staticmethod
    def init(exp_slv):
        if not FrElement.__initiated:
            FrElement.__exp_slv = exp_slv
            FrElement.__initiated = True

    @staticmethod
    def construct_value(name):
        if FrElement.__exp_slv is None:
            MyNoneError('FrElement.slv')
        TypeCheck(str, name)

        s_v = FrElement.__exp_slv.mkConst(FrElement.__exp_slv.F(), f'{name}.s_v')
        l_v = FrElement.__exp_slv.mkConst(FrElement.__exp_slv.F(), f'{name}.l_v')
        is_l = FrElement.__exp_slv.mkConst(FrElement.__exp_slv.B(), f'{name}.is_l')
        is_m = FrElement.__exp_slv.mkConst(FrElement.__exp_slv.B(), f'{name}.is_m')
        return FrElement(name, s_v, l_v, is_l, is_m)

    @staticmethod
    def construct_value_bash(*names):
        elements = list()
        for name in names:
            elements.append(FrElement.construct_value(name))
        return elements

    @staticmethod
    def construct_constant(name: str, raw_s_v: int, raw_l_v: int, raw_type: int):
        TypeCheck(str, name)
        TypeCheck(int, raw_s_v)
        TypeCheck(int, raw_l_v)
        TypeCheck(int, raw_type)
        s_v = FrElement.__exp_slv.mkFiniteFieldElem(str(raw_s_v), FrElement.__exp_slv.F())
        l_v = FrElement.__exp_slv.mkFiniteFieldElem(str(raw_l_v), FrElement.__exp_slv.F())
        raw_is_l = (raw_type & 0x80000000) != 0
        raw_is_m = (raw_type & 0x40000000) != 0
        if raw_is_l:
            is_l = FrElement.__exp_slv.Boolean_True()
        else:
            is_l = FrElement.__exp_slv.Boolean_False()

        if raw_is_m:
            is_m = FrElement.__exp_slv.Boolean_True()
        else:
            is_m = FrElement.__exp_slv.Boolean_False()
        return FrElement(name, s_v, l_v, is_l, is_m)

