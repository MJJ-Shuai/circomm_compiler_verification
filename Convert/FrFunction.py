from cvc5 import Kind
import re
from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Directory.FrElement import FrElement
from Tools.Check import TypeCheck
from Tools.ValueDeal import reverse_pairs


class FrFunction:

    def __init__(self, exp_slv):
        self.__exp_slv = exp_slv
        FrElement.init(self.__exp_slv)
        self.R = self.__exp_slv.FF_number(
            66521454376583106372151021801275821387139285237984299765396891955339289339)  # is that right?
        self.R2 = self.__exp_slv.FF_number(14726038781183911426970757956966674445174170689807202100147381253709995623)
        self.p = self.__exp_slv.FF_number(21888242871839275222246405745257275088548364400416034343698204186575808495617)
        self.Rr_int = 9915499612839321149637521777990102151350674507940716049588462388200839649614
        self.p_int = 21888242871839275222246405745257275088548364400416034343698204186575808495617
        self.directory_terms = list()
        self.signal_map = {}
        self.element_dict = {}
        self.int_dict = {}
        self.constants_dict = {}
        self.my_signal_start = 1
        self.function_name_dict = {}
        self.function_line_dict = {}
        self.start_position_dict = {}
        self.current_aux_create = None
        self.current_cmp_index_ref = None
        self.is_running_subfunction = False
        self.go_subfunction_line = None
        self.value_to_subfunction = None

    def Fr_Copy(self, r: FrElement, a: FrElement):
        copy_s = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, a.s_v)
        copy_l = self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, a.l_v)
        copy_if_l = self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, a.is_l)
        copy_if_m = self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, a.is_m)
        fr_copy = self.__exp_slv.mkTerm(Kind.AND, copy_s, copy_l, copy_if_l, copy_if_m)
        return fr_copy

    def add_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        fr_addl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ml2m

    def add_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_addl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b_m.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ml2n

    def add_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_addl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1nl2m

    def add_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        fr_addl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_addl1nl2n

    def add_l1ms2m(self, r: FrElement, a: FrElement, b: FrElement):
        fr_addl1ms2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ms2m

    def add_l1ms2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_addl1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b_m.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ms2n

    def add_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        fr_addl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                        b.s_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_addl1ns2

    def add_s1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        fr_adds1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_adds1ml2m

    def add_s1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_addl1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_addl1ms2n

    def add_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        fr_adds1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.s_v,
                                                                                        b.l_v)),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_adds1l2n

    def add_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        up = self.__exp_slv.FF_number(2 ** 31 - 1)
        down = self.__exp_slv.FF_number(-2 ** 31)
        sum_ab = a.s_v + b.s_v
        condition1_1 = self.__exp_slv.mkFFTerm_Gt(down, sum_ab)
        condition1_2 = self.__exp_slv.mkFFTerm_Gt(sum_ab, up)
        condition2_1 = self.__exp_slv.mkFFTerm_Ge(sum_ab, down)
        condition2_2 = self.__exp_slv.mkFFTerm_Ge(up, sum_ab)

        condition1 = self.__exp_slv.mkTerm(Kind.AND, condition1_1, condition1_2)
        condition2 = self.__exp_slv.mkTerm(Kind.AND, condition2_1, condition2_2)

        result_1 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, sum_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_s, self.__exp_slv.Boolean_False())
                                         )
        result_2 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, sum_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_s, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                         )
        fr_adds1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2)
                                           )

        return fr_adds1s2

    def Fr_add(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        self.add_l1ml2m(r, a, b)
                    else:
                        self.add_l1ml2n(r, a, b)
                else:
                    if b.is_m == self.__exp_slv.Boolean_True():
                        self.add_l1nl2m(r, a, b)
                    else:
                        self.add_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                if b.is_m == self.__exp_slv.Boolean_True():
                    self.add_l1ms2m(r, a, b)
                else:
                    self.add_l1ms2n(r, a, b)
            else:
                self.add_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    self.add_s1ml2m(r, a, b)
                else:
                    self.add_s1nl2m(r, a, b)
            else:
                self.add_s1l2n(r, a, b)
        else:
            self.add_s1s2(r, a, b)

    def sub_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        fr_subl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINI, a.l_v, b.l_v)),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ml2m

    def sub_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_subl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b_m.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ml2n

    def sub_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_subl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1nl2m

    def sub_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        fr_subl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                             )

        return fr_subl1nl2n

    def sub_l1ms2m(self, r: FrElement, a: FrElement, b: FrElement):
        fr_subl1ms2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ms2m

    def sub_l1ms2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        fr_subl1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b_m.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subl1ms2n

    def sub_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        fr_subl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                        self.__exp_slv.mkTerm(
                                                                                            Kind.FINITE_FIELD_NEG,
                                                                                            b.s_v))),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_subl1ns2

    def sub_s1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        fr_subs1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subs1ml2m

    def sub_s1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        fr_subs1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                   r.l_v,
                                                                   self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a_m.l_v,
                                                                                         self.__exp_slv.mkTerm(
                                                                                             Kind.FINITE_FIELD_NEG,
                                                                                             b.l_v))),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                             )

        return fr_subs1nl2m

    def sub_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        fr_subs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                  r.l_v,
                                                                  self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, a.s_v,
                                                                                        self.__exp_slv.mkTerm(
                                                                                            Kind.FINITE_FIELD_NEG,
                                                                                            b.l_v))),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                            self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False())
                                            )

        return fr_subs1l2n

    def sub_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        up = self.__exp_slv.FF_number(2 ** 31 - 1)
        down = self.__exp_slv.FF_number(-2 ** 31)
        sub_ab = a.s_v - b.s_v  # is that right?
        condition1_1 = self.__exp_slv.mkFFTerm_Gt(down, sub_ab)
        condition1_2 = self.__exp_slv.mkFFTerm_Gt(sub_ab, up)
        condition2_1 = self.__exp_slv.mkFFTerm_Ge(sub_ab, down)
        condition2_2 = self.__exp_slv.mkFFTerm_Ge(up, sub_ab)

        condition1 = self.__exp_slv.mkTerm(Kind.AND, condition1_1, condition1_2)
        condition2 = self.__exp_slv.mkTerm(Kind.AND, condition2_1, condition2_2)

        result_1 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, sub_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_s, self.__exp_slv.Boolean_False())
                                         )
        result_2 = self.__exp_slv.mkTerm(Kind.AND,
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, sub_ab),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_s, self.__exp_slv.Boolean_True()),
                                         self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                         )
        fr_subs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2)
                                           )

        return fr_subs1s2

    def Fr_sub(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        self.sub_l1ml2m(r, a, b)
                    else:
                        self.sub_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    self.sub_l1nl2m(r, a, b)
                else:
                    self.sub_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                if b.is_m == self.__exp_slv.Boolean_True():
                    self.sub_l1ms2m(r, a, b)
                else:
                    self.sub_l1ms2n(r, a, b)
            else:
                self.sub_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    self.sub_s1ml2m(r, a, b)
                else:
                    self.sub_s1nl2m(r, a, b)
            else:
                self.sub_s1l2n(r, a, b)
        else:
            self.sub_s1s2(r, a, b)

    def mul_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1ml2m

    def mul_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1ml2n

    def mul_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1nl2m

    def mul_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        r_temp = FrElement.construct_value('r_temp')  # temp right?
        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                         r.l_v)
        fr_mull1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1,
                                             result_2,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1nl2n

    def mul_l1ms2m(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ms2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1ms2m

    def mul_l1ms2n(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.s_v))
        fr_mull1ms2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1ms2n

    def mul_l1ns2m(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_mull1ns2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_mull1ns2m

    def mul_l1ns2n(self, r: FrElement, a: FrElement, b: FrElement):
        r_temp = FrElement.construct_value('r_temp')  # temp right?
        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.s_v))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                         r.l_v)
        fr_mull1ns2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1,
                                             result_2,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_mull1ns2n

    def mul_s1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_muls1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_muls1ml2m

    def mul_s1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, b.l_v))
        fr_muls1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_muls1ml2n

    def mul_s1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                       self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.s_v, b.l_v))
        fr_muls1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             result,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()))
        return fr_muls1nl2m

    def mul_s1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        r_temp = FrElement.construct_value('r_temp')  # temp right?
        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.s_v, b.l_v))
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                         self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                         r.l_v)
        fr_muls1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             result_1,
                                             result_2,
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                             self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True()))
        return fr_muls1nl2n

    def mul_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        fr_muls1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                 r.l_v,
                                                                 self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.s_v,
                                                                                       b.s_v)),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                           self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
                                           )

        return fr_muls1s2

    def Fr_mul(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        self.mul_l1ml2m(r, a, b)
                    else:
                        self.mul_l1ml2n(r, a, b)
                else:
                    if b.is_m == self.__exp_slv.Boolean_True():
                        self.mul_l1nl2m(r, a, b)
                    else:
                        self.mul_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                if b.is_m == self.__exp_slv.Boolean_True():
                    self.mul_l1ms2m(r, a, b)
                else:
                    self.mul_l1ms2n(r, a, b)
            else:
                if b.is_m == self.__exp_slv.Boolean_True():
                    self.mul_l1ns2m(r, a, b)
                else:
                    self.mul_l1ns2n(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if a.is_m == self.__exp_slv.Boolean_True():
                if b.is_m == self.__exp_slv.Boolean_True():
                    self.mul_s1ml2m(r, a, b)
                else:
                    self.mul_s1ml2n(r, a, b)
            elif b.is_m == self.__exp_slv.Boolean_True():
                self.mul_s1nl2m(r, a, b)
            else:
                self.mul_s1nl2n(r, a, b)
        else:
            self.mul_s1s2(r, a, b)

    def Fr_toMontgomery(self, r: FrElement, a: FrElement):
        if a.is_m == self.__exp_slv.Boolean_True():  # yes/not?
            return self.Fr_Copy(r, a)
        elif a.is_l == self.__exp_slv.Boolean_True():  # mult?
            fr_toMont = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                    r.l_v,
                                                                    self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
                                                                                          self.R, a.l_v)),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                              )
            return fr_toMont
        else:
            fr_toMont = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                    r.l_v,
                                                                    self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
                                                                                          self.R, a.s_v)),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False()),
                                              self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_True())
                                              )
            return fr_toMont

    def Fr_toLongNormal(self, r: FrElement, a: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if a.is_m == self.__exp_slv.Boolean_True():
                result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                               self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                               a.l_v)
                fr_tolongnormal = self.__exp_slv.mkTerm(Kind.AND,
                                                        result,
                                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                              self.__exp_slv.Boolean_True()),
                                                        self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                              self.__exp_slv.Boolean_False()))
                return fr_tolongnormal
            else:
                return self.Fr_Copy(r, a)
        else:
            fr_tolongnormal = self.__exp_slv.mkTerm(Kind.AND,
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.l_v, a.s_v),
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0),
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                          self.__exp_slv.Boolean_True()),
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                          self.__exp_slv.Boolean_False()))
            return fr_tolongnormal

    def Fr_Square(self, r: FrElement, a: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if a.is_m == self.__exp_slv.Boolean_True():  # yes/not?
                result = self.__exp_slv.mkTerm(Kind.EQUAL,
                                               self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r.l_v, self.R),
                                               self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, a.l_v))
                fr_squarelm = self.__exp_slv.mkTerm(Kind.AND,
                                                    result,
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                          self.__exp_slv.Boolean_True()),
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                          self.__exp_slv.Boolean_True()))
                return fr_squarelm
            else:
                r_temp = FrElement.construct_value('r_temp')  # temp right?
                result_1 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                                 self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R),
                                                 self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a.l_v, a.l_v))
                result_2 = self.__exp_slv.mkTerm(Kind.EQUAL,
                                                 self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, r_temp.l_v, self.R2),
                                                 r.l_v)
                fr_squareln = self.__exp_slv.mkTerm(Kind.AND,
                                                    result_1,
                                                    result_2,
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l,
                                                                          self.__exp_slv.Boolean_True()),
                                                    self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                          self.__exp_slv.Boolean_True()))
                return fr_squareln

        else:
            fr_squares = self.__exp_slv.mkTerm(Kind.AND,
                                               self.__exp_slv.mkTerm(Kind.EQUAL,
                                                                     r.l_v,
                                                                     self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT,
                                                                                           a.s_v, a.s_v)),
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_True()),
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m,
                                                                     self.__exp_slv.Boolean_False()),
                                               self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
                                               )

            return fr_squares

    def req_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ml2m

    def rneq_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ml2m

    def req_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ml2n

    def rneq_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                              before,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ml2n

    def req_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1nl2m

    def rneq_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                              before,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1nl2m

    def req_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1nl2n

    def rneq_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1nl2n

    def req_l1ms2(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ms2

    def rneq_l1ms2(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ms2

    def req_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        b_n = FrElement.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reql1ns2

    def rneq_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        b_n = FrElement.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneql1ns2

    def req_s1l2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reqs1l2m

    def rneq_s1l2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneqs1l2m

    def req_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        a_n = FrElement.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reqs1l2n

    def rneq_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        a_n = FrElement.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Eq(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneqs1l2n

    def req_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_reqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_reqs1s2

    def rneq_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Eq(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Neq(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rneqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rneqs1s2

    def Fr_eq(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        result = self.req_l1ml2m(r, a, b)
                    else:
                        result = self.req_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    result = self.req_l1nl2m(r, a, b)
                else:
                    result = self.req_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                result = self.req_l1ms2(r, a, b)
            else:
                result = self.req_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                result = self.req_s1l2m(r, a, b)
            else:
                result = self.req_s1l2n(r, a, b)
        else:
            result = self.req_s1s2(r, a, b)

        fr_eq = self.__exp_slv.mkTerm(Kind.AND,
                                      result,
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                      )
        return fr_eq

    def Fr_neq(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        result = self.rneq_l1ml2m(r, a, b)
                    else:
                        result = self.rneq_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    result = self.rneq_l1nl2m(r, a, b)
                else:
                    result = self.rneq_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                result = self.rneq_l1ms2(r, a, b)
            else:
                result = self.rneq_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                result = self.rneq_s1l2m(r, a, b)
            else:
                result = self.rneq_s1l2n(r, a, b)
        else:
            result = self.rneq_s1s2(r, a, b)

        fr_neq = self.__exp_slv.mkTerm(Kind.AND,
                                       result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                       )
        return fr_neq

    def geq_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ml2m

    def rlt_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rltl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ml2m

    def geq_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ml2n

    def rlt_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rltl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ml2n

    def geq_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1nl2m

    def rlt_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rltl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1nl2m

    def geq_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1nl2n

    def rlt_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rltl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1nl2n

    def geq_l1ms2(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ms2

    def rlt_l1ms2(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rltl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ms2

    def geq_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        b_n = FrElement.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geql1ns2

    def rlt_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        b_n = FrElement.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rltl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rltl1ns2

    def geq_s1l2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geqs1l2m

    def rlt_s1l2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rlts1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rlts1l2m

    def geq_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        a_n = FrElement.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geqs1l2n

    def rlt_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        a_n = FrElement.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Ge(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rlts1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rlts1l2n

    def geq_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_geqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_geqs1s2

    def rlt_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Ge(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Lt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rlts1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rlts1s2

    def Fr_lt(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        result = self.rlt_l1ml2m(r, a, b)
                    else:
                        result = self.rlt_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    result = self.rlt_l1nl2m(r, a, b)
                else:
                    result = self.rlt_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                result = self.rlt_l1ms2(r, a, b)
            else:
                result = self.rlt_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                result = self.rlt_s1l2m(r, a, b)
            else:
                result = self.rlt_s1l2n(r, a, b)
        else:
            result = self.rlt_s1s2(r, a, b)

        fr_lt = self.__exp_slv.mkTerm(Kind.AND,
                                      result,
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                      )
        return fr_lt

    def Fr_geq(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        result = self.geq_l1ml2m(r, a, b)
                    else:
                        result = self.geq_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    result = self.geq_l1nl2m(r, a, b)
                else:
                    result = self.geq_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                result = self.geq_l1ms2(r, a, b)
            else:
                result = self.geq_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                result = self.geq_s1l2m(r, a, b)
            else:
                result = self.geq_s1l2n(r, a, b)
        else:
            result = self.geq_s1s2(r, a, b)

        fr_geq = self.__exp_slv.mkTerm(Kind.AND,  # have some questions
                                       result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                       )
        return fr_geq

    def leq_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leql1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ml2m

    def rgt_l1ml2m(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgtl1ml2m = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ml2m

    def leq_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leql1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ml2n

    def rgt_l1ml2n(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgtl1ml2n = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ml2n

    def leq_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leql1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1nl2m

    def rgt_l1nl2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgtl1nl2m = self.__exp_slv.mkTerm(Kind.AND,
                                             before,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1nl2m

    def leq_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leql1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1nl2n

    def rgt_l1nl2n(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgtl1nl2n = self.__exp_slv.mkTerm(Kind.AND,
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                             self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1nl2n

    def leq_l1ms2(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leql1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ms2

    def rgt_l1ms2(self, r: FrElement, a: FrElement, b: FrElement):
        b_m = FrElement.construct_value('b_m')  # temp right?
        before = self.Fr_toMontgomery(b_m, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_m.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_m.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgtl1ms2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ms2

    def leq_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        b_n = FrElement.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leql1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leql1ns2

    def rgt_l1ns2(self, r: FrElement, a: FrElement, b: FrElement):
        b_n = FrElement.construct_value('b_n')  # temp right?
        before = self.Fr_toLongNormal(b_n, b)
        condition1 = self.__exp_slv.mkFFTerm_Le(a.l_v, b_n.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.l_v, b_n.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgtl1ns2 = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgtl1ns2

    def leq_s1l2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leqs1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leqs1l2m

    def rgt_s1l2m(self, r: FrElement, a: FrElement, b: FrElement):
        a_m = FrElement.construct_value('a_m')  # temp right?
        before = self.Fr_toMontgomery(a_m, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_m.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_m.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgts1l2m = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgts1l2m

    def leq_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        a_n = FrElement.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leqs1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leqs1l2n

    def rgt_s1l2n(self, r: FrElement, a: FrElement, b: FrElement):
        a_n = FrElement.construct_value('a_n')  # temp right?
        before = self.Fr_toLongNormal(a_n, a)
        condition1 = self.__exp_slv.mkFFTerm_Le(a_n.l_v, b.l_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a_n.l_v, b.l_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgts1l2n = self.__exp_slv.mkTerm(Kind.AND,
                                            before,
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                            self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgts1l2n

    def leq_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)

        fr_leqs1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_leqs1s2

    def rgt_s1s2(self, r: FrElement, a: FrElement, b: FrElement):
        condition1 = self.__exp_slv.mkFFTerm_Le(a.s_v, b.s_v)
        condition2 = self.__exp_slv.mkFFTerm_Gt(a.s_v, b.s_v)

        result_1 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 0)
        result_2 = self.__exp_slv.mkTerm(Kind.EQUAL, r.s_v, 1)

        fr_rgts1s2 = self.__exp_slv.mkTerm(Kind.AND,
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result_1),
                                           self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result_2))
        return fr_rgts1s2

    def Fr_gt(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        result = self.rgt_l1ml2m(r, a, b)
                    else:
                        result = self.rgt_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    result = self.rgt_l1nl2m(r, a, b)
                else:
                    result = self.rgt_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                result = self.rgt_l1ms2(r, a, b)
            else:
                result = self.rgt_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                result = self.rgt_s1l2m(r, a, b)
            else:
                result = self.rgt_s1l2n(r, a, b)
        else:
            result = self.rgt_s1s2(r, a, b)

        fr_gt = self.__exp_slv.mkTerm(Kind.AND,
                                      result,
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                      self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                      )
        return fr_gt

    def Fr_leq(self, r: FrElement, a: FrElement, b: FrElement):
        if a.is_l == self.__exp_slv.Boolean_True():
            if b.is_l == self.__exp_slv.Boolean_True():
                if a.is_m == self.__exp_slv.Boolean_True():
                    if b.is_m == self.__exp_slv.Boolean_True():
                        result = self.leq_l1ml2m(r, a, b)
                    else:
                        result = self.leq_l1ml2n(r, a, b)
                elif b.is_m == self.__exp_slv.Boolean_True():
                    result = self.leq_l1nl2m(r, a, b)
                else:
                    result = self.leq_l1nl2n(r, a, b)
            elif a.is_m == self.__exp_slv.Boolean_True():
                result = self.leq_l1ms2(r, a, b)
            else:
                result = self.leq_l1ns2(r, a, b)
        elif b.is_l == self.__exp_slv.Boolean_True():
            if b.is_m == self.__exp_slv.Boolean_True():
                result = self.leq_s1l2m(r, a, b)
            else:
                result = self.leq_s1l2n(r, a, b)
        else:
            result = self.leq_s1s2(r, a, b)

        fr_leq = self.__exp_slv.mkTerm(Kind.AND,  # have some questions
                                       result,
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_m, self.__exp_slv.Boolean_False()),
                                       self.__exp_slv.mkTerm(Kind.EQUAL, r.is_l, self.__exp_slv.Boolean_False())
                                       )
        return fr_leq

    def Fr_isTrue(self, pE: FrElement):
        result = 1
        if pE.is_l == self.__exp_slv.Boolean_True():
            if pE.l_v != 0:
                return self.__exp_slv.Boolean_True()
            else:
                return self.__exp_slv.Boolean_False()
            # condition1 = self.__exp_slv.mkFFTerm_Eq(pE.l_v, 0)
            # condition2 = self.__exp_slv.mkFFTerm_Neq(pE.l_v, 0)
            # result1 = self.__exp_slv.mkTerm(Kind.EQUAL, result, 0)
            # result2 = self.__exp_slv.mkTerm(Kind.EQUAL, result, 1)
            # return self.__exp_slv.mkTerm(Kind.AND,
            #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result1),
            #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result2)
            #                              )
        else:
            if pE.s_v != 0:
                return self.__exp_slv.Boolean_True()
            else:
                return self.__exp_slv.Boolean_False()
            # condition1 = self.__exp_slv.mkFFTerm_Eq(pE.s_v, 0)
            # condition2 = self.__exp_slv.mkFFTerm_Neq(pE.s_v, 0)
            # result1 = self.__exp_slv.mkTerm(Kind.EQUAL, result, 0)
            # result2 = self.__exp_slv.mkTerm(Kind.EQUAL, result, 1)
            # return self.__exp_slv.mkTerm(Kind.AND,
            #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition1, result1),
            #                              self.__exp_slv.mkTerm(Kind.IMPLIES, condition2, result2)
            #                              )

    def parse_sym_file(self, filepath):
        with open(filepath, 'r') as file:
            for line in file:
                parts = line.strip().split(',')
                if len(parts) == 4:
                    signal_index = int(parts[0])
                    signal_name = parts[3].strip()
                    self.signal_map[signal_index] = signal_name

    def get_signal_name(self, index):
        if index in self.signal_map:
            return self.signal_map[index]
        else:
            raise ValueError(f"Signal index {index} not found in the signal map.")

    def extract_index(self, part, mySignalStart):
        part = part.strip().rstrip(';')
        if part.startswith('&'):
            part = part[1:]
        if 'ctx->signalValues' in part:
            # Extract cmp_index_ref value
            start_index = part.find('[') + 1
            end_index = part.find(']')
            subcomponent_ref = part[start_index:end_index].strip()

            # Use the value_to_subfunction to calculate the index
            if self.value_to_subfunction is not None:
                component_index = self.value_to_subfunction
                start_pos = self.start_position_dict.get(component_index, 0)
                number = start_pos + int(part.split('+')[1].split(']')[0].strip())  # Extract offset
                signal_name = self.get_signal_name(number)
                if signal_name not in self.element_dict:
                    self.element_dict[signal_name] = FrElement.construct_value(signal_name)
                return signal_name

        elif part.startswith('expaux') or part.startswith('circuitConstants') or part.startswith('lvar'):
            # if part not in self.element_dict: # reuse the lvar
            if part.startswith('circuitConstants'):
                self.element_dict[part] = self.constants_dict[part]
            else:
                self.element_dict[part] = FrElement.construct_value(part)
            return part
        else:
            # print(mySignalStart)
            parts = part.split('[')
            index_part = parts[1].split(']')
            index_str = index_part[0].strip().rstrip(';')
            index = int(index_str.replace('mySignalStart +', '').strip()) + mySignalStart
            signal_name = self.get_signal_name(index)
            if signal_name not in self.element_dict:
                self.element_dict[signal_name] = FrElement.construct_value(signal_name)
            return signal_name

    def deal_dat(self, dat_path, num):
        file = open(dat_path, 'rb')
        content = file.read()
        file.close()

        # 每组40个字节，从文件末尾取 num * 40 个字节
        total_bytes_to_read = num * 40
        groups = content[-total_bytes_to_read:]

        for i in range(num):
            group = groups[-(i + 1) * 40: -(i * 40) if i > 0 else None]
            short = group[0:4]
            type = group[4:8]
            long = group[8:]

            short_value = int.from_bytes(short, byteorder='little', signed=True)
            print(f'Group {i + 1} Short Value: {hex(short_value)}')

            type_value = int.from_bytes(type, byteorder='little', signed=False)
            print(f'Group {i + 1} Type Value: {hex(type_value)}')
            if_long = bool(type_value & (1 << 31))
            if_mong = bool(type_value & (1 << 30))

            print(f'Group {i + 1} if_long = {if_long}')
            print(f'Group {i + 1} if_mong = {if_mong}')

            long_value_0 = int.from_bytes(long[0:8], byteorder='little', signed=False)
            long_value_1 = int.from_bytes(long[8:16], byteorder='little', signed=False)
            long_value_2 = int.from_bytes(long[16:24], byteorder='little', signed=False)
            long_value_3 = int.from_bytes(long[24:32], byteorder='little', signed=False)

            long_value = long_value_3
            long_value = (long_value << 64) + long_value_2
            long_value = (long_value << 64) + long_value_1
            long_value = (long_value << 64) + long_value_0
            print(f'Group {i + 1} Long Value: {hex(long_value)}')

            true_int = None
            if if_long:
                if if_mong:
                    element_type = 0xC0000000
                    true_int = self.Rr_int * long_value % self.p_int
                else:
                    element_type = 0x80000000
                    true_int = long_value % self.p_int
            else:
                if if_mong:
                    element_type = 0x40000000
                    true_int = self.Rr_int * short_value % self.p_int
                else:
                    element_type = 0x00000000
                    true_int = short_value % self.p_int

            self.constants_dict[f'circuitConstants[{num - 1 - i}]'] = FrElement.construct_constant(
                f'circuitConstants[{num - 1 - i}]',
                short_value, long_value, element_type)
            self.int_dict[f'circuitConstants[{num - 1 - i}]'] = true_int

    # 解析并计算表达式
    def evaluate_expression(self, operation):
        result = None
        match = re.match(r'Fr_(add|mul|sub|lt|gt|leq|geq)\(&expaux\[(\d+)\],&(\w+\[\d+\]),&(\w+\[\d+\])\)', operation)
        if match:
            op, dest, src1, src2 = match.groups()
            src1_val = self.int_dict.get(src1, 0)
            src2_val = self.int_dict.get(src2, 0)

            if op == 'add':
                result = src1_val + src2_val
            elif op == 'mul':
                result = src1_val * src2_val
            elif op == 'sub':
                result = src1_val - src2_val
            elif op == 'lt':
                result = 1 if src1_val < src2_val else 0
            elif op == 'gt':
                result = 1 if src1_val > src2_val else 0
            elif op == 'leq':
                result = 1 if src1_val <= src2_val else 0
            elif op == 'geq':
                result = 1 if src1_val >= src2_val else 0
            self.int_dict[f'expaux[{dest}]'] = result

    # 解析循环体中的操作
    def parse_while_loop(self, while_loop_code):
        dest_var = None
        dest_key = None
        for line in while_loop_code:
            if re.search(r'PFrElement aux_dest = &lvar\[\d+\]', line):
                dest_var = re.findall(r'&lvar\[\d+\]', line)[0]
                dest_key = dest_var[1:]
            if re.match(r'Fr_(add|mul|sub)\(&expaux\[\d+\],&\w+\[\d+\],&\w+\[\d+\]\)', line):
                self.evaluate_expression(line)
            elif re.match(r'Fr_copy\(\&\w+\[\d+\],\&expaux\[\d+\]\)', line):
                src_var = re.findall(r'&expaux\[\d+\]', line)[0]
                self.int_dict[dest_key] = self.int_dict.get(src_var[1:], 0)

    # 计算循环次数
    def calculate_loop_iterations(self, loop_condition_lines, while_loop_code):
        iterations = 0
        temp_dict = self.int_dict
        while True:
            for line in loop_condition_lines:
                self.evaluate_expression(line)

            if self.int_dict.get('expaux[0]', 0) == 0:
                break
            iterations += 1
            self.parse_while_loop(while_loop_code)
        self.int_dict = temp_dict
        return iterations

    def dealWhile(self, i, lines):
        loop_start = i
        in_while_loop = True
        loop_condition_lines = []
        while_loop_code = []
        update_code = []
        circom_line_number = None
        loop_end = None
        # 向前搜索一行，获取circom行号
        previous_line = lines[i - 1].strip().rstrip(';') if i > 0 else None
        if previous_line and re.search(r'// line circom \d+', previous_line):
            circom_line_number = re.findall(r'// line circom (\d+)', previous_line)[0]
        if in_while_loop and circom_line_number:
            for j in range(i - 1, -1, -1):
                line = lines[j].strip().rstrip(';')
                if re.search(rf'// line circom {circom_line_number}', line):
                    loop_condition_lines.insert(0, line)
                else:
                    loop_end = j + 1
                    break

        # 搜索循环体内的操作和完整的循环体代码
        for i in range(loop_start+1, len(lines)):
            line = lines[i].strip().rstrip(';')
            if loop_end is not None and lines[loop_end].strip().rstrip(';') in line:
                break
            else:
                while_loop_code.append(line)

        # 搜索the代码 need to update later
        for i in range(loop_start+1, len(lines)):
            line = lines[i].strip().rstrip(';')
            if previous_line in line:
                update_code.append(line)
                loop_end = i
                break
            else:
                update_code.append(line)

        return loop_condition_lines, while_loop_code, update_code, loop_start, loop_end

    # 更新代码中的循环部分
    def update_lines(self, lines, loop_start, loop_end, update_code, iterations):
        updated_lines = lines[:loop_start - 1]
        for _ in range(iterations):
            updated_lines.extend(update_code)
        updated_lines.extend(lines[loop_end + 1:])
        return updated_lines

    def directory_2_smt(self, symFile_path, code_block_file_path):
        self.parse_sym_file(symFile_path)
        # 打开并读取 code_block_file_path 对应的文件内容
        with open(code_block_file_path, 'r') as file:
            lines = file.readlines()
        aux_dest = None
        i = 0
        while i < len(lines):
            line = lines[i].strip().rstrip(';')
            if '_create(uint soffset,uint coffset,Circom_CalcWit* ctx,std::string componentName,uint componentFather){' not in line:
                if '_run(uint ctx_index,Circom_CalcWit* ctx){' in line:
                    # 提取函数名
                    function_line_match = re.search(r'void (\w+)_run', line)
                    if function_line_match:
                        function_name = function_line_match.group(1)
                        self.function_line_dict[function_name] = i
                i += 1
            else:
                break

        while i < len(lines):
            line = lines[i].strip().rstrip(';')
            if self.is_running_subfunction and line.startswith('void '):
                # 判断当前行是否为新函数定义
                self.is_running_subfunction = False
                i = self.go_subfunction_line + 1  # 返回到 temp 的下一个位置继续解析
                self.go_subfunction_line = None
                self.my_signal_start = 1
                continue
            if 'uint cmp_index_ref' in line:
                # Extract the value assigned to cmp_index_ref
                self.value_to_subfunction = int(line.split('=')[1].strip(';').strip())

            # 记录 uint aux_create 的标记
            if 'uint aux_create =' in line:
                aux_create_match = re.search(r'uint aux_create = (\d+)', line)
                if aux_create_match:
                    self.current_aux_create = aux_create_match.group(1)
            # 记录起始位置
            elif 'uint csoffset = mySignalStart+' in line:
                # 提取 number
                csoffset_match = re.search(r'uint csoffset = mySignalStart\+(\d+)', line)
                if csoffset_match and self.current_aux_create is not None:
                    number = int(csoffset_match.group(1))
                    self.start_position_dict[self.current_aux_create] = number + 1  # 记录起始位置
                    # 记录函数名
            elif '_create(csoffset,aux_cmp_num,ctx,new_cmp_name,myId)' in line:
                function_match = re.search(r'(\w+)_create', line)
                if function_match and self.current_aux_create is not None:
                    function_name = function_match.group(1)
                    self.function_name_dict[function_name] = self.current_aux_create
                    self.current_aux_creat = None
            # 运行子函数
            elif '_run(mySubcomponents[cmp_index_ref],ctx)' in line:
                # 提取函数名并记录当前位置
                function_match = re.search(r'(\w+)_run', line)
                if function_match:
                    function_name = function_match.group(1)
                    if function_name in self.function_line_dict:
                        self.go_subfunction_line = i
                        self.is_running_subfunction = True
                        i = self.function_line_dict[function_name] + 1  # 跳转到记录的行号解析子函数
                        self.my_signal_start = self.start_position_dict[self.function_name_dict[function_name]] # is it ok/
                        continue
                    # 解析子函数

            elif line.startswith('assert('):
                if self.value_to_subfunction is not None:
                    self.value_to_subfunction = None

            elif 'while(Fr_isTrue(&expaux[0]))' in line:
                loop_condition_lines, while_loop_code, update_code, loop_start, loop_end = self.dealWhile(i, lines)
                loop_num = self.calculate_loop_iterations(loop_condition_lines, while_loop_code)
                lines = self.update_lines(lines, loop_start, loop_end, update_code, loop_num)
                i = loop_start - 1  # 重新设置 i 到更新后的部分的起始位置

            elif line.startswith('PFrElement aux_dest'):
                dest_var = self.extract_index(line.split('&')[1], self.my_signal_start)
                aux_dest = FrElement.construct_value(dest_var)
                if re.search(r'PFrElement aux_dest = &lvar\[\d+\]', line):
                    dest_var = re.findall(r'&lvar\[\d+\]', line)[0]
                    dest_key = dest_var[1:]
                    temp = i + 1
                    while temp < len(lines):
                        line = lines[temp].strip().rstrip(';')
                        if re.match(r'Fr_(add|mul|sub)\(&expaux\[\d+\],&\w+\[\d+\],&\w+\[\d+\]\)', line):
                            self.evaluate_expression(line)
                        elif re.match(r'Fr_copy\(\&\w+\[\d+\],\&expaux\[\d+\]\)', line):
                            src_var = re.findall(r'&expaux\[\d+\]', line)[0]
                            self.int_dict[dest_key] = self.int_dict.get(src_var[1:], 0)
                            break
                    i = temp + 1
                    continue

            elif 'Fr_add' in line or 'Fr_mul' in line or 'Fr_sub' in line or 'Fr_eq' in line or 'Fr_neq' in line\
                    or 'Fr_gt' in line or 'Fr_lt' in line or 'Fr_geq' in line or 'Fr_leq' in line:
                print(line)
                parts = line.split(',')
                dest_part = parts[0].split('(')[1]
                src1_part = parts[1]
                src2_part = parts[2].split(')')[0]

                if 'aux_dest' in dest_part:
                    dest_element = aux_dest
                else:
                    dest_var = self.extract_index(dest_part, self.my_signal_start)
                    dest_element = self.element_dict[dest_var]

                src1_var = self.extract_index(src1_part, self.my_signal_start)
                src2_var = self.extract_index(src2_part, self.my_signal_start)

                src1_element = self.element_dict[src1_var]
                src2_element = self.element_dict[src2_var]

                if 'Fr_add' in line:
                    self.directory_terms.append(self.Fr_add(dest_element, src1_element, src2_element))
                elif 'Fr_mul' in line:
                    self.directory_terms.append(self.Fr_mul(dest_element, src1_element, src2_element))
                elif 'Fr_sub' in line:
                    self.directory_terms.append(self.Fr_sub(dest_element, src1_element, src2_element))
                elif 'Fr_eq' in line: # isTrue Function
                    self.directory_terms.append(self.Fr_eq(dest_element, src1_element, src2_element))
                    self.directory_terms.append(
                        self.__exp_slv.mkTerm(Kind.EQUAL, self.__exp_slv.Boolean_True(), self.Fr_isTrue(dest_element)))
                elif 'Fr_neq' in line:
                    self.directory_terms.append(self.Fr_neq(dest_element, src1_element, src2_element))
                    self.directory_terms.append(
                        self.__exp_slv.mkTerm(Kind.EQUAL, self.__exp_slv.Boolean_True(), self.Fr_isTrue(dest_element)))
                elif 'Fr_gt' in line:
                    self.directory_terms.append(self.Fr_gt(dest_element, src1_element, src2_element))
                elif 'Fr_lt' in line:
                    self.directory_terms.append(self.Fr_lt(dest_element, src1_element, src2_element))
                elif 'Fr_geq' in line:
                    self.directory_terms.append(self.Fr_geq(dest_element, src1_element, src2_element))
                elif 'Fr_leq' in line:
                    self.directory_terms.append(self.Fr_leq(dest_element, src1_element, src2_element))

            elif 'Fr_copy' in line or 'Fr_square' in line:
                print(line)
                parts = line.split(',')
                dest_part = parts[0].split('(')[1]
                src_part = parts[1].split(')')[0]

                if 'aux_dest' in dest_part:
                    dest_element = aux_dest
                else:
                    dest_var = self.extract_index(dest_part, self.my_signal_start)
                    dest_element = self.element_dict[dest_var]

                src_var = self.extract_index(src_part, self.my_signal_start)
                src_element = self.element_dict[src_var]

                if 'Fr_copy' in line:
                    self.directory_terms.append(self.Fr_Copy(dest_element, src_element))
                elif 'Fr_square' in line:
                    self.directory_terms.append(self.Fr_Square(dest_element, src_element))

            i += 1

if __name__ == '__main__':
    exp_slv = ExpandedCVC5('bn128')
    test = FrFunction(exp_slv=exp_slv)
    symFile_path = 'testsym.sym'
    codeblock = 'codeblocktest.txt'
    test.directory_2_smt(symFile_path=symFile_path, code_block_file_path=codeblock)
    print(test.directory_terms)
    print(test.signal_map)
