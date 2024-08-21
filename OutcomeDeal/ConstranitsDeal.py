import json

from cvc5 import Kind


class ConstraintsDealer:
    def __init__(self, cons_path, exp_slv, sym_data_dic):
        file = open(cons_path, 'r')
        context = json.load(file)
        file.close()
        self.__raw_consts = context['constraints']
        self.__exp_slv = exp_slv
        self.__sym_data_dic = sym_data_dic
        self.__constraint_terms = list()
        self.arrange_constraints()

    def get_all_terms(self):
        return self.__constraint_terms

    def arrange_constraints(self):
        for const in self.__raw_consts:
            item = self.arrange_one_constraint(const)
            self.__constraint_terms.append(item)

    def arrange_one_constraint(self, const):
        a = self.arrange_linear(const[0])
        b = self.arrange_linear(const[1])
        c = self.arrange_linear(const[2])
        if a is None or b is None:
            a_times_b = self.__exp_slv.FF_zero()
        else:
            a_times_b = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, a, b)

        if c is None:
            c = self.__exp_slv.FF_zero()

        return self.__exp_slv.mkTerm(Kind.EQUAL, a_times_b, c)

    def arrange_linear(self, linear):
        items = list()
        for s_add, coe in linear.items():
            if s_add == '0':
                item = self.__exp_slv.FF_number(coe)
            else:
                variable = self.__sym_data_dic.get_item(s_add)
                ff_coe = self.__exp_slv.FF_number(coe)
                item = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, ff_coe, variable)
            items.append(item)

        if len(items) == 0:
            return None
        elif len(items) == 1:
            return items[0]
        else:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, *items)
