from Elements.Circuit.BuildinWords import CBW
from Elements.Circuit.Interfaces import Type, SmtBuild
from Tools.Check import *


class Var(SmtBuild, Type):
    def __init__(self, call_name, id_name, exp_slv):
        TypeCheck(str, call_name)
        TypeCheck(str, id_name)
        self.call_name = call_name
        self.id_name = id_name
        self.exp_slv = exp_slv
        self.value = 0
        # deterministic == True ===> value is int
        # deterministic == False ===> expression

    def __str__(self):
        return f"Var {self.id_name}"

    def type(self):
        return CBW.Var

    def toSmt(self):
        if isinstance(self.value, int):
            return self.exp_slv.FF_number(self.value)
        else:
            return self.value


class VarArray(Type):
    def __init__(self, call_name, id_name, var_list):
        self.call_name = call_name
        self.id_name = id_name
        self.var_list = var_list

    def set_values(self, value_list):
        for i in range(len(value_list)):
            self.var_list[i].value = value_list[i]

    def type(self):
        return CBW.VarArray

    