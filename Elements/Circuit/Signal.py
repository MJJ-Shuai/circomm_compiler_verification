from enum import Enum

from Elements.Circuit.BuildinWords import CBW
from Tools.Check import *
from Elements.Circuit.Interfaces import *


class SignalTypes(Enum):
    Input = 'Input '
    Output = 'Output'
    Intermediate = 'Inter '


class Signal(SmtBuild, Type):
    def __init__(self, call_name, id_name, sym_name, signal_type, smt):
        TypeCheck(str, call_name)
        TypeCheck(str, id_name)
        EnumCheck(SignalTypes, signal_type)
        self.call_name = call_name
        self.id_name = id_name
        self.sym_name = sym_name
        self.signal_type = signal_type
        self.smt = smt

    def __str__(self):
        return f"{self.signal_type.value} signal {self.id_name}"

    def toSmt(self):
        return self.smt

    def type(self):
        return CBW.Signal

    def loc_sym_name(self, loc):
        self.sym_name = f'{loc}.{self.sym_name}'

    def __hash__(self):
        return hash(self.id_name)
