from cvc5 import Kind

from Convert.AdditionalOperations import ExpandedCVC5
from Elements.Circuit.BuildinWords import CBW, EIO, EPO, OP
from Elements.Circuit.Interfaces import Type
from Elements.Circuit.Signal import SignalTypes, Signal
from Elements.Circuit.Template import Template
from Elements.Circuit.Var import Var, VarArray
from Tools.Calculate import calculate_deterministic_infixOp, calculate_deterministic_prefixOp
from Tools.Check import TypeCheck
from Tools.Errors import MyItemError, MyNumError


class Component(Type):

    @staticmethod
    def main_component(js_mc, exp_slv):
        component = Component('main', exp_slv)
        call = js_mc[1][CBW.Call.value]
        template_name = call[CBW.id.value]
        raw_args = call[CBW.args.value]
        args = Component.deal_main_args(raw_args)
        component.call(template_name, args)
        return component

    @staticmethod
    def deal_main_args(args):
        outcome = list()
        for item in args:
            if CBW.Number.value in item:
                value_type = item[CBW.Number.value][1][0]
                if value_type == 0:
                    outcome.append(0)
                else:
                    value = item[CBW.Number.value][1][1][0]
                    outcome.append(int(value))
            else:
                raise MyNumError('main args not given via number')
        return outcome

    def __init__(self, call_name, exp_slv):
        TypeCheck(str, call_name)
        TypeCheck(ExpandedCVC5, exp_slv)
        self.__exp_slv = exp_slv
        # call_name 是在代码段中的名字
        self.__call_name = call_name
        # id_name 是唯一的名字，在调用template生成后才会给定
        self.__id_name = ''
        # subcomponent name --> component
        self.__sub_components = dict()
        # variable name --> variable
        self.__variable_dic = dict()
        self.__signal_dic = dict()
        self.__parameter_list = list()
        self.__input_signal_dic = dict()
        self.__output_signal_dic = dict()
        self.circuit_terms = list()
        self.constraint_terms = list()

    def call(self, template_name, args_values):
        template = Template.get_Template(template_name)
        suffix = template.prepare_build_component()
        self.__id_name = template.get_name() + suffix
        args_names = template.get_args()
        self.init_parameter_list(args_names, args_values)
        block = template.get_block()
        self.block_2_smt(block)

    def init_parameter_list(self, args_names, args_values):
        for i in range(len(args_names)):
            call_name = args_names[i]
            id_name = self.build_id_name(call_name)
            var = Var(call_name, id_name, self.__exp_slv)
            var.value = args_values[i]
            self.__variable_dic[call_name] = var
            self.__parameter_list.append(var)
            print(f'Para var {id_name} = {var.value}')

    def type(self):
        return CBW.Component

    def get_all_circuit_terms(self):
        outcome = list()
        outcome.extend(self.circuit_terms)
        for call_name, comp in self.__sub_components.items():
            outcome.extend(comp.get_all_circuit_terms())
        return outcome

    def get_all_constraint_terms(self):
        outcome = list()
        outcome.extend(self.constraint_terms)
        for call_name, comp in self.__sub_components.items():
            outcome.extend(comp.get_all_constraint_terms())
        return outcome

    def get_all_signals_dic(self):
        outcome = dict()
        outcome.update(self.__signal_dic)
        for call_name, comp in self.__sub_components.items():
            sub_comp_signals = comp.get_all_signals()
            for signal in sub_comp_signals:
                signal.loc_sym_name(self.__call_name)
                outcome[signal.id_name] = signal
        return outcome

    def get_io_signal(self, call_name):
        TypeCheck(str, call_name)
        return self.__variable_dic[call_name]

    def get_output_signals_dic(self):
        return self.__output_signal_dic

    def get_input_signals_dic(self):
        return self.__input_signal_dic

    def block_2_smt(self, block):
        stmts = block[CBW.stmts.value]
        for stmt in stmts:
            self.stmt_2_smt(stmt)

    def stmt_2_smt(self, stmt):
        for subfield, value in stmt.items():
            if subfield == CBW.InitializationBlock.value:
                self.initialization_block_2_smt(value)
            elif subfield == CBW.Substitution.value:
                self.substitution_2_smt(value)
            elif subfield == CBW.Block.value:
                self.block_2_smt(value)
            elif subfield == CBW.ConstraintEquality.value:
                self.equality_2_smt(value)
            elif subfield == CBW.While.value:
                self.deal_while(value)
            elif subfield == CBW.IfThenElse.value:
                self.deal_ifThenElse(value)
            else:
                print('unsolved subfield :' + subfield)

    def initialization_block_2_smt(self, initialization_block):
        initializations = initialization_block[CBW.initializations.value]
        self.initialization_2_smt(initializations)

    def initialization_2_smt(self, initialization):
        for item in initialization:
            for subfield, value in item.items():
                if subfield == CBW.Declaration.value:
                    self.declaration_2_smt(value)
                elif subfield == CBW.Substitution.value:
                    self.substitution_2_smt(value)
                else:
                    print('unsolved subfield :' + subfield)

    def declaration_2_smt(self, declaration):
        xtype = declaration[CBW.xtype.value]
        name = declaration[CBW.name.value]
        if xtype == CBW.Var.value:
            dimensions = declaration[CBW.dimensions.value]
            self.build_var(name, dimensions)
        elif xtype == CBW.Component.value:
            self.build_component(name)
        elif CBW.Signal.value in xtype:
            dimensions = declaration[CBW.dimensions.value]
            self.build_signal(xtype, name, dimensions)

    def build_var(self, call_name, dimensions):
        id_name = self.build_id_name(call_name)
        suffix = self.build_dimension_names([''], dimensions, 0)
        # 以数组形式构造的
        if suffix[0] != '':
            var_list = list()
            for suf in suffix:
                delt_id_name = id_name + suf
                delt_call_name = call_name + suf
                var = Var(delt_call_name, delt_id_name, self.__exp_slv)
                self.__variable_dic[delt_call_name] = var
                var_list.append(var)
                print(var)
            var_array = VarArray(call_name, id_name, var_list)
            self.__variable_dic[call_name] = var_array
        else:
            var = Var(call_name, id_name, self.__exp_slv)
            self.__variable_dic[call_name] = var

    def build_component(self, call_name):
        component = Component(call_name, self.__exp_slv)
        self.__variable_dic[call_name] = component
        self.__sub_components[call_name] = component

    def build_signal(self, xtype, call_name, dimensions):
        id_name = self.build_id_name(call_name)
        raw_type = xtype[CBW.Signal.value][0]
        if raw_type == CBW.Input.value:
            signal_type = SignalTypes.Input
        elif raw_type == CBW.Output.value:
            signal_type = SignalTypes.Output
        elif raw_type == CBW.Intermediate.value:
            signal_type = SignalTypes.Intermediate
        else:
            raise MyItemError(raw_type)

        suffix = self.build_dimension_names([''], dimensions, 0)
        for suf in suffix:
            delt_id_name = id_name + suf
            delt_call_name = call_name + suf
            delt_sym_name = f'{self.__call_name}.{delt_call_name}'
            smt = self.__exp_slv.mkConst(self.__exp_slv.F(), delt_id_name)
            signal = Signal(delt_call_name, delt_id_name, delt_sym_name, signal_type, smt)
            self.__variable_dic[delt_call_name] = signal
            self.__signal_dic[signal.id_name] = signal
            if signal_type == SignalTypes.Output:
                self.__output_signal_dic[signal.id_name] = signal
            elif signal_type == SignalTypes.Input:
                self.__input_signal_dic[signal.id_name] = signal
            print(signal)

    def build_dimension_names(self, suffix, dimensions, i):
        if i < len(dimensions):
            stmt = dimensions[i]
            # if CBW.Variable.value in current:
            #     variable = current[CBW.Variable.value]
            #     var_name = variable[CBW.name.value]
            #     var = self.__variable_dic[var_name]
            #     n = var.value
            # elif CBW.Number.value in current:
            #     number = current[CBW.Number.value]
            #     n = number[1][1][0]
            # else:
            #     n = 0
            n = self.getVarStmtValue(stmt)

            next = list()
            for suf in suffix:
                for index in range(0, n):
                    next.append(f'{suf}[{index}]')
            return self.build_dimension_names(next, dimensions, i+1)
        else:
            return suffix

    def component_name_mapping(self, name_prefix):
        if name_prefix in self.__sub_components.keys():
            current_name = self.__sub_components.get(name_prefix).__id_name
            if len(current_name) != 0:
                return current_name
        return name_prefix

    def substitution_2_smt(self, substitution):
        op = substitution[CBW.op.value]
        name = substitution[CBW.subbed_var.value]
        # name_prefix = self.component_name_mapping(name_prefix)
        access = substitution[CBW.access.value]
        is_component, name_suffix = self.get_access(access)
        if not is_component:
            name = name + name_suffix
        left = self.__variable_dic[name]
        right = substitution[CBW.rhe.value]
        # for signals
        if op == OP.AssignConstraintSignal.value or op == OP.AssignSignal.value:
            if left.type() is CBW.Signal:
                delt_left = left.toSmt()

            elif left.type() is CBW.Component:
                call_name = name_suffix
                signal = left.get_io_signal(call_name)
                delt_left = signal.toSmt()

            # 需要考察右测是否有条件运算
            if CBW.InlineSwitchOp.value in right:
                switch = right[CBW.InlineSwitchOp.value]
                cond = switch[CBW.cond.value]
                t_case = switch[CBW.if_true.value]
                f_case = switch[CBW.if_false.value]
                d_cond = self.item_2_smt(cond)
                dt_case = self.item_2_smt(t_case)
                df_case = self.item_2_smt(f_case)
                term = self.mkSwitchTerm(delt_left, op, d_cond, dt_case, df_case)
            else:
                delt_right = self.item_2_smt(right)
                term = self.__exp_slv.mkTerm(Kind.EQUAL, delt_left, delt_right)
            self.circuit_terms.append(term)
            if op == OP.AssignConstraintSignal.value:
                self.constraint_terms.append(term)
        elif op == OP.AssignVar.value:
            if left.type() == CBW.Component:
                call = right[CBW.Call.value]
                template_name = call[CBW.id.value]

                args_raw_values = call[CBW.args.value]
                args_values = list()
                for arg_raw_value in args_raw_values:
                    arg_value = self.getVarStmtValue(arg_raw_value)
                    args_values.append(arg_value)

                left.call(template_name, args_values)
            elif left.type() == CBW.Var:
                left.value = self.getVarStmtValue(right)
            elif left.type() == CBW.VarArray:
                if CBW.UniformArray.value in right:
                    uniform_array = right[CBW.UniformArray.value]
                    array_data = self.deal_uniformArray(uniform_array)
                    left.set_values(array_data)
                elif CBW.ArrayInLine.value in right:
                    array_inline = right[CBW.ArrayInLine.value]
                    array_data = self.deal_arrayInline(array_inline)
                    left.set_values(array_data)

    def deal_uniformArray(self, uniform_array):
        outcome = list()
        value = uniform_array[CBW.value.value]
        dimension = uniform_array[CBW.dimension.value]
        return outcome

    def deal_arrayInline(self, array_inline):
        outcome = list()
        values = array_inline[CBW.values.value]
        return outcome

    def get_access(self, access):
        is_component = False
        suffix = ''
        for acc in access:
            if CBW.ArrayAccess.value in acc:
                stmt = acc[CBW.ArrayAccess.value]
                index = self.getVarStmtValue(stmt)
                suffix = f'{suffix}[{index}]'
            elif CBW.ComponentAccess.value in acc:
                call_name = acc[CBW.ComponentAccess.value]
                suffix = f'{call_name}'
                is_component = True
            else:
                pass
        return (is_component, suffix)

    def mkSwitchTerm(self, left, op, cond, t_case, f_case):
        if op == OP.AssignSignal.value:
            neg_cond = self.__exp_slv.mkTerm(Kind.NOT, cond)
            t_eq = self.__exp_slv.mkTerm(Kind.EQUAL, left, t_case)
            f_eq = self.__exp_slv.mkTerm(Kind.EQUAL, left, f_case)
            t_imply = self.__exp_slv.mkTerm(Kind.IMPLIES, cond, t_eq)
            f_imply = self.__exp_slv.mkTerm(Kind.IMPLIES, neg_cond, f_eq)
            return self.__exp_slv.mkTerm(Kind.AND, t_imply, f_imply)

    def item_2_smt(self, item):
        if CBW.InfixOp.value in item:
            stmt = item[CBW.InfixOp.value]
            left = stmt[CBW.lhe.value]
            infix_op = stmt[CBW.infix_op.value]
            right = stmt[CBW.rhe.value]
            delt_left = self.item_2_smt(left)
            delt_right = self.item_2_smt(right)
            return self.mkInfixTerm(delt_left, infix_op, delt_right)

        elif CBW.PrefixOp.value in item:
            stmt = item[CBW.PrefixOp.value]
            prefix_op = stmt[CBW.prefix_op.value]
            right = stmt[CBW.rhe.value]
            delt_right = self.item_2_smt(right)
            return self.mkPrefixTerm(prefix_op, delt_right)

        elif CBW.Variable.value in item:
            js_variable = item[CBW.Variable.value]
            name = js_variable[CBW.name.value]
            # name_prefix = self.component_name_mapping(name_prefix)
            access = js_variable[CBW.access.value]
            is_component, name_suffix = self.get_access(access)
            if not is_component:
                name = name + name_suffix
            variable = self.__variable_dic[name]
            if variable.type() is CBW.Signal:
                return variable.toSmt()
            elif variable.type() is CBW.Var:
                return variable.toSmt()
            elif variable.type() is CBW.Component:
                call_name = name_suffix
                signal = variable.get_io_signal(call_name)
                return signal.toSmt()

        elif CBW.Number.value in item:
            value_type = item[CBW.Number.value][1][0]
            if value_type == 0:
                return self.__exp_slv.FF_zero()
            else:
                value = item[CBW.Number.value][1][1][0]
                return self.__exp_slv.FF_number(value)

        else:
            MyItemError(item)

    def getVarStmtValue(self, stmt):
        if CBW.Number.value in stmt:
            cond = stmt[CBW.Number.value][1][0]
            if cond == 0:
                return 0
            else:
                return stmt[CBW.Number.value][1][1][0]
        elif CBW.Variable.value in stmt:
            variable = stmt[CBW.Variable.value]
            var_name = variable[CBW.name.value]
            access = variable[CBW.access.value]
            is_component, suffix = self.get_access(access)
            var = self.__variable_dic[var_name + suffix]
            if var.type() == CBW.Var:
                return var.value
            elif var.type() == CBW.Signal:
                return var.toSmt()
        elif CBW.InfixOp.value in stmt:
            stmt = stmt[CBW.InfixOp.value]
            left = stmt[CBW.lhe.value]
            op = stmt[CBW.infix_op.value]
            right = stmt[CBW.rhe.value]
            left_value = self.getVarStmtValue(left)
            right_value = self.getVarStmtValue(right)
            return self.dealVarInfixOp(left_value, op, right_value)
        elif CBW.PrefixOp.value in stmt:
            stmt = stmt[CBW.InfixOp.value]
            op = stmt[CBW.infix_op.value]
            right = stmt[CBW.rhe.value]
            right_value = self.getVarStmtValue(right)
            return self.dealVarPrefixOp(op, right_value)

    # 这里计算的是var对象和var对象，当然也有可能是signal
    def dealVarInfixOp(self, left, op, right):
        if isinstance(left, int) and isinstance(right, int):
            return calculate_deterministic_infixOp(left, op, right, self.__exp_slv.prime())
        if isinstance(left, int):
            left = self.__exp_slv.FF_number(left)
        if isinstance(right, int):
            right = self.__exp_slv.FF_number(right)
        return self.mkInfixTerm(left, op, right)

    def dealVarPrefixOp(self, op, right):
        if isinstance(right, int):
            return calculate_deterministic_prefixOp(op, right, self.__exp_slv.prime())
        else:
            return self.mkPrefixTerm(op, right)

    # 处理中缀表达式
    def mkInfixTerm(self, left, op, right):
        # print(f'{left} {op} {right}')
        if op == EIO.Add.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, left, right)

        elif op == EIO.Sub.value:
            # 取负
            neg_right = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, right)
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_ADD, left, neg_right)

        elif op == EIO.Mul.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, left, right)

        elif op == EIO.Div.value:
            # 取乘法逆元
            inv_right = self.__exp_slv.slv().mkConst(self.__exp_slv.F(), f'1 / {right}')
            mult = self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, right, inv_right)
            eq = self.__exp_slv.mkTerm(Kind.EQUAL, mult, self.__exp_slv.FF_one())
            self.circuit_terms.append(eq)
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_MULT, left, inv_right)

        elif op == EIO.Eq.value:
            return self.__exp_slv.mkTerm(Kind.EQUAL, left, right)

        elif op == EIO.NotEq.value:
            Eq = self.__exp_slv.mkTerm(Kind.EQUAL, left, right)
            return self.__exp_slv.mkTerm(Kind.NOT, Eq)

        elif op == EIO.Greater.value:
            return self.__exp_slv.mkFFTerm_Gt(left, right)

    def mkPrefixTerm(self, op, right):
        if op == EPO.Sub.value:
            return self.__exp_slv.mkTerm(Kind.FINITE_FIELD_NEG, right)

    def equality_2_smt(self, equality):
        left = equality[CBW.lhe.value]
        right = equality[CBW.rhe.value]
        delt_left = self.item_2_smt(left)
        delt_right = self.item_2_smt(right)
        constraint = self.__exp_slv.mkTerm(Kind.EQUAL, delt_left, delt_right)
        self.constraint_terms.append(constraint)

    # 生成变量，如signal等在具体component中的名字
    def build_id_name(self, call_name):
        return f'{self.__id_name}.{call_name}'

    def deal_while(self, item):
        cond = item[CBW.cond.value]
        block = item[CBW.stmt.value][CBW.Block.value]
        while self.check_cond(cond):
            self.block_2_smt(block)

    def deal_ifThenElse(self, item):
        cond = item[CBW.cond.value]
        if_case = item[CBW.if_case.value]
        else_case = item[CBW.else_case.value]
        if self.check_cond(cond):
            self.stmt_2_smt(if_case)
        else:
            self.stmt_2_smt(else_case)

    def check_cond(self, cond):
        return self.getVarStmtValue(cond)



