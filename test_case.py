import os
import shutil

from cvc5 import Kind

from Convert.AdditionalOperations import ExpandedCVC5
from Tools.ColorPrint import colorPrint, COLOR
from verify import compile_case, pick_information


class Mapping:
    # Map A ---> B
    def __init__(self, signals_A, signals_B, Map_rule=0, Map_data=None):
        self.__signals_A = signals_A
        self.__signals_B = signals_B
        self.__AB_dic = dict()      # id --> [A,B]
        if Map_rule == 0:       # 同名匹配
            for id_name, signal_A in self.__signals_A.items():
                signal_B = self.__signals_B[id_name]
                self.__AB_dic[id_name] = [signal_A, signal_B]
        elif Map_rule == 1:     # A加上前缀匹配B
            for id_name, signal_A in self.__signals_A.items():
                signal_B = self.__signals_B[f'{Map_data}{id_name}']
                self.__AB_dic[id_name] = [signal_A, signal_B]
        elif Map_rule == 2:     # A减去前缀匹配B
            for id_name, signal_A in self.__signals_A.items():
                signal_B = self.__signals_B[id_name.removeprefix(Map_data)]
                self.__AB_dic[id_name] = [signal_A, signal_B]
        elif Map_rule == 3:     # 依照Map匹配 A->B
            for id_name, signal_A in self.__signals_A.items():
                signal_B = self.__signals_B[Map_data[id_name]]
                self.__AB_dic[id_name] = [signal_A, signal_B]
    
    def get_Pair(self, signal):
        pair = self.__AB_dic[signal.id_name]
        return pair

    def get_setting_terms(self, exp_slv):
        terms = list()
        for id_name, signal_pair in self.__AB_dic.items():
            term = exp_slv.mkTerm(Kind.EQUAL, signal_pair[0].toSmt(), signal_pair[1].toSmt())
            terms.append(term)
        return terms


if __name__ == '__main__':
    raw_path = '../../Test_CASES/Simple/raw.circom'
    generate_path_list = list()
    generate_path_list.append('../../Test_CASES/Simple/generate.circom')

    temp_file_dir = './temp_file'
    ast_builder_path = './dependence/AstBuilder'
    compiler_path = './dependence/circom'
    prime_name = 'bn128'
    polish = 'O2'
    can_deal = True
    raw_terms = list()
    generate_terms_list = list()

    # 检查临时文件夹是否存在，不存在就创建
    if not os.path.exists(temp_file_dir) or not os.path.isdir(temp_file_dir):
        os.makedirs(temp_file_dir)

    raw_name = os.path.splitext(os.path.basename(raw_path))[0]

    # 初始化求解器
    exp_slv = ExpandedCVC5(prime_name)

    # 考察案例文件夹是否存在，如果存在就先删掉再重建
    case_temp_path = f'{temp_file_dir}/{raw_name}_group'
    if os.path.exists(case_temp_path) and os.path.isdir(case_temp_path):
        shutil.rmtree(case_temp_path)
    os.makedirs(case_temp_path)

    # 处理raw
    # 编译raw
    raw_temp_path = f'{case_temp_path}/{raw_name}'
    os.makedirs(raw_temp_path)
    raw_compile_passed = compile_case(compiler_path, polish, raw_path, prime_name, raw_temp_path)
    # 获取raw所对应约束
    if raw_compile_passed:
        raw_terms = pick_information(ast_builder_path, raw_path, raw_temp_path, raw_name, exp_slv)

    # 处理generate
    for generate_path in generate_path_list:
        # 编译generate
        generate_name = os.path.splitext(os.path.basename(generate_path))[0]
        generate_temp_path = f'{case_temp_path}/{generate_name}'
        os.makedirs(generate_temp_path)
        generate_compile_passed = compile_case(compiler_path, polish, generate_path, prime_name, generate_temp_path)
        generate_terms = pick_information(ast_builder_path, generate_path, generate_temp_path, generate_name, exp_slv)
        generate_terms_list.append(generate_terms)
        # 全部的signals
        signals_dic = dict()
        signals_dic.update(raw_terms.signals_dic)
        signals_dic.update(generate_terms.signals_dic)
        # 比较calculate 一致性
        colorPrint('The SMT statements of raw calculate terms:', COLOR.YELLOW)
        colorPrint(raw_terms.calculate_terms)
        colorPrint('The SMT statements of generate calculate terms:', COLOR.YELLOW)
        colorPrint(generate_terms.calculate_terms)
        input_mapping = Mapping(raw_terms.input_signals_dic, generate_terms.input_signals_dic, 2, 'raw_')
        input_setting = input_mapping.get_setting_terms(exp_slv)
        output_mapping = Mapping(raw_terms.output_signals_dic, generate_terms.output_signals_dic, 2, 'raw_')
        output_setting = output_mapping.get_setting_terms(exp_slv)
        setting_terms = list()
        setting_terms.extend(raw_terms.calculate_terms)
        setting_terms.extend(generate_terms.calculate_terms)
        setting_terms.extend(input_setting)
        calculate_compare_result = exp_slv.check_satisfy_with_settings(output_setting,
                                                                       setting_terms)
        colorPrint(f'calculate check passed: {calculate_compare_result}', COLOR.GREEN)
        colorPrint()

        # 比较constraint 一致性
        colorPrint('The SMT statements of raw constraint terms:', COLOR.YELLOW)
        colorPrint(raw_terms.constraint_terms)
        colorPrint('The SMT statements of generate constraint terms:', COLOR.YELLOW)
        colorPrint(generate_terms.constraint_terms)
        # 计算settings
        mapping = Mapping(raw_terms.signals_dic, generate_terms.signals_dic, 2, 'raw_')
        setting = mapping.get_setting_terms(exp_slv)
        constraint_compare_result = exp_slv.check_equality_with_settings(raw_terms.constraint_terms,
                                                                         generate_terms.constraint_terms,
                                                                         setting,
                                                                         list(signals_dic.values())
                                                                         )
        colorPrint(f'constraint check passed: {constraint_compare_result}', COLOR.GREEN)