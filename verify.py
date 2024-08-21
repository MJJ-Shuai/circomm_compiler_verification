import json
import subprocess
import sys
import os
import shutil

from Elements.Circuit.BuildinWords import *
from Elements.Circuit.Component import Component
from Elements.Circuit.Template import Template
from Elements.Directory.FrElement import *
from OutcomeDeal.ConstranitsDeal import ConstraintsDealer
from Tools.ColorPrint import *

from Tools.DealSym import SymDataDic
from cvc5 import Kind


# demo_name: name of the ast file in the form of json
# prime: the large prime that defines the finite field
def deal_ast(ast_path, exp_slv):
    # 打开JSON文件
    with open(ast_path, 'r') as f:
        # 加载JSON数据
        data = json.load(f)

    # 初始化Template
    js_definitions = data[CBW.definitions.value]
    Template.init_definitions(js_definitions)

    # 获取main component
    colorPrint(f'Signals and Vars:', COLOR.YELLOW)

    js_main_component = data[CBW.main_component.value]
    main_component = Component.main_component(js_main_component, exp_slv)

    return main_component


def try_deal_ast(ast_path, exp_slv):
    outcome = True
    colorPrint('=========== DEALING AST FILE ===========', COLOR.GREEN)
    colorPrint(f'AST PATH : {ast_path}', COLOR.YELLOW)

    try:
        deal_ast(ast_path, exp_slv)
    except Exception as e:
        colorPrint('!!!!!!!! Exception Happened !!!!!!!!', COLOR.RED)
        colorPrint(e.with_traceback(None))
        outcome = False

    # colorPrint('=========== DEALING ENDS ===========', COLOR.GREEN)
    colorPrint()
    return outcome


def run_demos():
    # prime = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    prime = 29

    demo_name_list = ['array',
                      'compare',
                      'data2',
                      'data3',
                      'iszero',
                      'parameters',
                      'parameters2',
                      'Powers',
                      'simple',
                      'simple2',
                      'square',
                      'raw',
                      'generate',
                      'signal2var',
                      'ast']
    passed_num = 0
    for demo_name in demo_name_list:
        ast_path = f'./demos/{demo_name}.json'
        # 初始化求解器
        exp_slv = ExpandedCVC5(prime)
        outcome = try_deal_ast(ast_path, exp_slv)
        if outcome:
            passed_num += 1

    colorPrint('*********** DEMO REPORT ***********', COLOR.YELLOW)
    colorPrint(f'Demos num  = {len(demo_name_list)}')
    colorPrint(f'Passed num = {passed_num}')
    colorPrint(f'Failed num = {len(demo_name_list) - passed_num}')
    colorPrint('*********** REPORT ENDS ***********', COLOR.YELLOW)


class CircuitTerms:
    def __init__(self, main_component, compiled_calculate_terms, compiled_constraint_terms):
        self.main_component = main_component
        self.input_signals_dic = main_component.get_input_signals_dic()
        self.output_signals_dic = main_component.get_output_signals_dic()
        self.signals_dic = main_component.get_all_signals_dic()
        self.calculate_terms = main_component.get_all_circuit_terms()
        self.constraint_terms = main_component.get_all_constraint_terms()
        self.compiled_calculate_terms = compiled_calculate_terms
        self.compiled_constraint_terms = compiled_constraint_terms


def compile_case(compiler_path, polish, raw_path, prime_name, case_temp_path):
    if os.path.exists(case_temp_path) and os.path.isdir(case_temp_path):
        shutil.rmtree(case_temp_path)
    os.makedirs(case_temp_path)

    colorPrint('========== COMPILING CIRCUIT ==========', COLOR.GREEN)
    compile_cmd = [compiler_path, f'--{polish}', raw_path, '--prime', prime_name, '--r1cs', '--sym', '--c', '--json', '-o', case_temp_path]
    result = subprocess.run(compile_cmd, capture_output=True, text=True)
    if result.returncode == 0:
        print(result.stdout)
        return True
    else:
        print(result.stderr)
        return False


def pick_information(ast_builder_path, raw_path, case_temp_path, circuit_name, exp_slv):
    # 生成 ast
    ast_path = f'{case_temp_path}/ast.json'
    build_ast_cmd = [ast_builder_path, raw_path, ast_path]
    subprocess.run(build_ast_cmd)

    # 处理 ast
    main_component = deal_ast(ast_path, exp_slv)

    # 读取sym文件
    sym_path = f'{case_temp_path}/{circuit_name}.sym'
    all_signals = list(main_component.get_all_signals_dic().values())
    sym_data_dic = SymDataDic(sym_path, all_signals, exp_slv.FF_number(1))

    # 读取dat文件
    dat_path = f'{case_temp_path}/{circuit_name}_cpp/{circuit_name}.dat'
    # deal_dat(dat_path)

    # 读取constraint文件
    cons_path = f'{case_temp_path}/{circuit_name}_constraints.json'
    cons_dealer = ConstraintsDealer(cons_path, exp_slv, sym_data_dic)

    # 获取编译后的计算约束
    compiled_calculate_terms = None

    # 获取编译后的constraint约束
    compiled_constraint_terms = cons_dealer.get_all_terms()

    return CircuitTerms(main_component, compiled_calculate_terms, compiled_constraint_terms)


if __name__ == '__main__':
    can_deal = False
    raw_path = None
    temp_file_dir = './temp_file'
    ast_builder_path = './dependence/AstBuilder'
    compiler_path = './dependence/circom'
    # now = datetime.now()
    # formatted_now = now.strftime("_%Y_%m_%d_%H_%M_%S_%f")[:-3]

    # 检查临时文件夹是否存在，不存在就创建
    if not os.path.exists(temp_file_dir) or not os.path.isdir(temp_file_dir):
        os.makedirs(temp_file_dir)

    sys.argv = list()
    sys.argv.append(0)
    # sys.argv.append('../../Verify_CASES/bug/bug.circom')
    sys.argv.append('../../InputGenerate_CASES/temp2/temp2.circom')
    sys.argv.append('bn128')
    sys.argv.append('O2')

    if len(sys.argv) == 2:
        raw_path = sys.argv[1]
        prime_name = 'bn128'
        polish = 'O1'
        can_deal = True
    elif len(sys.argv) == 4:
        raw_path = sys.argv[1]
        prime_name = sys.argv[2]
        polish = sys.argv[3]
        can_deal = True
    else:
        colorPrint("Wrong Number of Parameters", color=COLOR.RED)
        colorPrint("USAGE: Verify [raw circom file path] [the prime number]")

    circuit_name = os.path.splitext(os.path.basename(raw_path))[0]

    # 初始化求解器
    exp_slv = ExpandedCVC5(prime_name)

    # 考察案例文件夹是否存在，如果存在就先删掉再重建
    case_temp_path = f'{temp_file_dir}/{circuit_name}'
    compile_passed = False
    if can_deal:
        compile_passed = compile_case(compiler_path, polish, raw_path, prime_name, case_temp_path)
        # compile_passed = True

    if compile_passed:
        CircuitTerms = pick_information(ast_builder_path, raw_path, case_temp_path, circuit_name, exp_slv)
        colorPrint('The SMT statements of calculate terms:', COLOR.YELLOW)
        colorPrint(CircuitTerms.calculate_terms)
        colorPrint('The SMT statements of constraint terms:', COLOR.YELLOW)
        colorPrint(CircuitTerms.constraint_terms)
        colorPrint('The SMT statements of calculate terms after compilation:', COLOR.YELLOW)
        colorPrint(CircuitTerms.compiled_calculate_terms)
        colorPrint('The SMT statements of constraint terms after compilation:', COLOR.YELLOW)
        colorPrint(CircuitTerms.compiled_constraint_terms)

        # 比较编译后constraint的等价性
        constraint_compare_result = exp_slv.check_equality(CircuitTerms.constraint_terms,
                                                           CircuitTerms.compiled_constraint_terms,
                                                           list(CircuitTerms.signals_dic.values())
                                                           )

        colorPrint()
        colorPrint(f'constraint check passed: {constraint_compare_result}', COLOR.GREEN)

        # 求取一个可以满足的输入集合
        for term in CircuitTerms.calculate_terms:
            exp_slv.assertFormula(term)

        for term in CircuitTerms.constraint_terms:
            exp_slv.assertFormula(term)

        input_signal_list = list(CircuitTerms.main_component.get_input_signals_dic().values())
        exp_slv.get_model(input_signal_list, True)
