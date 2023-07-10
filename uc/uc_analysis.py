import argparse
import pathlib
import sys
from typing import List, Tuple
from uc.uc_ast import FuncDef, Node
from uc.uc_block import CFG, format_instruction
from uc.uc_code import CodeGenerator, EmitBlocks
from uc.uc_interpreter import Interpreter
from uc.uc_parser import UCParser
from uc.uc_sema import NodeVisitor, Visitor
import json

from pprint import pprint

class DataFlow(NodeVisitor):
    def __init__(self, viewcfg: bool):
        # flag to show the optimized control flow graph
        self.viewcfg: bool = viewcfg
        # list of code instructions after optimizations
        self.code: List[Tuple[str]] = []
        
        # Reach Definitions Analysis
        self.rd_gen: dict = {}
        self.rd_kill: dict = {}
        self.rd_in: dict = {}
        self.rd_out: dict = {}

        # Liveness Variable Analysis
        self.lv_use: dict = {}
        self.lv_def: dict = {}
        self.lv_in: dict = {}
        self.lv_out: dict = {}

        # Misc
        self.definitions: dict = {}
        self.predecessors: dict = {}
        self.sucessors: dict = {}
        self.enumerated_code: List = []

    def show(self, buf=sys.stdout):
        _str = ""
        for _code in self.code:
            _str += format_instruction(_code) + "\n"
        buf.write(_str)

    def print_rd(self):
        """
        Imprime os conjuntos gen, kill, in e out
        """
        lists = {"gen": self.rd_gen, "kill": self.rd_kill, "in": self.rd_in, "out": self.rd_out}

        print("Reach Definitions Analysis: ==========")
        for key in lists:
            pretty = json.dumps(lists[key], indent=4)
            print(key, " ", pretty)
        print("======================================")

    def print_enumerated_code(self):
        """
        Imprime o código enumerado.
        """
        print("Enumerated code: =====================")
        for idx in range(len(self.enumerated_code)):
            print(idx, self.enumerated_code[idx])
        print("======================================")

    def print_code(self):
        """
        Imprime o código otimizado.
        """
        print("Optimized code: ======================")
        for inst in self.code:
            print(inst)
        print("======================================")
    
    def print_lv(self):
        """
        Imprime os conjuntos use, def, in e out
        """
        lists = {"use": self.lv_use, "def": self.lv_def, "in": self.lv_in, "out": self.lv_out}

        print("Liveness Variable Analysis: ==========")
        for key in lists:
            pretty = json.dumps(lists[key], indent=4)
            print(key, " ", pretty)
        print("======================================")

    def modify_inst_field(self, inst, idx, field):
        """
        Modifica uma instrução do código.
        """
        list_inst = list(inst)
        list_inst[idx] = field
        return tuple(list_inst)

    def add_definition(self, varName, idx):
        """
        Adiciona uma definição à lista de definições.
        """
        if varName not in self.definitions:
            self.definitions[varName] = []
        self.definitions[varName].append(idx)

    def get_definitions(self, varName):
        """
        Recupera as definições de uma variável.
        """
        if varName not in self.definitions:
            return None
        return self.definitions[varName].copy()

    def get_rd_in(self, index):
        """
        Recupera o conjunto in de uma instrução.
        """
        if index not in self.rd_in:
            return []
        return self.rd_in[index].copy()
    
    def get_rd_out(self, index):
        """
        Recupera o conjunto out de uma instrução.
        """
        if index not in self.rd_out:
            return []
        return self.rd_out[index].copy()
    
    def get_lv_in(self, index):
        """
        Recupera conjunto in de uma instrução
        """
        if index not in self.lv_in:
            return []
        return self.lv_in[index].copy()
    
    def get_rd_gen(self, index):
        """
        Recupera o conjunto gen de uma instrução.
        """
        if index not in self.rd_gen:
            return []
        return self.rd_gen[index].copy()
    
    def get_lv_use(self, index):
        """
        Recupera o conjunto use de uma instrução.
        """
        if index not in self.lv_use:
            return []
        return self.lv_use[index].copy()
    
    def get_lv_def(self, index):
        """
        Recupera o conjunto def de uma instrução.
        """
        if index not in self.lv_def:
            return []
        return self.lv_def[index].copy()
    
    def get_rd_kill(self, index):
        """
        Recupera o conjunto kill de uma instrução.
        """
        if index not in self.rd_kill:
            return []
        return self.rd_kill[index].copy()
    
    def calculate_sucessors(self):
        """
        Recupera sucessores de uma instrução
        """
        # Clean predecessors
        self.sucessors = {}

        # Sucessor ultimo elemento é vazio
        self.sucessors[len(self.enumerated_code)-1] = []
        
        # Calcula o sucesspr padrão
        for index in range(0, len(self.enumerated_code) - 1):
            self.add_sucessor(index, index + 1)

        # Calcula os sucessores por jump
        for _branch_index in range(len(self.enumerated_code)):
            inst = self.enumerated_code[_branch_index]

            # inst == jump: Coloca endereço pulante como sucessor do atual
            if inst[0].startswith("jump"):
                _label = inst[1][1:]

                for _label_idx in range(len(self.enumerated_code)):
                    if self.enumerated_code[_label_idx][0][:-1] == _label:
                        self.add_sucessor(_branch_index, _label_idx)
                        break
                
            # inst == cbranch: Coloca como sucessor os endereços que ele pode pular
            elif inst[0] == "cbranch":
                # true label
                _true_label = inst[2][1:]
                for _label_idx in range(len(self.enumerated_code)):
                    if self.enumerated_code[_label_idx][0][:-1] == _true_label:
                        self.add_sucessor(_branch_index, _label_idx)
                        break

                # false label
                _false_label = inst[3][1:]
                for _label_idx in range(len(self.enumerated_code)):
                    if self.enumerated_code[_label_idx][0][:-1] == _false_label:
                        self.add_sucessor(_branch_index, _label_idx)
                        break


    def calculate_predecessors(self):
        """
        Recupera os predecessores de uma instrução.
        """
        # Clean predecessors
        self.predecessors = {}

        # Predecessor da entrada é vazio
        self.predecessors[0] = []

        # Calcula o predecessor padrão
        for index in range(1, len(self.enumerated_code)):
            self.add_predecessor(index, index-1)

        # Calcula os predecessores por jump
        for _branch_index in range(len(self.enumerated_code)):
            inst = self.enumerated_code[_branch_index]

            # inst == jump: Se coloca como predecessor da label para qual ele pula
            if inst[0].startswith("jump"):
                _label = inst[1][1:]

                for _label_idx in range(len(self.enumerated_code)):
                    if self.enumerated_code[_label_idx][0][:-1] == _label:
                        self.add_predecessor(_label_idx, _branch_index)
                        break
                
            # inst == cbranch: Se coloca como predecessor das labels paras quais ele pode pular
            elif inst[0] == "cbranch":
                # true label
                _true_label = inst[2][1:]
                for _label_idx in range(len(self.enumerated_code)):
                    if self.enumerated_code[_label_idx][0][:-1] == _true_label:
                        self.add_predecessor(_label_idx, _branch_index)
                        break

                # false label
                _false_label = inst[3][1:]
                for _label_idx in range(len(self.enumerated_code)):
                    if self.enumerated_code[_label_idx][0][:-1] == _false_label:
                        self.add_predecessor(_label_idx, _branch_index)
                        break

    def get_predecessors(self, index):
        """
        Recupera os predecessores de uma instrução.
        """
        return self.predecessors[index].copy()
    
    def get_sucessors(self, index):
        """
        Recupera os sucessores de uma instrução.
        """
        return self.sucessors[index].copy()

    def add_predecessor(self, line, predecessor):
        """
        Adiciona um predecessor a uma instrução.
        """
        if line not in self.predecessors:
            self.predecessors[line] = []
        if predecessor not in self.predecessors[line]:
            self.predecessors[line].append(predecessor)
    
    def add_sucessor(self, line, sucessor):
        """
        Adiciona um sucessor a uma instrução
        """
        if line not in self.sucessors:
            self.sucessors[line] = []
        if sucessor not in self.sucessors[line]:
            self.sucessors[line].append(sucessor)
    
    def remove_duplicates(self, listObj):
        """
        Remove duplicatas de uma lista.
        """
        return list(dict.fromkeys(listObj))
    
    def count_live_definitions(self, varName, line):
        """
        Conta as definições vivas.
        """
        _definitions = self.get_definitions(varName)
        if _definitions is None:
            return 0

        _in = self.rd_in[line]
        return len(set(_definitions).intersection(_in))

    def enumerate_instructions(self, cfg):
        """
        Enumera as instruções do CFG.
        """
        currentBlock = cfg
        # Itera sobre os blocos do CFG
        while currentBlock is not None:
            # Itera sobre as instruções do bloco
            for inst in currentBlock.instructions:
                self.enumerated_code.append(inst)
            
            currentBlock = currentBlock.next_block

    def reset_global_vars(self):
        """
        Reseta as variáveis globais.
        """
        self.rd_gen = {}
        self.rd_kill = {}
        self.rd_in = {}
        self.rd_out = {}

        self.lv_use = {}
        self.lv_def = {}
        self.lv_in = {}
        self.lv_out = {}

        self.definitions = {}
        self.enumerated_code = []
        self.predecessors = {}

    def visit_Program(self, node: Node):
        # First, save the global instructions on code member
        self.code = node.text[:]  # [:] to do a copy
        for _decl in node.gdecls:
            if isinstance(_decl, FuncDef):
                # Reset global variables
                self.reset_global_vars()

                # Enumera as instruções do CFG
                self.enumerate_instructions(_decl.cfg)

                # Remove loads desnessários de variáveis globais
                self.optimized_global_int_variables()

                # start with Reach Definitions Analysis
                self.buildRD_blocks(_decl.cfg)
                self.computeRD_gen_kill()
                self.computeRD_in_out()
                
                # and do constant propagation optimization
                self.constant_propagation()

                # after do live variable analysis
                self.buildLV_blocks(_decl.cfg)
                self.computeLV_use_def()
                self.computeLV_in_out()
                # and do dead code elimination
                self.deadcode_elimination()

                # after that do cfg simplify (optional)
                self.short_circuit_jumps(_decl.cfg)
                self.merge_blocks(_decl.cfg)
                self.discard_unused_allocs(_decl.cfg)

                # finally save optimized instructions in self.code
                self.appendOptimizedCode(_decl.cfg)

        if self.viewcfg:
            for _decl in node.gdecls:
                if isinstance(_decl, FuncDef):
                    dot = CFG(_decl.decl.name.name + ".opt")
                    dot.view(_decl.cfg)

    def optimized_global_int_variables(self):
        """
        Remove loads desnecessários de variáveis globais.
        """
        _varName = None
        # Itera sobre as instruções do bloco
        for index in range(len(self.enumerated_code)):
            # Recupera a instrução
            inst = self.enumerated_code[index]

            # Se for um load de uma variável global
            if inst[0].startswith("load_int") and inst[1].startswith("@"):
                _varName = inst[1]
                _global_reg = inst[2]

                # Tenta achar outro load da mesma variável global
                self.cp_remove_similar_loads(index+1, _varName, _global_reg)
                break


    def buildRD_blocks(self, cfg):
        """
        Constrói os blocos de análise de definições alcançáveis.
        """
        pass

    def computeRD_gen_kill(self):
        """
        Calcula os conjuntos gen e kill para análise de definições alcançáveis.
        """
        self.rd_gen = {}
        self.rd_kill = {}
        self.definitions = {}
        # Calcula o conjunto de predecessores
        self.calculate_predecessors()

        # Itera sobre as instruções do bloco
        for index in range(len(self.enumerated_code)):
            # Recupera a instrução
            inst = self.enumerated_code[index]

            # Recupera o nome da variável definida
            _varName = None
            if inst[0].startswith("store_"):
                _varName = inst[2]

            # Adiciona a definição à lista de definições
            if _varName is not None:
                self.add_definition(_varName, index)

        # Gera o conjunto gen
        for index in range(len(self.enumerated_code)):
            # Recupera a instrução
            inst = self.enumerated_code[index]

            # Recupera o nome da variável definida
            if inst[0].startswith("store_"):
                self.rd_gen[index] = [index]

        # Gera o conjunto kill
        for index in range(len(self.enumerated_code)):
            # Recupera a instrução
            inst = self.enumerated_code[index]

            # Recupera o nome da variável definida
            _defs = None
            if inst[0].startswith("store_"):
                _defs = self.get_definitions(inst[2])

            # Gera o conjunto kill
            if _defs is not None:
                _defs.remove(index)
                self.rd_kill[index] = _defs

    def computeRD_in_out(self):
        """
        Calcula os conjuntos in e out para análise de definições alcançáveis.
        """
        self.rd_in = {}
        self.rd_out = {}

        _old_in = None
        _old_out = None

        # Itera diversas vezes até que os conjuntos in e out não mudem
        while (_old_in != self.rd_in or _old_out != self.rd_out):
            # Listas antigas de in e out
            _old_in = self.rd_in.copy()
            _old_out = self.rd_out.copy()

            # Gera o conjunto in
            for index in range(len(self.enumerated_code)):
                # Recupera os predecessores
                _preds = self.get_predecessors(index)

                # Recupera o conjunto out
                _in = []
                for _pred in _preds:
                    _in += self.get_rd_out(_pred)
                _in = self.remove_duplicates(_in)
                self.rd_in[index] = _in

            # Gera o conjunto out
            for index in range(len(self.enumerated_code)):
                # Recupera o conjunto gen
                _gen = self.get_rd_gen(index)

                # Recupera o conjunto kill
                _kill = self.get_rd_kill(index)

                # Recupera o conjunto in
                _in = self.get_rd_in(index)

                # Gera o conjunto out
                _out = _gen + [x for x in _in if x not in _kill]
                _out = self.remove_duplicates(_out)
                self.rd_out[index] = _out

    def constant_propagation(self):
        """
        Realiza a otimização de propagação de constantes.
        """
        # Cria uma lista com registradores que não podem ser removidos
        # Registradores de parâmetros
        _params_regs = []
        for _param in self.enumerated_code[0][2]:
            _params_regs.append(_param[1])
        
        # Adiciona o registrador de retorno
        if len(_params_regs) > 0:
            _last_reg = _params_regs[-1]
            _params_regs.append("%" + str(int(_last_reg[1:]) + 1))
        elif not self.enumerated_code[0][0].startswith("define_void"):
            _params_regs.append("%1")

        # Itera sobre as instruções do bloco
        currentIndex = 0
        endIteration = False
        while not endIteration:
            for index in range(currentIndex, len(self.enumerated_code)):
                _store_to_remove: int = None
                _load_to_remove: int = None
                _store_reg: int = None
                _load_reg: int = None
                _varName: str = None

                # Acha um load
                inst = self.enumerated_code[index]
                if self.enumerated_code[index][0].startswith("load_"):
                    # Recupera a variável do load (%a)
                    _varName = inst[1]

                    # Se for uma variável global, vai pra próxima instrução
                    if _varName.startswith("@"):
                        continue

                    # Conta quantas definições da variável chegam no load
                    _live_definitions = self.count_live_definitions(_varName, index)

                    # Se a contagem for maior de 1, então não é possível propagar a constante
                    if _live_definitions > 1:
                        continue

                    # Olha o que tem em cada in (store)
                    _in = self.rd_in[index]
                    for _in_index in range(len(_in)):
                        # Vê qual dos store que tem a variável que o load carrega
                        _store_index = _in[_in_index]
                        _store_varName = self.enumerated_code[_store_index][2]

                        # Se o store ocorrer antes do load
                        # e se a variável do store for a mesma do load
                        if _store_index < index and _varName == _store_varName:
                            _store_to_remove = _store_index

                    # Se achou um store
                    if _store_to_remove is not None:
                        # Recupera o registrador do load (%5)
                        _load_reg = inst[2]

                        # Recupera o registrador do store (%2)
                        _store_reg = self.enumerated_code[_store_to_remove][1]
                        _store_reg_2 = self.enumerated_code[_store_to_remove][2]

                        # Se o registrador do store for um parâmetro, não remove
                        if _store_reg in _params_regs or _store_reg_2 in _params_regs:
                            continue

                        # Recupera o index do load
                        _load_to_remove = index

                        # Substitui todos os registradores subsequentes pelo registrador do store
                        self.cp_replace_subsequent_registers(index, _load_reg, _store_reg)
                        
                        # Itera pelo restante do código para achar outros loads do mesmo store
                        canRemoveStore = self.cp_remove_similar_loads(index+1, _varName, _store_reg)

                        # Remove o load e o store do código
                        inst_to_remove = [_load_to_remove]
                        if canRemoveStore:
                            inst_to_remove.append(_store_to_remove)

                        self.remove_instructions(inst_to_remove)
                        currentIndex = _store_to_remove
                        break

                    continue

                if index == len(self.enumerated_code) - 1:
                    endIteration = True
                    break

            self.computeRD_gen_kill()
            self.computeRD_in_out()

    def remove_instructions(self, instructions_to_remove):
        """
        Remove as instruções do código.
        """
        sorted = instructions_to_remove.copy()
        sorted.sort(reverse=True)
        for index in range(len(sorted)):
            inst_index = sorted[index]
            self.enumerated_code[inst_index] = None
        self.enumerated_code = [x for x in self.enumerated_code if x is not None]
        
    def cp_replace_subsequent_registers(self, starting_index, _load_reg, _reg):
        """
        Realiza a otimização de propagação de constantes.
        """
        # Itera pelo restante do código
        for inst_idx in range(starting_index, len(self.enumerated_code)):
            inst = self.enumerated_code[inst_idx]

            # Substitui todas as ocorrências registradores do load (%5)
            # pelo registrador do store (%2)
            for field_index in range(len(inst)):
                if inst[field_index] == _load_reg:
                    new_inst = self.modify_inst_field(self.enumerated_code[inst_idx], field_index, _reg)
                    self.enumerated_code[inst_idx] = new_inst
    
    def cp_remove_similar_loads(self, starting_index, varName, _reg) -> bool:
        """
        Remove loads que carregam a mesma variável.
        """
        _loads_to_remove = []
        canRemoveStore = True
        # Itera sobre as instruções do bloco
        for inst_idx in range(starting_index, len(self.enumerated_code)):
            inst = self.enumerated_code[inst_idx]

            # Se achar um load da mesma variável, marca-o para remoção
            if inst[0].startswith("load_"):
                # Recupera a variável do load (%a)
                _varName = inst[1]

                if _varName == varName:
                    # Conta quantas definições da variável chegam no load
                    _live_definitions = self.count_live_definitions(_varName, inst_idx)

                    # Se a contagem for maior de 1, então não é possível propagar a constante
                    # e não pode remover o store pai
                    if _live_definitions > 1:
                        canRemoveStore = False
                        break
                    
                    _loads_to_remove.append(inst_idx)

                    # Substitui os registradores do load pelo registrador do store
                    _load_reg = inst[2]
                    self.cp_replace_subsequent_registers(inst_idx+1, _load_reg, _reg)

            # Se achar um outro store da mesma variável, não pode mais remover loads
            if inst[0].startswith("store_"):
                # Recupera a variável do store (%a)
                _varName = inst[2]
                if _varName == varName:
                    break

        # Remove os loads marcados para remoção
        self.remove_instructions(_loads_to_remove)

        return canRemoveStore

    def buildLV_blocks(self, cfg):
        """
        Constrói os blocos de análise de variáveis vivas.
        """
        pass

    def computeLV_use_def(self):
        """
        Calcula os conjuntos use e def para análise de variáveis vivas.
        """
        # Itera de baixo para cima
        for index in range(len(self.enumerated_code) - 1, -1, -1):
            # Recupera a instrução
            inst = self.enumerated_code[index]

            # Caso definição: adiciona ao conjunto def
            if inst[0].startswith("store_"):
                _varName = inst[2]
                self.lv_def[index] = [_varName]

            # Caso uso: adiciona ao conjunto use
            if inst[0].startswith("load_"):
                _varName = inst[1]
                self.lv_use[index] = [_varName]

    def computeLV_in_out(self):
        """
        Calcula os conjuntos in e out para análise de variáveis vivas.
        """
        # Calcula o conjunto de sucessores
        self.calculate_sucessors()

        _old_in = None
        _old_out = None

        # Itera diversas vezes até que os conjuntos in e out não mudem
        while (_old_in != self.lv_in or _old_out != self.lv_out):
            # Listas antigas de in e out
            _old_in = self.lv_in.copy()
            _old_out = self.lv_out.copy()

            # Itera de baixo para cima: gera o conjunto out depois o in
            for index in range(len(self.enumerated_code) - 1, -1, -1):
                # Recuperar sucessores
                _suces = self.get_sucessors(index)

                # Inicializa o conjuntou out
                _out = []

                # Recupera o conjunto out
                for _suce in _suces:
                    _out += self.get_lv_in(_suce)
                _out = self.remove_duplicates(_out)
                self.lv_out[index] = _out

                # Recupera o conjunto use
                _use = self.get_lv_use(index)

                # Recupera o conjunto def
                _def = self.get_lv_def(index)

                # Recupera o conjunto in
                _in = self.get_lv_in(index)

                # Gera o conjunto out
                _in = _use + [x for x in _out if x not in _def]
                _in = self.remove_duplicates(_in)
                self.lv_in[index] = _in
        

    def deadcode_elimination(self):
        """
        Realiza a eliminação de código morto.
        """
        _inst_to_remove = []

        # Itera pela tabela def
        for key in self.lv_def:
            # Recupera o conjunto def
            _def = self.get_lv_def(key)

            # Para cada definição, verifica se ela está no conjunto out
            for _varName in _def:
                if _varName not in self.lv_out[key]:
                    # Se não estiver, marca pra remoção
                    _inst_to_remove.append(key)
        
        # Remove as instruções mortas
        self.remove_instructions(_inst_to_remove)


    def short_circuit_jumps(self, cfg):
        """
        Simplifica os saltos no fluxo de controle.
        """
        pass

    def merge_blocks(self, cfg):
        """
        Mescla blocos no fluxo de controle.
        """
        pass

    def discard_unused_allocs(self, cfg):
        """
        Descarta alocações de memória não utilizadas.
        """
        pass

    def appendOptimizedCode(self, cfg):
        """
        Adiciona as instruções otimizadas ao código.
        """
        for inst in self.enumerated_code:
            self.code.append(inst)


if __name__ == "__main__":

    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file",
        help="Path to file to be used to generate uCIR. By default, this script runs the interpreter on the optimized uCIR \
              and shows the speedup obtained from comparing original uCIR with its optimized version.",
        type=str,
    )
    parser.add_argument(
        "--opt",
        help="Print optimized uCIR generated from input_file.",
        action="store_true",
    )
    parser.add_argument(
        "--speedup",
        help="Show speedup from comparing original uCIR with its optimized version.",
        action="store_true",
        default=True,
    )
    parser.add_argument(
        "--debug", help="Run interpreter in debug mode.", action="store_true"
    )
    parser.add_argument(
        "-c",
        "--cfg",
        help="show the CFG of the optimized uCIR for each function in pdf format",
        action="store_true",
    )
    args = parser.parse_args()

    speedup = args.speedup
    print_opt_ir = args.opt
    create_cfg = args.cfg
    interpreter_debug = args.debug

    # get input path
    input_file = args.input_file
    input_path = pathlib.Path(input_file)

    # check if file exists
    if not input_path.exists():
        print("Input", input_path, "not found", file=sys.stderr)
        sys.exit(1)

    # set error function
    p = UCParser()
    # open file and parse it
    with open(input_path) as f:
        ast = p.parse(f.read())

    sema = Visitor()
    sema.visit(ast)

    gen = CodeGenerator(False)
    gen.visit(ast)
    gencode = gen.code

    opt = DataFlow(create_cfg)
    opt.visit(ast)
    optcode = opt.code
    if print_opt_ir:
        print("Optimized uCIR: --------")
        opt.show()
        print("------------------------\n")

    speedup = len(gencode) / len(optcode)
    sys.stderr.write(
        "[SPEEDUP] Default: %d Optimized: %d Speedup: %.2f\n\n"
        % (len(gencode), len(optcode), speedup)
    )

    vm = Interpreter(interpreter_debug)
    vm.run(optcode)
