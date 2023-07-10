import argparse
import pathlib
import sys
from typing import Dict, List, Tuple
from uc.uc_ast import *
from uc.uc_block import CFG, EmitBlocks, BasicBlock, Block, ConditionBlock, format_instruction
from uc.uc_interpreter import Interpreter
from uc.uc_parser import UCParser
from uc.uc_sema import NodeVisitor, Visitor
from uc.uc_type import *

binary_ops = {
    "+": "add",
    "-": "sub",
    "*": "mul",
    "/": "div",
    "%": "mod",
    ">": "gt",
    ">=": "ge",
    "<": "lt",
    "<=": "le",
    "==": "eq",
    "!=": "ne",
    "&&": "and",
    "||": "or",
    "!": "not",
}

# Cria um enum das etapas da geração de código
from enum import Enum

class Etapa(Enum):
    GLOBAL_VARIABLES = 1
    ALLOCATE = 2
    CODE_GENERATION = 3

class LoopType(Enum):
    FOR = 1
    WHILE = 2

class Label():
    def __init__(self):
        self.label_count = {}
        self.numberOfForLoops = 0
        self.numberOfWhileLoops = 0

    def make_label(self, label: str) -> str:
        """ Cria uma label e incrementa ela (usada em for, while, assert, ...) """
        if label not in self.label_count:
            self.label_count[label] = 0
        else:
            self.label_count[label] += 1
            label = label + str(self.label_count[label])

        return label
    
    def get_label(self, label: str) -> str:
        """ Retorna o nome da label """
        if self.label_count[label] == 1:
            return label
        return label + '.' + str(self.label_count[label])
    
    def get_loop_label(self, loopType: LoopType, labelSufix: str) -> str:
        """ Retorna o nome da label do loop """
        if loopType == LoopType.FOR:
            _label = 'for.' + labelSufix
            _num = self.numberOfForLoops
        elif loopType == LoopType.WHILE:
            _label = 'while.' + labelSufix
            _num = self.numberOfWhileLoops
        
        if _num > 1:
            _label = _label + '.' + str(_num)
        return _label
    
    def clear_labels(self):
        """ Limpa todas as labels """
        self.label_count = {}

class Variable():
    def __init__(self):
        self.variables = {}
        self.variablesDeclaredInScope = []
    
    def new_var(self, name: str) -> str:
        """
        Create a new variable.
        """
        if name not in self.variables:
            self.variables[name] = 1
            self.variablesDeclaredInScope[-1].append(name)
        else:
            self.variables[name] += 1
            self.variablesDeclaredInScope[-1].append(name)
    
    def get_var(self, name: str) -> str:
        """
        Get the name of a variable.
        """
        if name in self.variables and self.variables[name] > 1:
            return name + '.' + str(self.variables[name])
        else:
            return name
    
    def create_scope(self):
        """
        Create a new variables scope.
        """
        self.variablesDeclaredInScope.append([])

    def pop_scope(self):
        """
        Pop the last variables scope.
        """
        for var in self.variablesDeclaredInScope[-1]:
            self.variables[var] -= 1
            if self.variables[var] == 0:
                del self.variables[var]
        self.variablesDeclaredInScope.pop()


class CodeGenerator(NodeVisitor):
    """
    Node visitor class that creates 3-address encoded instruction sequences
    with Basic Blocks & Control Flow Graph.
    """

    def __init__(self, viewcfg: bool):
        self.viewcfg: bool = viewcfg
        self.current_block: Block = None

        # version dictionary for temporaries. We use the name as a Key
        self.fname: str = "_glob_"
        self.versions: Dict[str, int] = {self.fname: 0}

        # The generated code (list of tuples)
        # At the end of visit_program, we call each function definition to emit
        # the instructions inside basic blocks. The global instructions that
        # are stored in self.text are appended at beginning of the code
        self.code: List[Tuple[str]] = []

        self.text: List[Tuple[str]] = []  # Used for global declarations & constants (list, strings)

        # TODO: Complete if needed.
        self.etapa = Etapa.GLOBAL_VARIABLES
        self.label = Label()
        self.variable = Variable()
        self.globals = []
        self.returnRegister = None
        self.currentLoopType = None # LoopType.FOR or LoopType.WHILE

    def show(self, buf=sys.stdout):
        _str = ""
        for _code in self.code:
            _str += format_instruction(_code) + "\n"
        buf.write(_str)

    def new_temp(self) -> str:
        """
        Create a new temporary variable of a given scope (function name).
        """
        if self.fname not in self.versions:
            self.versions[self.fname] = 1
        name = "%" + "%d" % (self.versions[self.fname])
        self.versions[self.fname] += 1
        return name

    def new_text(self, typename: str) -> str:
        """
        Create a new literal constant on global section (text).
        """
        name = "@." + typename + "." + "%d" % (self.versions["_glob_"])
        self.versions["_glob_"] += 1
        self.globals.append(typename)
        return name
    
    def new_global(self, name: str):
        """
        Create a new global variable.
        """
        self.globals.append(name)
    
    def get_address(self, node: Node) -> str:
        """
        Get the address of a variable or function.
        """
        if isinstance(node, ID):
            name = node.name
            if name in self.globals:
                return "@" + name
            return "%" + self.variable.get_var(name)
        if isinstance(node, Constant):
            return node.gen_location
        if isinstance(node, FuncCall):
            return "@" + node.name.name
        if isinstance(node, ArrayRef):
            name = node.name.name
            if name in self.globals:
                return "@" + name
            return "%" + self.variable.get_var(name)
        
    def connect_next_block(self, block: Block, blockLabel: str):
        """
        Connect the current block to the next block.
        """
        # Conecta o block
        self.current_block.next_block = block
        block.predecessors.append(self.current_block)
        self.current_block = block

        # Cria label
        inst = (blockLabel + ":",)
        self.current_block.append(inst)

    def create_jump_instruction(self, targetLabel: str):
        """
        Create a jump instruction to a target label.
        """
        inst = ("jump", "%" + targetLabel)
        self.current_block.append(inst)

    # You must implement visit_Nodename methods for all of the other
    # AST nodes.  In your code, you will need to make instructions
    # and append them to the current block code list.
    #
    # A few sample methods follow. Do not hesitate to complete or change
    # them if needed.

    # PROGRAM / FUNCTIONS

    def visit_Program(self, node: Node):
        """Start by visiting all global declarations.
        Then, visit all the function definitions and emit the code stored inside basic blocks."""
        # Visit all of the global declarations
        for _decl in node.gdecls:
            self.visit(_decl)
        # At the end of codegen, first init the self.code with
        # the list of global instructions allocated in self.text
        self.code = self.text.copy()
        # Also, copy the global instructions into the Program node
        node.text = self.text.copy()
        # After, visit all the function definitions and emit the
        # code stored inside basic blocks.
        for _decl in node.gdecls:
            if isinstance(_decl, FuncDef):
                # _decl.cfg contains the Control Flow Graph for the function
                # cfg points to start basic block
                bb = EmitBlocks()
                bb.visit(_decl.cfg)
                for _code in bb.code:
                    self.code.append(_code)

        if self.viewcfg:  # evaluate to True if -cfg flag is present in command line
            for _decl in node.gdecls:
                if isinstance(_decl, FuncDef):
                    dot = CFG(_decl.decl.name.name)
                    dot.view(_decl.cfg)  # _decl.cfg contains the CFG for the function

    def visit_FuncDef(self, node: Node):
        """Initialize the necessary blocks to construct the CFG of the function.
        Visit the function declaration. Visit all the declarations within the function.
        After allocating all declarations, visit the arguments initialization.
        Visit the body of the function to generate its code.
        Finally, setup the return block correctly and generate the return statement (even for void function)."""

        self.etapa = Etapa.ALLOCATE

        # Muda para o escopo da função
        self.fname = node.decl.name.name

        # Adiciona função nas variáveis globais
        self.new_global(node.decl.name.name)

        # Cria o escopo de variáveis da função
        self.variable.create_scope()

        # Cria o bloco principal da função
        node.cfg = BasicBlock(node.decl.name)
        if self.current_block is not None:
            node.cfg.predecessors.append(self.current_block)
            self.current_block.next_block = node.cfg
        self.current_block = node.cfg

        # Visita a declaração da função
        self.visit(node.decl)

        # Aloca uma variavel temporária para o retorno da função, caso não seja void
        _typename = node.type.name
        if _typename != "void":
            self.returnRegister = self.new_temp()
            inst = ("alloc_" + _typename, self.returnRegister)
            self.current_block.append(inst)

        # Visita apenas as declarações de variáveis fase no body
        self.visit(node.body)
        
        # change stage to "code generation"
        self.etapa = Etapa.CODE_GENERATION

        # Visita a declaração da função
        self.visit(node.decl)

        # Visita o código da função
        self.visit(node.body)

        self.label.clear_labels()

        # Cria um bloco de retorno
        ret_block = BasicBlock("%" + "exit")

        # Configura o bloco atual para ser o bloco de retorno
        ret_block.predecessors.append(self.current_block)

        # Cria a instrução de pulo para o retorno
        inst = ("jump", "%" + "exit")
        self.current_block.append(inst)

        # Cria a instrução de saída da função
        inst = ("exit:",)
        ret_block.append(inst)

        # Cria a função de retorno, caso a função retorne void
        if _typename == "void":
            inst = ('return_void',)
            ret_block.append(inst)

        # Cria a função de retorno, caso a função retorne algo
        else:
            _returnTemp = self.new_temp()
            inst = ('load_' + _typename, self.returnRegister, _returnTemp)
            ret_block.append(inst)
            inst = ('return_' + _typename, _returnTemp)
            ret_block.append(inst)

        self.current_block.next_block = ret_block
        self.current_block = None

        # Limpa o escopo de variáveis da função
        self.variable.pop_scope()

        self.etapa = Etapa.GLOBAL_VARIABLES

        # Volta para o escopo global
        self.fname = '_glob_'


    def visit_ParamList(self, node: Node):
        """Just visit all arguments."""
        for _param in node.params:
            self.visit(_param)

    # DECLARATIONS / TYPE

    def visit_GlobalDecl(self, node: Node):
        """Visit each global declaration that is not a function declaration."""
        for _decl in node.decls:
            self.visit(_decl)

    def visit_Decl(self, node: Node):
        """Visit the type of the node (VarDecl, FuncDecl, etc.)."""
        # if decl é FuncDecl
        if isinstance(node.init, FuncDecl):
            # Visita FuncDecl
            self.visit(node.init)

        elif isinstance(node.init, ArrayDecl):
            node.init.decl = node
            node.init.declname = node.name

            # Visita ArrayDecl
            self.visit(node.init)

        # if decl é VarDecl
        elif node.type is not None:
            node.type.decl = node
            node.type.declname = node.name

            # Visita VarDecl
            self.visit(node.type)

    def visit_VarDecl(self, node: Node):
        """Allocate the variable (global or local) with the correct initial value (if any)."""
        if self.etapa == Etapa.GLOBAL_VARIABLES:
            _type = node.decl.init.value
            self.new_global(node.declname.name)
            if node.type.name == "int":
                _type = int(node.decl.init.value)
            inst = ('global_' + node.type.name, self.get_address(node.declname), _type)
            self.text.append(inst)
        if self.etapa == Etapa.ALLOCATE:
            # Se tiver inicialização, visita a inicialização
            if node.decl.init is not None:
                # Visita Constant
                self.visit(node.decl.init)

            # Allocate on stack memory
            _name = node.declname.name
            _type = node.type.name
            self.variable.new_var(_name)
            _varname = self.get_address(node.declname)
            inst = ("alloc_" + _type, _varname)
            self.current_block.append(inst)

        elif self.etapa == Etapa.CODE_GENERATION:
            # Pega o gen_location do ID
            # Visita ID
            self.visit(node.declname)

            # Store optional init val
            _init = node.decl.init
            inst = None
            if _init is not None and isinstance(_init, Constant):
                inst = (
                    "store_" + node.type.name,
                    self.get_address(_init),
                    self.get_address(node.declname),
                )
                self.current_block.append(inst)
            elif _init is not None and isinstance(_init, ID) or isinstance(_init, BinaryOp):
                inst = (
                    "store_" + node.type.name,
                    _init.gen_location,
                    self.get_address(node.declname),
                )
                self.current_block.append(inst)
            elif hasattr(node, 'gen_location'):
                inst = (
                    "store_" + node.type.name,
                    node.gen_location,
                    self.get_address(node.declname),
                )
                self.current_block.append(inst)

            if inst is not None:
                self.current_block.append(inst)

    def visit_ArrayDecl(self, node: Node):
        """Visit the node type of an array declaration."""
        # Aloca coisas globais
        if self.etapa == Etapa.GLOBAL_VARIABLES or self.etapa == Etapa.ALLOCATE:
            _inst_name = "global_" + node.type.type.name
            _typename = None
            _list = []

            if node.decl.init is not None:
                # Configurar dimensão do array
                if hasattr(node.decl.init, 'dimension'):
                    for dim in node.decl.init.dimension:
                        _inst_name += "_" + str(dim)
                
                if hasattr(node.decl.init, 'exprs'):
                    for elem in node.decl.init.exprs:
                        _value = elem.value
                        if node.type.type.name == "int":
                            _value = int(elem.value)
                        _list.append(_value)

            if self.etapa == Etapa.GLOBAL_VARIABLES:
                self.new_global(node.type.declname.name)
                _typename = "@" + node.type.declname.name
            elif self.etapa == Etapa.ALLOCATE:
                _typename = self.new_text("const_" + node.type.declname.name)

            inst = (_inst_name, _typename, _list)
            self.text.append(inst)
        
        # Aloca espaço para variáveis
        if self.etapa == Etapa.ALLOCATE:
            _name = node.declname.name
            _type = node.type.type.name

            if hasattr(node.decl.init, 'dimension'):
                for dim in node.decl.init.dimension:
                    _type += "_" + str(dim)

            self.variable.new_var(_name)
            _varname = self.get_address(node.declname)

            inst = ("alloc_" + _type, _varname)
            self.current_block.append(inst)

    def visit_FuncDecl(self, node: Node):
        """Generate the function definition (including function name, return type, and argument types).
        Generate the entry point for the function, allocate a temporary for the return statement (if not a void function),
        and visit the arguments."""
        if self.etapa == Etapa.ALLOCATE:
            _funcType = node.type.type.name
            _funcName = node.type.declname.name
            _paramList = []

            # Cria a definição da função (FALTA OS ARGUMENTOS)
            inst = ("define_" + _funcType, "@" + _funcName, _paramList)
            self.current_block.append(inst)

            # Cria a instrução de entrada da função
            inst = ("entry:",)
            self.current_block.append(inst)

            # Cria um novo bloco para a função
            if node.params is not None:
                self.visit(node.params)

                # Cria array de argumentos
                for _param in node.params.params:                    
                    # Cria gen_location do argumento
                    _param.type.gen_location = self.new_temp()

                    # Adiciona o argumento na lista de argumentos
                    _paramList.append((_param.type.uc_type.typename, _param.type.gen_location))
        elif self.etapa == Etapa.CODE_GENERATION:
            # Cria um novo bloco para a função
            if node.params is not None:
                self.visit(node.params)

    def visit_DeclList(self, node: Node):
        """Visit all the declarations that appear inside a for statement."""
        # Visita todas as declarações
        for _decl in node.decls:
            self.visit(_decl)

    def visit_Type(self, node: Node):
        """Do nothing: just pass."""
        pass

    # STATEMENTS

    def visit_If(self, node: Node):
        """Generate code for the If statement.
        Generate the evaluation of the condition, create the required blocks and the branch for the condition.
        Move to the first block, generate the statement related to the 'then' branch, and create the branch to exit.
        If there is an 'else' block, generate it in a similar way."""
        # Visita a condição
        self.visit(node.cond)

        # Cria as labels do if
        thenLabel = self.label.make_label('if.then')
        ifFalseLabel = self.label.make_label('if.end')
        exitIfLabel = self.label.make_label('if.exit')

        # Cria a branch para os blocos do if
        branch = ('cbranch', node.cond.gen_location, "%" + thenLabel, "%" + ifFalseLabel)
        self.current_block.append(branch)

        # Cria o blocos
        thenBlock = BasicBlock(thenLabel)
        ifFalseBlock = BasicBlock(ifFalseLabel)
        exitIfBlock = BasicBlock(exitIfLabel)

        # Conecta bloco do then
        self.connect_next_block(thenBlock, thenLabel)

        # Visita o then
        self.visit(node.iftrue)

        # Cria a instrução de pulo para o final do if
        self.create_jump_instruction(exitIfLabel)
        
        # Conecta o bloco do if false
        self.connect_next_block(ifFalseBlock, ifFalseLabel)

        # Visita o if false
        if node.iffalse is not None:
            self.visit(node.iffalse)

        # Cria a instrução de pulo para o final do if
        self.create_jump_instruction(exitIfLabel)
        
        # Conecta o bloco do exit if
        self.current_block.next_block = exitIfBlock
        exitIfBlock.predecessors.append(self.current_block)

        # Cria label do exit if
        inst = (exitIfLabel + ":",)
        self.current_block.append(inst)


    def visit_For(self, node: Node):
        """Generate code for the For statement.
        Generate the initialization of the For and create all the required blocks.
        Then, generate the jump to the condition block and generate the condition and the correct conditional branch.
        Generate the body of the For followed by the jump to the increment block.
        Generate the increment and the correct jump."""

        # Cria um novo escopo de variáveis
        self.variable.create_scope()

        # Determina o loop atual
        self.currentLoopType = LoopType.FOR

        # Alocar declarações do for
        self.etapa = Etapa.ALLOCATE
        self.visit(node.init) # Visita DeclList
        self.etapa = Etapa.CODE_GENERATION

        # Visita a inicialização
        self.visit(node.init)

        # Cria as labels do for
        condLabel = self.label.make_label("for.cond")
        bodyLabel = self.label.make_label("for.body")
        endLabel = self.label.make_label("for.end")
        incLabel = self.label.make_label("for.inc")

        # Cria os blocos do for
        condBlock = ConditionBlock(condLabel)
        bodyBlock = BasicBlock(bodyLabel)
        endBlock = BasicBlock(endLabel)
        incBlock = BasicBlock(incLabel)

        # Cria a instrução de jump para o bloco de condição
        jump = ('jump', "%" + condLabel)
        self.current_block.append(jump)

        # Conecta os blocos ao bloco de condição
        condBlock.taken = bodyBlock
        condBlock.fall_through = endBlock

        # Conecta o bloco de condição
        self.connect_next_block(condBlock, condLabel)

        # Visita a condição
        self.visit(node.cond)

        # Cria a instrução de branch para os labels do for
        branch = ('cbranch', node.cond.gen_location, "%" + bodyLabel, "%" + endLabel)
        self.current_block.append(branch)

        # Conecta o bloco do body
        self.connect_next_block(bodyBlock, bodyLabel)

        # Visita o body
        self.visit(node.body)

        # Cria a instrução de jump para o bloco de incremento
        jump = ('jump', "%" + incLabel)
        self.current_block.append(jump)

        # Conecta o bloco do incremento
        self.connect_next_block(incBlock, incLabel)

        # Visita o incremento
        self.visit(node.next)

        # Cria a instrução de jump para o bloco de condição
        jump = ('jump', "%" + condLabel)
        self.current_block.append(jump)

        # Conecta o bloco de end
        self.connect_next_block(endBlock, endLabel)

        # Limpa o escopo de variáveis
        self.variable.pop_scope()

    def visit_While(self, node: Node):
        """Generate code for the While statement.
        The generation of While is similar to For except that it does not require the part related to initialization and increment."""

        # Cria um novo escopo de variáveis
        self.variable.create_scope()

        # Etapa de alocar declarações
        self.etapa = Etapa.ALLOCATE

        self.visit(node.cond)
        self.visit(node.body)
        
        # Etapa de gerar código
        self.etapa = Etapa.CODE_GENERATION

        # Cria as labels do while
        condLabel = self.label.make_label("while.cond")
        bodyLabel = self.label.make_label("while.body")
        endLabel = self.label.make_label("while.end")

        # Cria os blocos do while
        condBlock = ConditionBlock(condLabel)
        bodyBlock = BasicBlock(bodyLabel)
        endBlock = BasicBlock(endLabel)

        # Cria a instrução de jump para o bloco de condição
        jump = ('jump', "%" + condLabel)
        self.current_block.append(jump)

        # Conecta o bloco de condição
        self.connect_next_block(condBlock, condLabel)

        # Visita a condição
        self.visit(node.cond)

        # Cria a instrução de branch para os labels do while
        branch = ('cbranch', node.cond.gen_location, "%" + bodyLabel, "%" + endLabel)
        self.current_block.append(branch)

        # Conecta o bloco do body
        self.connect_next_block(bodyBlock, bodyLabel)

        # Visita o body
        self.visit(node.body)

        # Cria a instrução de jump para o bloco de condição
        jump = ('jump', "%" + condLabel)
        self.current_block.append(jump)

        # Conecta o bloco de end
        self.connect_next_block(endBlock, endLabel)

        # Limpa o escopo de variáveis
        self.variable.pop_scope()


    def visit_Compound(self, node: Node):
        """Visit the list of block items (declarations or statements) within a Compound statement."""
        if node.citens is None:
            return

        # Visita apenas as declarações
        if self.etapa == Etapa.ALLOCATE:
            for _decl in node.citens:
                if isinstance(_decl, Decl):
                    self.visit(_decl)

        # Visita tudo
        if self.etapa == Etapa.CODE_GENERATION:
            for element in node.citens:
                self.visit(element)

    def visit_Assignment(self, node: Node):
        """Generate code for the Assignment statement.
        Visit the right side and load the value according to its type.
        Then, visit the left side and generate the code according to the assignment operator and the type of the expression (ID or ArrayRef)."""
        self.visit(node.rvalue)

        if isinstance(node.lvalue, ArrayRef):
            _type = node.lvalue.uc_type.type.typename
        else:
            _type = node.lvalue.uc_type.typename
        inst = ('store_' + _type, node.rvalue.gen_location, self.get_address(node.lvalue))
        self.current_block.append(inst)

    def visit_Break(self, node: Node):
        """Generate a jump instruction to the current exit label."""
        # Cria a instrução de pulo para o final do loop atual
        _label = self.label.get_loop_label(LoopType.FOR, "end")

        inst = ("jump", "%" + _label)
        self.current_block.append(inst)

    def visit_FuncCall(self, node: Node):
        """Generate code for the Function Call statement.
        Start by generating the code for the arguments.
        For each argument, visit the expression and generate a param_type instruction with its value.
        Then, allocate a temporary for the return value and generate the code to call the function."""
        node.gen_location = self.new_temp()

        _funcName = self.get_address(node)
        
        if isinstance(node.args, ExprList):
            for arg in node.args.exprs:
                self.visit(arg)
                inst = ('param_' + arg.uc_type.typename, arg.gen_location)
                self.current_block.append(inst)
        else:
            self.visit(node.args)
            inst = ('param_' + node.args.uc_type.typename, node.args.gen_location)
            self.current_block.append(inst)

        inst = ('param')

        inst = ('call_' + node.uc_type.type.typename, _funcName, node.gen_location)
        self.current_block.append(inst)

    def visit_Assert(self, node: Node):
        """Generate code for the Assert statement.
        If the expression is false, issue an error message (assertfail) and terminate.
        If the expression is true, proceed to the next statement.
        Generate code similar to the If block to handle the assertion."""
        
        # Visita a expressão (Binary Op por exemplo)
        self.visit(node.expr)

        # Declara string de erro global para caso o assert falhe
        _target = self.new_text("str")
        inst = ("global_string", _target, 'assertion_fail on ' + str(node.expr.coord))
        self.text.append(inst)

        # Cria as labels do assert
        condLabel = self.label.make_label("assert")
        falseLabel = self.label.make_label("assert.false")
        trueLabel = self.label.make_label("assert.true")

        # Cria os blocos do assert
        condBlock = ConditionBlock(condLabel)
        falseBlock = BasicBlock(falseLabel)
        trueBlock = BasicBlock(trueLabel)

        # Conecta os demais blocos com o bloco de condição
        condBlock.taken = trueBlock
        condBlock.fall_through = falseBlock

        # Coloca o bloco de condição como bloco atual
        condBlock.predecessors.append(self.current_block)
        self.current_block.next_block = condBlock
        self.current_block = condBlock

        # Cria instrução de branch para os blocos de true e false
        inst = ("cbranch", node.expr.gen_location, "%" + trueLabel, "%" + falseLabel)
        self.current_block.append(inst)

        # Monta o bloco do false
        self.connect_next_block(falseBlock, falseLabel)
        inst = ('print_string', _target)
        self.current_block.append(inst)
        inst = ('jump', '%exit')
        self.current_block.append(inst)

        # Monta o bloco do true
        self.connect_next_block(trueBlock, trueLabel)


    def visit_EmptyStatement(self, node: Node):
        """Do nothing, just pass."""
        pass

    def visit_Print(self, node: Node):
        """Generate code for the Print statement.
        If the expression is empty, generate a print_void instruction.
        Otherwise, visit each expression, load it if necessary, and generate a print instruction for each one."""

        # TODO: Load the location containing the expression

        # Formata o opcode corretamente: para print o formato deve ser (print_<opcode>, %<location>)
        _opcodes = []
        _gen_locations = []
        if isinstance(node.expr, ExprList):
            for expr in node.expr.exprs:
                self.visit(expr)

                # Recupera o tipo da expressão
                if isinstance(expr, FuncCall) or isinstance(expr, ArrayRef):
                    _opcodes.append(expr.uc_type.type.typename)
                else:
                    _opcodes.append(expr.uc_type.typename)

                _gen_locations.append(expr.gen_location)
        elif node.expr is not None:
            self.visit(node.expr)

            # Recupera o tipo da expressão
            if isinstance(node.expr, FuncCall) or isinstance(node.expr, ArrayRef):
                _opcodes.append(node.expr.uc_type.type.typename)
            else:
                _opcodes.append(node.expr.uc_type.typename)

            _gen_locations.append(node.expr.gen_location)

        # Create the opcode and append to list
        for i in range(len(_opcodes)):
            inst = ("print_" + _opcodes[i], _gen_locations[i])
            self.current_block.append(inst)

        # TODO: Handle the cases when node.expr is None or ExprList

    def visit_Read(self, node: Node):
        """Generate code for the Read statement.
        For each name, visit it, load it if necessary, and generate a read instruction for each element."""
        pass

    def visit_Return(self, node: Node):
        """Generate code for the Return statement.
        If there is an expression, visit it, load it if necessary, and store its value to the return location.
        Then, generate a jump to the return block if needed. Update the predecessor of the return block."""
        
        # THIS SHOULDN'T HANDLE EXIT FUNCITON, FUNDEF MUST HANDLE THIS
        if node.expr is not None:
            self.visit(node.expr)
            _typename = node.expr.uc_type.typename
            inst = ('store_' + _typename, node.expr.gen_location, self.returnRegister)
            self.current_block.append(inst)

    # EXPRESSIONS

    def visit_Constant(self, node: Node):
        """Generate code for the Constant node.
        If the constant is of type string, create a new global that will contain the value.
        Otherwise, create a new temporary initialized with the value."""
        if node.uc_type.typename == "string":
            _target = self.new_text("str")
            inst = ("global_string", _target, node.value)
            self.text.append(inst)
        else:
            # Create a new temporary variable name
            _target = self.new_temp()
            # Make the SSA opcode and append to list of generated instructions
            if not self.etapa == Etapa.GLOBAL_VARIABLES:
                inst = ("literal_" + node.uc_type.typename, int(node.value), _target)
                self.current_block.append(inst)
        # Save the name of the temporary variable where the value was placed
        node.gen_location = _target

    def visit_ID(self, node: Node):
        """Generate code for the Identifier node.
        Get the name of the temporary (or register) where the value of the variable is stored."""
        # Dá um load na variável se uc_type já foi definido
        if hasattr(node, "uc_type"):
            # Criar o gen_location
            node.gen_location = self.new_temp()

            # Cria a instrução de load
            inst = ("load_" + node.uc_type.typename, self.get_address(node), node.gen_location)
            self.current_block.append(inst)

    def visit_BinaryOp(self, node: Node):
        """Generate code for the Binary Operation node.
        Visit the left and right expressions to generate the code related to them.
        Load their value if they reference an array.
        Create a new instruction with the correct opcode and store its result in a new temporary variable."""
        # Visit the left and right expressions
        self.visit(node.left)
        self.visit(node.right)

        # TODO:
        # - Load the location containing the left expression
        # - Load the location containing the right expression

        # Make a new temporary for storing the result
        target = self.new_temp()

        # Recupera o tipo da chamada da função
        if isinstance(node.left, FuncCall) or isinstance(node.left, ArrayRef):
            _type = node.left.uc_type.type.typename
        else:
            _type = node.left.uc_type.typename

        # Create the opcode and append to list
        opcode = binary_ops[node.op] + "_" + _type
        inst = (opcode, node.left.gen_location, node.right.gen_location, target)
        self.current_block.append(inst)

        # Store location of the result on the node
        node.gen_location = target

    def visit_UnaryOp(self, node: Node):
        """Generate code for the Unary Operation node.
        The generation of unary operations is similar to binary operations except that they have only a single expression."""
        self.visit(node.expr)
        node.gen_location = node.expr.gen_location

    def visit_ExprList(self, node: Node):
        """Do nothing, just pass.
        The Expression List must be treated in the scope that uses it."""
        pass

    def visit_ArrayRef(self, node: Node):
        """Generate code for the Array Reference node.
        Start by visiting the subscript.
        Load the values of the index into a new temporary.
        If the array has multiple dimensions, generate arithmetic instructions to compute the index of the element in the array."""
        # Visita o subscript
        self.visit(node.subscript)

        # Cria temporário para a referência do array
        node.address_location = self.new_temp()

        # Cria instrução para carregar o elemento do array
        inst = ("elem_" + node.uc_type.type.typename, self.get_address(node), node.subscript.gen_location, node.address_location)
        self.current_block.append(inst)

        # Cria temporário para o valor do elemento do array
        node.gen_location = self.new_temp()

        # Cria instrução de load
        inst = ("load_" + node.uc_type.type.typename + "_*", node.address_location, node.gen_location)
        self.current_block.append(inst)

    def visit_InitList(self, node: Node):
        """Evaluate each element of the Initialization List and add its value to the node value (which is a list)."""
        pass


if __name__ == "__main__":

    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file",
        help="Path to file to be used to generate uCIR. By default, this script only runs the interpreter on the uCIR. \
              Use the other options for printing the uCIR, generating the CFG or for the debug mode.",
        type=str,
    )
    parser.add_argument(
        "--ir",
        help="Print uCIR generated from input_file.",
        action="store_true",
    )
    parser.add_argument(
        "--cfg", help="Show the cfg of the input_file.", action="store_true"
    )
    parser.add_argument(
        "--debug", help="Run interpreter in debug mode.", action="store_true"
    )
    args = parser.parse_args()

    print_ir = args.ir
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

    gen = CodeGenerator(create_cfg)
    gen.visit(ast)
    gencode = gen.code

    if print_ir:
        print("Generated uCIR: --------")
        gen.show()
        print("------------------------\n")

    vm = Interpreter(interpreter_debug)
    vm.run(gencode)
