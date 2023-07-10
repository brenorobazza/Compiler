import argparse
import pathlib
import sys
from copy import deepcopy
from typing import Any, Dict, Union
from uc.uc_ast import *
from uc.uc_parser import UCParser
from uc.uc_type import CharType, IntType, StringType, BoolType, VoidType, ArrayType, FuncType


class SymbolTable:
    """Class representing a symbol table.

    `add` and `lookup` methods are given, however you still need to find a way to 
    deal with scopes.

    ## Attributes
    - :attr data: the content of the SymbolTable
    """

    def __init__(self) -> None:
        """ Initializes the SymbolTable. """
        self.__data = [{}]


    @property
    def data(self) -> Dict[str, Any]:
        """ Returns a copy of the SymbolTable.
        """
        return deepcopy(self.__data)

    def create(self) -> None:
        # criar o escopo da função
        #colocar tuduo do dicionario anterior
        self.__data.append({})

    def add(self, name: str, value: Any, index = -1) -> None:
        """ Adds to the SymbolTable.

        ## Parameters
        - :param name: the identifier on the SymbolTable
        - :param value: the value to assign to the given `name`
        """
        self.__data[index][name] = value

    def pop(self) -> None:
        # remove o escopo da função
        self.__data.pop()

    def lookup(self, name: str) -> Union[Any, None]:
        """ Searches `name` on the SymbolTable and returns the value
        assigned to it.

        ## Parameters
        - :param name: the identifier that will be searched on the SymbolTable

        ## Return
        - :return: the value assigned to `name` on the SymbolTable. If `name` is not found, `None` is returned.
        """
        for i in range(len(self.__data)-1, -1, -1):
            if name in self.__data[i]:
                return self.__data[i].get(name)
            
    def lookup_scope(self, name: str) -> Union[Any, None]:
        if name in self.__data[-1]:
            return self.__data[-1].get(name)

    def print(self):
        print(self.__data)


class NodeVisitor:
    """A base NodeVisitor class for visiting uc_ast nodes.
    Subclass it and define your own visit_XXX methods, where
    XXX is the class name you want to visit with these
    methods.
    """

    _method_cache = None

    def visit(self, node):
        """Visit a node."""

        if self._method_cache is None:
            self._method_cache = {}

        visitor = self._method_cache.get(node.__class__.__name__)
        if visitor is None:
            method = "visit_" + node.__class__.__name__
            visitor = getattr(self, method, self.generic_visit)
            self._method_cache[node.__class__.__name__] = visitor

        return visitor(node)

    def generic_visit(self, node):
        """Called if no explicit visitor function exists for a
        node. Implements preorder visiting of the node.
        """
        for _, child in node.children():
            self.visit(child)


class Visitor(NodeVisitor):
    """
    Program visitor class. This class uses the visitor pattern. You need to define methods
    of the form visit_NodeName() for each kind of AST node that you want to process.
    """

    def __init__(self):
        # Initialize the symbol table
        self.symtab = SymbolTable()
        self.return_type = None
        self.has_return = False
        self.doNotCreateScope = False
        self.funcName = ""
        self.isInsineLoop = False
        self.typemap = {
            "int": IntType,
            "char": CharType,
            "string": StringType,
            "bool": BoolType,
            "void": VoidType,
        }
        self.binaryOperations = ["+", "-", "*", "/", "%"]
        self.relationalOperations=["==", "!=", "<", ">", "<=", ">="]
        # TODO: Complete...

    def _assert_semantic(self, condition: bool, msg_code: int, coord, name: str = "", ltype="", rtype=""):
        """Check condition, if false print selected error message and exit"""
        error_msgs = {
            1: f"{name} is not defined",
            2: f"subscript must be of type(int), not type({ltype})",
            3: "Expression must be of type(bool)",
            4: f"Cannot assign type({rtype}) to type({ltype})",
            5: f"Binary operator {name} does not have matching LHS/RHS types",
            6: f"Binary operator {name} is not supported by type({ltype})",
            7: "Break statement must be inside a loop",
            8: "Array dimension mismatch",
            9: f"Size mismatch on {name} initialization",
            10: f"{name} initialization type mismatch",
            11: f"{name} initialization must be a single element",
            12: "Lists have different sizes",
            13: "List & variable have different sizes",
            14: f"conditional expression is type({ltype}), not type(bool)",
            15: f"{name} is not a function",
            16: f"no. arguments to call {name} function mismatch",
            17: f"Type mismatch with parameter {name}",
            18: "The condition expression must be of type(bool)",
            19: "Expression must be a constant",
            20: "Expression is not of basic type",
            21: f"{name} does not reference a variable of basic type",
            22: f"{name} is not a variable",
            23: f"Return of type({ltype}) is incompatible with type({rtype}) function definition",
            24: f"Name {name} is already defined in this scope",
            25: f"Unary operator {name} is not supported",
        }
        if not condition:
            msg = error_msgs[msg_code]  # invalid msg_code raises Exception
            print("SemanticError: %s %s" % (msg, coord), file=sys.stdout)
            sys.exit(1)

    # PROGRAM / FUNCTIONS ==============================================================================================

    def visit_Program(self, node):
        # Visit all of the global declarations
        for _decl in node.gdecls:
            # adicionar _decl na symbol table
            self.visit(_decl)
            # após a visita, é de responsabilidade da funcão visita retirar todas as variaveis do escopo
        # TODO: Manage the symbol table

    def visit_FuncDef(self, node):
        # Cria um novo escopo para a função
        self.symtab.create()

        # Salva o tipo do retorno da função
        self.return_type = node.type
        
        # Essa variável vai ser configurada como True em seus filhos, caso haja retorno
        self.has_return = False

        if node.decl is not None:
            self.visit(node.decl)
        
        if node.body is not None:
            self.doNotCreateScope = True
            self.visit(node.body)

        # Se não tiver retorno dá erro
        if not self.has_return:
            self._assert_semantic(node.type.name == "void", 23, node.body.coord, ltype="void", rtype=self.return_type.name)

        # Remove o escopo da função
        self.symtab.pop()

    def visit_ParamList(self, node):
        # Pegar a função
        _funcType = self.symtab.lookup(self.funcName)

        for child in node.params:
            self.visit(child)
            child.type.uc_type = self.typemap[child.type.type.name]

            # Pega o nome do parametro
            _varName = child.name.name

            # Pega o tipo do parametro
            _varType = self.symtab.lookup(_varName)

            # Adicionar o parametro na FuncType com seu tipo
            _funcType.param_order.append(_varName)
            _funcType.param_symtab[_varName] = _varType

    # Declarations / Type ==============================================================================================

    def visit_Decl(self, node):
        if isinstance(node.init, VarDecl):
            # Pega tipo da declaração
            _type = self.typemap[node.init.primitive.name]

        elif isinstance(node.init, FuncDecl):
            # Pegar o tipo da função
            _type = self.typemap[node.init.type.primitive.name]

            # Criar FuncType
            _type = FuncType(_type)

            # Grava qual a função atual
            if node.init.type.identifier is not None:
                self.funcName = node.init.type.identifier.name
            else:
                self.funcName = node.name.name
        elif isinstance(node.type, ArrayDecl):
            # aqui nesse if temos um array sendo instanciado com init list

            if isinstance(node.init, InitList):
                # se um valor da inicialização não for constante, dá erro
                self.visit(node.init)

                # salva as dimensões do array
                _dimension = []
                _arrayDecl = node.type
                while isinstance(_arrayDecl, ArrayDecl):
                    if _arrayDecl.dim is not None:
                        _dimension.append(int(_arrayDecl.dim.value))
                    _arrayDecl = _arrayDecl.type
                
                # se a lista a init estiver errada
                self._assert_semantic(not node.init.differentSizes, 12, coord=node.name.coord)

                # diferentes tamanhos entre var e inicialização, dá erro
                for i in range(len(_dimension)):
                    if isinstance(node.type.type, ID):
                        self._assert_semantic(node.type.dim == None or _dimension[i] == node.init.dimension[i], 13, node.type.type.declname.coord)
                    else:
                        self._assert_semantic(node.type.dim == None or _dimension[i] == node.init.dimension[i], 13, node.name.coord)

                _len = len(node.init.exprs)
            elif isinstance(node.init, Constant):
                if node.init.type == "string":
                    self._assert_semantic(node.type.dim == len(node.init.value), 9, node.type.type.declname.coord, name=node.name.name)

            _type = ArrayType(self.typemap[node.type.primitive.name], _len)
        elif isinstance(node.init, InitList):
            self._assert_semantic(not isinstance(node.type, VarDecl), 11, node.name.coord, name=node.name.name)
            _type = self.typemap[node.type.primitive.name]
        elif isinstance(node.init, ArrayDecl):
            # Itera até achar uma vardecl
            _varDecl = node.init.type
            while not isinstance(_varDecl, VarDecl):
                _varDecl = _varDecl.type

            # Pegar o tipo do array
            _type = self.typemap[_varDecl.primitive.name]

            # Criar ArrayType
            _type = ArrayType(_type, node.init.dim)
        elif isinstance(node.type, VarDecl):
            _type = self.typemap[node.type.primitive.name]
        else:
            _type = self.typemap[node.type.primitive.name]

        if isinstance(node.type, VarDecl):
            _type = self.typemap[node.type.primitive.name]

            # Verifica se a inicialização tem o tipo correto
            if node.init is not None:
                if isinstance(node.init, ID) or isinstance(node.init, Constant):
                    # Se tiver tipo, pega direto
                    if isinstance(node.init, Constant):
                        _initType = node.init.type
                    # Se não tiver, pega na AST
                    else:
                        _initType = self.symtab.lookup(node.init.name).typename

                    self._assert_semantic(_type.typename == _initType, 10, node.name.coord, name=node.name.name)

        # Adiciona variavel na symbol table
        self._assert_semantic(not self.symtab.lookup_scope(node.name.name), 24, node.name.coord, name=node.name.name)

        # Se for uma função, adiciona no escopo anterior
        if isinstance(_type, FuncType):
            self.symtab.add(node.name.name, _type, 0)
        else:
            self.symtab.add(node.name.name, _type)

        if node.init is not None:
            # Visita child
            self.visit(node.init)

    def visit_VarDecl(self, node):
        # criar node.scope = True  e adicionar variabel na tabela de simbolos
        pass

    def visit_ArrayDecl(self, node):
        # criar node.scope = True  e adicionar variabel na tabela de simbolos
        _varDecl = node
        while not isinstance(_varDecl, VarDecl):
            _varDecl = _varDecl.type

        self._assert_semantic(node.dim != None, 8, coord=_varDecl.declname.coord)

        if isinstance(node.dim, Constant):
            self._assert_semantic(node.dim.value != None and int(node.dim.value) > 0, 8, coord=_varDecl.declname.coord)

        self.visit(node.type)

    def visit_FuncDecl(self, node):
        if node.params is not None:
            self.visit(node.params)

    def visit_DeclList(self, node):
        """
        Visit all of the declarations that appear inside the statement. Append the declaration
        to the list of decls in the current function. This list will be used by the code
        generation to allocate the variables.
        """
        
        for child in node.decls:
            self.visit(child)

    def visit_Type(self, node):
        # Get the matching basic uCType.
        pass

    # Statements =======================================================================================================

    def visit_If(self, node):
        # Visita a condição
        self.visit(node.cond)

        # Verifica se a condição é do tipo bool
        if isinstance(node.cond, ID):
            _type = self.symtab.lookup(node.cond.name)
            self._assert_semantic(_type == self.typemap["bool"], 18, node.cond.coord)
        if isinstance(node.cond, Assignment):
            self._assert_semantic(False, 18, node.cond.coord)

        # # Visita o corpo do if
        self.visit(node.iftrue)

        # # Visita o corpo do else
        if node.iffalse is not None:
            self.visit(node.iffalse)

    def visit_While(self, node):
        self.isInsineLoop = True
        self.visit(node.cond)

        # Tratando casos para BinaryOp, Constant e ID
        _type = node.cond.uc_type
        self._assert_semantic(_type == self.typemap["bool"], 14, node.coord, ltype=_type.typename)
        self.isInsineLoop = False

        self.visit(node.body)
    
    def visit_Read(self, node):
        if not isinstance(node.names, ID):
            # se for um elemento do array, não dá erro
            if (isinstance(node.names, ArrayRef) and (isinstance(node.names.subscript, ID) or isinstance(node.names.subscript, Constant))):
                pass
            elif isinstance(node.names, ExprList):
                self.visit(node.names)
            else:
                self._assert_semantic(False, 22, node.names.coord, name=type(node.names).__name__)

    # Expressions ======================================================================================================

    def visit_BinaryOp(self, node):
        # Visit the left and right expression
        self.visit(node.left)
        self.visit(node.right)

        if isinstance(node.left, ID):
            self._assert_semantic(self.symtab.lookup(node.left.name), 1, node.left.coord, name=node.left.name)
        if isinstance(node.right, ID):
            self._assert_semantic(self.symtab.lookup(node.right.name), 1, node.right.coord, name=node.right.name)

        # case 1: is constant or ID
        if isinstance(node.left, Constant) or isinstance(node.left, ID) or isinstance(node.left, BinaryOp):
            ltype = node.left.uc_type
        if isinstance(node.right, Constant) or isinstance(node.right, ID) or isinstance(node.right, BinaryOp):
            rtype = node.right.uc_type

        if isinstance(node.left, FuncCall):
            ltype = self.symtab.lookup(node.left.name.name).type
        if isinstance(node.right, FuncCall):
            rtype = self.symtab.lookup(node.right.name.name).type

        if isinstance(node.left, ArrayRef):
            ltype = self.symtab.lookup(node.left.name.name)
        if isinstance(node.right, ArrayRef):
            rtype = self.symtab.lookup(node.right.name.name)

        self._assert_semantic(ltype == rtype, 5, node.coord, name=node.op)

        # TODO:
        # - Make sure left and right operands have the same type
        # - Make sure the operation is supported

        # Checa se os elementos da binary op suportam a operação
        if node.op in self.binaryOperations:
            self._assert_semantic(node.op in ltype.binary_ops, 6, node.coord, name=node.op, ltype=ltype.typename)
            self._assert_semantic(node.op in rtype.binary_ops, 6, node.coord, name=node.op, ltype=rtype.typename)

        if node.op in self.relationalOperations:
            node.uc_type = self.typemap["bool"]
        else:
            node.uc_type = ltype

    def visit_UnaryOp(self, node):
        self.visit(node.expr)
        if isinstance(node.expr, Constant):
            constType = node.expr.uc_type
            self._assert_semantic(node.op in constType.unary_ops, 25, node.coord, name=node.op)

    def visit_Compound(self, node):
        # Cria um novo escopo de variáveis na pilha
        hasToCreateScope = not self.doNotCreateScope
        self.doNotCreateScope = False

        if hasToCreateScope:
            self.symtab.create()

        if node.citens != None:
            _citens = node.citens

            if isinstance(_citens, DeclList):
                _citens = _citens.decls

            for statement in _citens:
                self.visit(statement)

        # Remove o escopo de variáveis da pilha
        if hasToCreateScope:
            self.symtab.pop()
        
    def visit_Constant(self, node):
        node.uc_type = self.typemap[node.type]

    def visit_ID(self, node):
        # checar se quando visitar id, ele está em uma declaracao (dai adicionar a simble table) ou se ele está sendo utilizado (checar simble table)
        # self._assert_semantic(self.symtab.lookup(node.name) != None, 1, node.coord, node.name)
        node.uc_type = self.symtab.lookup(node.name)

    def visit_Assignment(self, node):
        # visit right side
        self.visit(node.rvalue)
        _type = None

        # visit left side (must be a location)
        self.visit(node.lvalue)

        # error when right value is not defined
        if isinstance(node.lvalue, ID):
            _type = self.symtab.lookup(node.lvalue.name)
        elif isinstance(node.lvalue.name, ID):
            _type = self.symtab.lookup(node.lvalue.name.name)
        elif isinstance(node.lvalue.name, ArrayRef):
            _varDecl = node.lvalue.name
            while not isinstance(_varDecl, ID):
                _varDecl = _varDecl.name
                
            _type = self.symtab.lookup(_varDecl.name)

        self._assert_semantic(_type, 1, node.lvalue.coord, name=node.lvalue.name)


        # setup left type
        if isinstance(node.lvalue, ID):
            ltype = node.lvalue.uc_type
        elif isinstance(node.lvalue, ArrayRef):
            ltype = self.typemap[str(_type)]

        # setup right type
        rtype = node.rvalue.uc_type
        if isinstance(node.rvalue, ArrayRef) or isinstance(node.rvalue, FuncCall):
            rtype = rtype.type

        self._assert_semantic(ltype == rtype, 4, node.coord, ltype=ltype.typename, rtype=rtype.typename)

        # Check that assignment is allowed
        self._assert_semantic(ltype == rtype, 4, node.coord, ltype=ltype, rtype=rtype)

        # Check that assign_ops is supported by the type
        self._assert_semantic(
            node.op in ltype.assign_ops, 5, node.coord, name=node.op, ltype=ltype
        )

    def visit_Assert(self, node):
        # Visita a expressão
        self.visit(node.expr)

        if isinstance(node.expr, ID):
            _type = self.symtab.lookup(node.expr.name)
            self._assert_semantic(_type == self.typemap["bool"], 3, node.expr.coord)

    def visit_Print(self, node):
        _type = None
        if node.expr is not None:
            self.visit(node.expr)
    
        if isinstance(node.expr, ID):
            _type = self.symtab.lookup(node.expr.name)
        if isinstance(node.expr, FuncCall):
            self._assert_semantic(node.expr.uc_type.type.typename != 'void', 20, node.expr.coord)
        elif type(_type) == ArrayType:
            self._assert_semantic(False, 21, node.expr.coord, name=node.expr.name)
        # Just visit each expression and check if it is of basic type. Returns an error otherwise.
        # for expr in node.exprs:
        #     self.visit(expr)
        #     self._assert_semantic(expr.uc_type in self.basic_types, 3, node.coord)
    
    def visit_FuncCall(self, node):
        _name = node.name.name
        _funcType = self.symtab.lookup(_name)
        node.uc_type = _funcType

        if node.args is not None:
            self.visit(node.args)

        # verifica se o numero de argumentos é diferente
        if isinstance(node.args, ExprList):
            self._assert_semantic(len(node.args.exprs) == len(_funcType.param_order), 16, coord=node.coord, name=_name)

        # verifica se o tipo dos parametros batem com os parametros passados
        if isinstance(node.args, ExprList):
            for i in range(len(_funcType.param_order)):
                _name = _funcType.param_order[i]
                _arg = node.args.exprs[i]
                
                _argType = _arg.uc_type

                _paramType = _funcType.param_symtab[_name]
                self._assert_semantic(_argType == _paramType, 17, coord=_arg.coord, name=_name)

        # primeiro se existe na symbol table
        typeRecived = self.symtab.lookup(node.name.name)

        if typeRecived == None:
            # dar erro
            pass

        # segundo se ele e funcao
        else:
            if not isinstance(typeRecived, FuncType):
                self._assert_semantic(isinstance(typeRecived, FuncType), 15, coord=node.coord ,name=node.name.name)

    def visit_Return(self, node):
        # visita a expressao
        if node.expr is not None:
            self.visit(node.expr)
        
        #tipo de retorno esperado: self.return_type
        if isinstance(node.expr, ID):
            _varType = self.symtab.lookup(node.expr.name).typename
            self._assert_semantic(self.return_type.name == _varType, 23, node.coord, ltype=_varType, rtype=self.return_type.name)
        self.has_return = True

    def visit_For(self, node):
        self.isInsineLoop = True
        self.symtab.create()
        self.visit(node.init)
        self.visit(node.cond)
        self.visit(node.next)
        self.visit(node.body)
        self.symtab.pop()
        self.isInsineLoop = False

    def visit_ArrayRef(self, node):
        if isinstance(node.subscript, BinaryOp):
            self.visit(node.subscript)
            _subscriptType = node.subscript.uc_type
        else:
            self.visit(node.subscript)
            _subscriptType = self.symtab.lookup(node.subscript.name)

        self._assert_semantic(_subscriptType == self.typemap['int'], 2, coord=node.subscript.coord, ltype=_subscriptType.typename)

        _name = node.name
        while not isinstance(_name, ID):
            _name = _name.name

        node.uc_type = self.symtab.lookup(_name.name)
    
    def visit_InitList(self, node):
        node.dimension = [len(node.exprs)]
        node.differentSizes = False

        # checo se na lista tenho outras initlist ou já tenho constantes
        if isinstance(node.exprs[0], InitList):
            _firstDimension = None
            for child in node.exprs:
                self.visit(child)
                _firstDimension = node.exprs[0].dimension[0]
                if not (_firstDimension == None or _firstDimension == child.dimension[0]) or child.differentSizes:
                    node.differentSizes = True

            node.dimension.append(node.exprs[0].dimension[0])
        else:
            # checo se todos os elementos são constantes
            for child in node.exprs:
                self._assert_semantic(isinstance(child, Constant), 19, child.coord)
    
    def visit_Break(self, node):
        self._assert_semantic(self.isInsineLoop, 7, coord=node.coord)

    def visit_ExprList(self, node):
        # Visita os elementos da Expr List
        for expr in node.exprs:
            self.visit(expr)

if __name__ == "__main__":
    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "input_file", help="Path to file to be semantically checked", type=str
    )
    args = parser.parse_args()

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
