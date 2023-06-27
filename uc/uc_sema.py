import argparse
import pathlib
import sys
from copy import deepcopy
from typing import Any, Dict, Union
from uc.uc_ast import ID
from uc.uc_parser import UCParser
from uc.uc_type import CharType, IntType


class SymbolTable:
    """Class representing a symbol table.

    `add` and `lookup` methods are given, however you still need to find a way to 
    deal with scopes.

    ## Attributes
    - :attr data: the content of the SymbolTable
    """

    def __init__(self) -> None:
        """ Initializes the SymbolTable. """
        self.__data = dict()

    @property
    def data(self) -> Dict[str, Any]:
        """ Returns a copy of the SymbolTable.
        """
        return deepcopy(self.__data)

    def add(self, name: str, value: Any) -> None:
        """ Adds to the SymbolTable.

        ## Parameters
        - :param name: the identifier on the SymbolTable
        - :param value: the value to assign to the given `name`
        """
        self.__data[name] = value

    def lookup(self, name: str) -> Union[Any, None]:
        """ Searches `name` on the SymbolTable and returns the value
        assigned to it.

        ## Parameters
        - :param name: the identifier that will be searched on the SymbolTable

        ## Return
        - :return: the value assigned to `name` on the SymbolTable. If `name` is not found, `None` is returned.
        """
        return self.__data.get(name)


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
        self.typemap = {
            "int": IntType,
            "char": CharType,
            # TODO
        }
        # TODO: Complete...

    def _assert_semantic(self, condition: bool, msg_code: int, coord, name: str = "", ltype="", rtype=""):
        """Check condition, if false print selected error message and exit"""
        error_msgs = {
            1: f"{name} is not defined",
            2: f"subscript must be of type(int), not {ltype}",
            3: "Expression must be of type(bool)",
            4: f"Cannot assign {rtype} to {ltype}",
            5: f"Binary operator {name} does not have matching LHS/RHS types",
            6: f"Binary operator {name} is not supported by {ltype}",
            7: "Break statement must be inside a loop",
            8: "Array dimension mismatch",
            9: f"Size mismatch on {name} initialization",
            10: f"{name} initialization type mismatch",
            11: f"{name} initialization must be a single element",
            12: "Lists have different sizes",
            13: "List & variable have different sizes",
            14: f"conditional expression is {ltype}, not type(bool)",
            15: f"{name} is not a function",
            16: f"no. arguments to call {name} function mismatch",
            17: f"Type mismatch with parameter {name}",
            18: "The condition expression must be of type(bool)",
            19: "Expression must be a constant",
            20: "Expression is not of basic type",
            21: f"{name} does not reference a variable of basic type",
            22: f"{name} is not a variable",
            23: f"Return of {ltype} is incompatible with {rtype} function definition",
            24: f"Name {name} is already defined in this scope",
            25: f"Unary operator {name} is not supported",
        }
        if not condition:
            msg = error_msgs[msg_code]  # invalid msg_code raises Exception
            print("SemanticError: %s %s" % (msg, coord), file=sys.stdout)
            sys.exit(1)

    def visit_Program(self, node):
        # Visit all of the global declarations
        for _decl in node.gdecls:
            self.visit(_decl)
        # TODO: Manage the symbol table

    def visit_BinaryOp(self, node):
        # Visit the left and right expression
        self.visit(node.left)
        ltype = node.left.uc_type
        self.visit(node.right)
        rtype = node.right.uc_type
        # TODO:
        # - Make sure left and right operands have the same type
        # - Make sure the operation is supported
        # - Assign the result type

    def visit_Assignment(self, node):
        # visit right side
        self.visit(node.rvalue)
        rtype = node.rvalue.uc_type
        # visit left side (must be a location)
        _var = node.lvalue
        self.visit(_var)
        if isinstance(_var, ID):
            self._assert_semantic(_var.scope is not None,
                                  1, node.coord, name=_var.name)
        ltype = node.lvalue.uc_type
        # Check that assignment is allowed
        self._assert_semantic(ltype == rtype, 4, node.coord,
                              ltype=ltype, rtype=rtype)
        # Check that assign_ops is supported by the type
        self._assert_semantic(
            node.op in ltype.assign_ops, 5, node.coord, name=node.op, ltype=ltype
        )


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
