import argparse
import pathlib
import sys
from ply.yacc import yacc
from uc.uc_ast import (
    ID,
    ArrayDecl,
    ArrayRef,
    Assert,
    Assignment,
    BinaryOp,
    Break,
    Compound,
    Constant,
    Decl,
    DeclList,
    EmptyStatement,
    ExprList,
    For,
    FuncCall,
    FuncDecl,
    FuncDef,
    GlobalDecl,
    If,
    InitList,
    ParamList,
    Print,
    Program,
    Read,
    Return,
    Type,
    UnaryOp,
    VarDecl,
    While,
)
from uc.uc_lexer import UCLexer


class Coord:
    """Coordinates of a syntactic element. Consists of:
    - Line number
    - (optional) column number, for the Lexer
    """

    __slots__ = ("line", "column")

    def __init__(self, line, column=None):
        self.line = line
        self.column = column

    def __str__(self):
        if self.line and self.column is not None:
            coord_str = "@ %s:%s" % (self.line, self.column)
        elif self.line:
            coord_str = "@ %s" % (self.line)
        else:
            coord_str = ""
        return coord_str


class UCParser:
    def __init__(self, debug=True):
        """Create a new uCParser."""
        self.uclex = UCLexer(self._lexer_error)
        self.uclex.build()
        self.tokens = self.uclex.tokens

        self.ucparser = yacc(module=self, start="program", debug=debug)
        # Keeps track of the last token given to yacc (the lookahead token)
        self._last_yielded_token = None

    def parse(self, text, debuglevel=0):
        self.uclex.reset_lineno()
        self._last_yielded_token = None
        return self.ucparser.parse(input=text, lexer=self.uclex, debug=debuglevel)

    def _lexer_error(self, msg, line, column):
        # use stdout to match with the output in the .out test files
        print("LexerError: %s at %d:%d" % (msg, line, column), file=sys.stdout)
        sys.exit(1)

    def _parser_error(self, msg, coord=None):
        # use stdout to match with the output in the .out test files
        if coord is None:
            print("ParserError: %s" % (msg), file=sys.stdout)
        else:
            print("ParserError: %s %s" % (msg, coord), file=sys.stdout)
        sys.exit(1)

    def _token_coord(self, p, token_idx):
        last_cr = p.lexer.lexer.lexdata.rfind("\n", 0, p.lexpos(token_idx))
        if last_cr < 0:
            last_cr = -1
        column = p.lexpos(token_idx) - (last_cr)
        return Coord(p.lineno(token_idx), column)

    def p_program(self, p):
        """ program  : global_declaration_list"""
        p[0] = Program(p[1])

    def p_global_declaration_list(self, p):
        """global_declaration_list : global_declaration
        | global_declaration_list global_declaration
        """
        p[0] = [p[1]] if len(p) == 2 else p[1] + [p[2]]

    def p_global_declaration_1(self, p):
        """global_declaration    : declaration"""
        p[0] = GlobalDecl(p[1])

    def p_global_declaration_2(self, p):
        """global_declaration    : function_definition"""
        p[0] = p[1]

    def p_expression(self, p):
        """expression  : assignment_expression
        | expression COMMA assignment_expression
        """
        # single expression
        if len(p) == 2:
            p[0] = p[1]
        else:
            if not isinstance(p[1], ExprList):
                p[1] = ExprList([p[1]])

            p[1].exprs.append(p[3])
            p[0] = p[1]

    def p_error(self, p):
        if p:
            self._parser_error(
                "Before %s" % p.value, Coord(p.lineno, self.uclex.find_tok_column(p))
            )
        else:
            self._parser_error("At the end of input (%s)" % self.uclex.filename)


if __name__ == "__main__":

    # create argument parser
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", help="Path to file to be parsed", type=str)
    args = parser.parse_args()

    # get input path
    input_file = args.input_file
    input_path = pathlib.Path(input_file)

    # check if file exists
    if not input_path.exists():
        print("ERROR: Input", input_path, "not found", file=sys.stderr)
        sys.exit(1)

    def print_error(msg, x, y):
        print("Lexical error: %s at %d:%d" % (msg, x, y), file=sys.stderr)

    # set error function
    p = UCParser()
    # open file and print ast
    with open(input_path) as f:
        ast = p.parse(f.read())
        ast.show(buf=sys.stdout, showcoord=True)
