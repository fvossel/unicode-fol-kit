import pathlib
from lark import Lark, UnexpectedCharacters, UnexpectedToken, UnexpectedEOF
from .nodes import Node, FOLTransformer
from .naming import NamingError, ParsingError


class FOLParser:
    def __init__(self):
        grammar_path = pathlib.Path(__file__).parent / "syntax.lark"
        with open(grammar_path, encoding="utf-8") as file:
            grammar = file.read()
        self.parser = Lark(grammar, parser='earley')

    def parse(self, text: str) -> Node:
        try:
            tree = self.parser.parse(text)
            return FOLTransformer().transform(tree)
        except UnexpectedCharacters as e:
            raise NamingError(self.parser, e, text)
        except (UnexpectedToken, UnexpectedEOF) as e:
            raise ParsingError(self.parser, e, text)
