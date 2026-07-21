import sys
from dataclasses import dataclass
from typing import Optional, List


sys.setrecursionlimit(10_000)


@dataclass(frozen=True)
class Node:
    kind: str
    value: Optional[str] = None
    left: Optional["Node"] = None
    right: Optional["Node"] = None


def make_var(name: str) -> Node:
    return Node("var", value=name)


def make_const(value: str) -> Node:
    return Node("const", value=value)


def make_not(child: Node) -> Node:
    return Node("not", left=child)


def make_binary(kind: str, left: Node, right: Node) -> Node:
    return Node(kind, left=left, right=right)


class Parser:
    def __init__(self, text: str):
        self.text = text
        self.pos = 0

    def parse(self) -> Node:
        result = self.parse_formula()

        if self.pos != len(self.text):
            raise ValueError(
                f"Unexpected input at position {self.pos}"
            )

        return result

    def parse_formula(self) -> Node:
        if self.pos >= len(self.text):
            raise ValueError("Unexpected end of input")

        ch = self.text[self.pos]

        # Variable
        if "a" <= ch <= "z":
            self.pos += 1
            return make_var(ch)

        # Constant
        if ch in ("T", "F"):
            self.pos += 1
            return make_const(ch)

        # Negation
        if ch == "!":
            self.pos += 1
            return make_not(self.parse_formula())

        # Binary formula
        if ch == "(":
            self.pos += 1

            left = self.parse_formula()

            # Check the longest operators first.
            if self.text.startswith("<->", self.pos):
                operator = "iff"
                self.pos += 3

            elif self.text.startswith("->", self.pos):
                operator = "imp"
                self.pos += 2

            elif (
                self.pos < len(self.text)
                and self.text[self.pos] in ("&", "|")
            ):
                if self.text[self.pos] == "&":
                    operator = "and"
                else:
                    operator = "or"

                self.pos += 1

            else:
                raise ValueError(
                    f"Expected an operator at position {self.pos}"
                )

            right = self.parse_formula()

            if (
                self.pos >= len(self.text)
                or self.text[self.pos] != ")"
            ):
                raise ValueError(
                    f"Expected ')' at position {self.pos}"
                )

            self.pos += 1

            return make_binary(operator, left, right)

        raise ValueError(
            f"Unexpected character {ch!r} at position {self.pos}"
        )


def eliminate_implications(node: Node) -> Node:
    if node.kind in ("var", "const"):
        return node

    if node.kind == "not":
        return make_not(
            eliminate_implications(node.left)
        )

    left = eliminate_implications(node.left)
    right = eliminate_implications(node.right)

    if node.kind == "and":
        return make_binary("and", left, right)

    if node.kind == "or":
        return make_binary("or", left, right)

    # A -> B  ===  !A | B
    if node.kind == "imp":
        return make_binary(
            "or",
            make_not(left),
            right,
        )

    if node.kind == "iff":
        first_direction = make_binary(
            "or",
            make_not(left),
            right,
        )

        second_direction = make_binary(
            "or",
            make_not(right),
            left,
        )

        return make_binary(
            "and",
            first_direction,
            second_direction,
        )

    raise ValueError(f"Unknown node kind: {node.kind}")


def to_nnf(node: Node, is_negated: bool = False) -> Node:
    # Variable
    if node.kind == "var":
        if is_negated:
            return make_not(node)

        return node

    # Constant
    if node.kind == "const":
        if not is_negated:
            return node

        if node.value == "T":
            return make_const("F")

        return make_const("T")

    # Double negation
    if node.kind == "not":
        return to_nnf(
            node.left,
            not is_negated,
        )

    # De Morgan for AND
    if node.kind == "and":
        if is_negated:
            new_kind = "or"
        else:
            new_kind = "and"

        return make_binary(
            new_kind,
            to_nnf(node.left, is_negated),
            to_nnf(node.right, is_negated),
        )

    # De Morgan for OR
    if node.kind == "or":
        if is_negated:
            new_kind = "and"
        else:
            new_kind = "or"

        return make_binary(
            new_kind,
            to_nnf(node.left, is_negated),
            to_nnf(node.right, is_negated),
        )

    raise ValueError(
        "Implications must be eliminated before converting to NNF"
    )


def deduplicate_nodes(nodes: List[Node]) -> List[Node]:
    result = []
    seen = set()

    for node in nodes:
        if node not in seen:
            seen.add(node)
            result.append(node)

    return result


def deduplicate_groups(
    groups: List[List[Node]]
) -> List[List[Node]]:
    result = []
    seen = set()

    for group in groups:
        # Remove repeated literals inside the clause/term.
        group = deduplicate_nodes(group)

        key = tuple(group)

        # Remove exactly repeated clauses/terms.
        if key not in seen:
            seen.add(key)
            result.append(group)

    return result



def make_cnf(node: Node) -> List[List[Node]]:
    # Atomic CNF: one clause containing one literal.
    if node.kind in ("var", "const", "not"):
        return [[node]]

    if node.kind == "and":
        left_cnf = make_cnf(node.left)
        right_cnf = make_cnf(node.right)

        return deduplicate_groups(
            left_cnf + right_cnf
        )

    # CNF(A | B): Cartesian product of clauses.
    if node.kind == "or":
        left_cnf = make_cnf(node.left)
        right_cnf = make_cnf(node.right)

        product = []

        # Left-to-right order is preserved.
        for left_clause in left_cnf:
            for right_clause in right_cnf:
                merged_clause = (
                    left_clause + right_clause
                )

                merged_clause = deduplicate_nodes(
                    merged_clause
                )

                product.append(merged_clause)

        return deduplicate_groups(product)

    raise ValueError(
        f"Unexpected node in CNF conversion: {node.kind}"
    )


def make_dnf(node: Node) -> List[List[Node]]:
    # Atomic DNF: one term containing one literal.
    if node.kind in ("var", "const", "not"):
        return [[node]]

    # DNF(A | B): concatenate terms.
    if node.kind == "or":
        left_dnf = make_dnf(node.left)
        right_dnf = make_dnf(node.right)

        return deduplicate_groups(
            left_dnf + right_dnf
        )

    # DNF(A & B): Cartesian product of terms.
    if node.kind == "and":
        left_dnf = make_dnf(node.left)
        right_dnf = make_dnf(node.right)

        product = []

        # Left-to-right order is preserved.
        for left_term in left_dnf:
            for right_term in right_dnf:
                merged_term = (
                    left_term + right_term
                )

                merged_term = deduplicate_nodes(
                    merged_term
                )

                product.append(merged_term)

        return deduplicate_groups(product)

    raise ValueError(
        f"Unexpected node in DNF conversion: {node.kind}"
    )

def is_negation_pair(left: Node, right: Node) -> bool:
    # left == !right
    if (
        left.kind == "not"
        and left.left == right
    ):
        return True

    # right == !left
    if (
        right.kind == "not"
        and right.left == left
    ):
        return True

    return False


def simplify_once(node: Node) -> Node:
    if node.kind in ("var", "const"):
        return node

    if node.kind == "not":
        child = simplify_once(node.left)

        # !T => F
        # !F => T
        if child.kind == "const":
            if child.value == "T":
                return make_const("F")

            return make_const("T")

        # !!A => A
        if child.kind == "not":
            return child.left

        return make_not(child)

    left = simplify_once(node.left)
    right = simplify_once(node.right)

    if node.kind == "and":
        # A & F => F
        # F & A => F
        if (
            left.kind == "const"
            and left.value == "F"
        ):
            return make_const("F")

        if (
            right.kind == "const"
            and right.value == "F"
        ):
            return make_const("F")

        # T & A => A
        if (
            left.kind == "const"
            and left.value == "T"
        ):
            return right

        # A & T => A
        if (
            right.kind == "const"
            and right.value == "T"
        ):
            return left

        # A & A => A
        if left == right:
            return left

        # A & !A => F
        if is_negation_pair(left, right):
            return make_const("F")

        return make_binary(
            "and",
            left,
            right,
        )
        
    if node.kind == "or":
        # A | T => T
        # T | A => T
        if (
            left.kind == "const"
            and left.value == "T"
        ):
            return make_const("T")

        if (
            right.kind == "const"
            and right.value == "T"
        ):
            return make_const("T")

        # F | A => A
        if (
            left.kind == "const"
            and left.value == "F"
        ):
            return right

        # A | F => A
        if (
            right.kind == "const"
            and right.value == "F"
        ):
            return left

        # A | A => A
        if left == right:
            return left

        # A | !A => T
        if is_negation_pair(left, right):
            return make_const("T")

        return make_binary(
            "or",
            left,
            right,
        )

    raise ValueError(
        f"Unexpected node in simplification: {node.kind}"
    )


def simplify_to_fixed_point(node: Node) -> Node:
    while True:
        new_node = simplify_once(node)

        if new_node == node:
            return new_node

        node = new_node


def fold_left_text(
    parts: List[str],
    operator: str,
) -> str:
    result = parts[0]

    for part in parts[1:]:
        result = f"({result}{operator}{part})"

    return result


def render_literal(node: Node) -> str:
    if node.kind in ("var", "const"):
        return node.value

    if node.kind == "not":
        return "!" + render_literal(node.left)

    raise ValueError(
        "CNF/DNF clauses must contain literals only"
    )


def render_cnf(cnf: List[List[Node]]) -> str:
    clauses = []

    for clause in cnf:
        literal_texts = [
            render_literal(literal)
            for literal in clause
        ]

        clause_text = fold_left_text(
            literal_texts,
            "|",
        )

        clauses.append(clause_text)

    return fold_left_text(
        clauses,
        "&",
    )


def render_dnf(dnf: List[List[Node]]) -> str:
    terms = []

    for term in dnf:
        literal_texts = [
            render_literal(literal)
            for literal in term
        ]

        term_text = fold_left_text(
            literal_texts,
            "&",
        )

        terms.append(term_text)

    return fold_left_text(
        terms,
        "|",
    )


def render_formula(node: Node) -> str:
    if node.kind in ("var", "const"):
        return node.value

    if node.kind == "not":
        return "!" + render_formula(node.left)

    # Consecutive identical AND/OR operators must be
    # printed in associative-left form.
    if node.kind in ("and", "or"):
        operands = []

        def collect(current: Node) -> None:
            if current.kind == node.kind:
                collect(current.left)
                collect(current.right)
            else:
                operands.append(current)

        collect(node)

        if node.kind == "and":
            operator = "&"
        else:
            operator = "|"

        operand_texts = [
            render_formula(operand)
            for operand in operands
        ]

        return fold_left_text(
            operand_texts,
            operator,
        )

    operator_text = {
        "imp": "->",
        "iff": "<->",
    }[node.kind]

    return (
        f"({render_formula(node.left)}"
        f"{operator_text}"
        f"{render_formula(node.right)})"
    )


def solve(text: str) -> tuple[str, str, str]:
    root = Parser(text).parse()

    without_implications = eliminate_implications(root)
    nnf = to_nnf(without_implications)

    cnf = make_cnf(nnf)
    dnf = make_dnf(nnf)

    simplified = simplify_to_fixed_point(nnf)

    return (
        render_cnf(cnf),
        render_dnf(dnf),
        render_formula(simplified),
    )


def main() -> None:
    formula = sys.stdin.readline().strip()

    cnf_text, dnf_text, simplified_text = solve(
        formula
    )

    print(cnf_text)
    print(dnf_text)
    print(simplified_text)


if __name__ == "__main__":
    # main()

    formula = "!(!p&!q)"
    # formula = "((p&T)|F)"
    # formula = "(p<->!p)"
    # formula = "(p->q)"
    # formula = "!(p|q)"
    # formula = "((p|q)&(!p|r))"
    # formula = "((a&b)|(c&d))"
    # formula = "((a|b)&(c|d))"
    # formula = "((p&!p)|q)"
    # formula = "((p|!p)&q)"
    # formula = "(((p&T)|F)&p)"
    # formula = "!((p->q)&(q->r))"

    cnf_text, dnf_text, simplified_text = solve(formula)

    print("Input:")
    print(formula)

    print("\nCNF:")
    print(cnf_text)

    print("\nDNF:")
    print(dnf_text)

    print("\nSimplified:")
    print(simplified_text)