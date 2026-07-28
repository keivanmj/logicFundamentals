# fromula equivalence checker
import sys
from typing import Dict, List, Tuple

sys.setrecursionlimit(10_000)


class FormulaParser:

    def __init__(
        self,
        text: str,
        variable_masks: Dict[str, int],
        full_mask: int,
    ):
        self.text = text
        self.variable_masks = variable_masks
        self.full_mask = full_mask
        self.position = 0

    def parse(self) -> int:
        result = self.parse_formula()

        if self.position != len(self.text):
            raise ValueError(
                f"Unexpected input at position {self.position}: "
                f"{self.text[self.position:]}"
            )

        return result

    def parse_formula(self) -> int:
        if self.position >= len(self.text):
            raise ValueError("Unexpected end of formula")

        current = self.text[self.position]


        if "a" <= current <= "z":
            self.position += 1
            return self.variable_masks[current]

        if current == "T":
            self.position += 1
            return self.full_mask

        if current == "F":
            self.position += 1
            return 0

        if current == "!":
            self.position += 1

            child = self.parse_formula()

            return self.full_mask ^ child

        if current == "(":
            self.position += 1

            left = self.parse_formula()

            operator = self.parse_operator()

            right = self.parse_formula()

            if (
                self.position >= len(self.text)
                or self.text[self.position] != ")"
            ):
                raise ValueError(
                    f"Expected ')' at position {self.position}"
                )

            self.position += 1

            return self.apply_operator(
                operator=operator,
                left=left,
                right=right,
            )

        raise ValueError(
            f"Unexpected character {current!r} "
            f"at position {self.position}"
        )

    def parse_operator(self) -> str:
        # عملگر بلندتر باید زودتر بررسی شود.
        if self.text.startswith("<->", self.position):
            self.position += 3
            return "<->"

        if self.text.startswith("->", self.position):
            self.position += 2
            return "->"

        if (
            self.position < len(self.text)
            and self.text[self.position] == "&"
        ):
            self.position += 1
            return "&"

        if (
            self.position < len(self.text)
            and self.text[self.position] == "|"
        ):
            self.position += 1
            return "|"

        raise ValueError(
            f"Expected operator at position {self.position}"
        )

    def apply_operator(
        self,
        operator: str,
        left: int,
        right: int,
    ) -> int:
        if operator == "&":
            return left & right

        if operator == "|":
            return left | right

        # A -> B === !A | B
        if operator == "->":
            return (self.full_mask ^ left) | right

        # A <-> B
        if operator == "<->":
            return self.full_mask ^ (left ^ right)

        raise ValueError(f"Unknown operator: {operator}")


def collect_variables(formulas: List[str]) -> List[str]:

    variables = set()

    for formula in formulas:
        for character in formula:
            if "a" <= character <= "z":
                variables.add(character)

    return sorted(variables)


def build_variable_masks(
    variables: List[str],
) -> Tuple[Dict[str, int], int]:

    variable_count = len(variables)

    valuation_count = 1 << variable_count

    full_mask = (1 << valuation_count) - 1

    variable_masks: Dict[str, int] = {}

    for position, variable in enumerate(variables):
        block_size = 1 << (
            variable_count - position - 1
        )

        ones_block = (1 << block_size) - 1

        variable_mask = 0

        for start in range(
            block_size,
            valuation_count,
            2 * block_size,
        ):
            variable_mask |= ones_block << start

        variable_masks[variable] = variable_mask

    return variable_masks, full_mask


def evaluate_formula(
    formula: str,
    variable_masks: Dict[str, int],
    full_mask: int,
) -> int:
    parser = FormulaParser(
        text=formula,
        variable_masks=variable_masks,
        full_mask=full_mask,
    )

    return parser.parse()


def find_first_set_bit(value: int) -> int:
  
    lowest_set_bit = value & -value

    return lowest_set_bit.bit_length() - 1


def format_valuation(
    valuation_index: int,
    variables: List[str],
) -> str:

    variable_count = len(variables)

    assignments = []

    for position, variable in enumerate(variables):
        shift = variable_count - position - 1

        value = (
            valuation_index >> shift
        ) & 1

        text_value = "True" if value else "False"

        assignments.append(
            f"{variable}={text_value}"
        )

    return " ".join(assignments)


def solve(input_data: str) -> str:
    lines = [
        line.strip()
        for line in input_data.splitlines()
        if line.strip() != ""
    ]

    if len(lines) != 2:
        raise ValueError(
            "Input must contain exactly two formulas"
        )

    first_formula = lines[0]
    second_formula = lines[1]

    variables = collect_variables(
        [first_formula, second_formula]
    )

    variable_masks, full_mask = build_variable_masks(
        variables
    )

    first_result = evaluate_formula(
        formula=first_formula,
        variable_masks=variable_masks,
        full_mask=full_mask,
    )

    second_result = evaluate_formula(
        formula=second_formula,
        variable_masks=variable_masks,
        full_mask=full_mask,
    )

    difference_mask = first_result ^ second_result

    if difference_mask == 0:
        return "Equivalent"

    first_counterexample = find_first_set_bit(
        difference_mask
    )

    valuation_text = format_valuation(
        valuation_index=first_counterexample,
        variables=variables,
    )

    return (
        "Not Equivalent\n"
        + valuation_text
    )

def main() -> None:
    first_formula = input().strip()
    second_formula = input().strip()

    input_data = "\n".join(
        [
            first_formula,
            second_formula,
        ]
    )

    print(solve(input_data))


if __name__ == "__main__":
    main()
