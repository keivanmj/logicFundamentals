# counter example generator
import sys
from typing import Dict, List, Tuple


sys.setrecursionlimit(10_000)

class FormulaParser:
    
    # Parses the formula and evaluates it for all valuations,
    # storing the results as an integer bitset.

    # Each bit represents the result of the formula for one valuation.

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

            # Negate all valuation bits.
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

        # A <-> B is true exactly when A and B are equal.
        if operator == "<->":
            return self.full_mask ^ (left ^ right)

        raise ValueError(f"Unknown operator: {operator}")


def collect_variables(formulas: List[str]) -> List[str]:

    # returns all the appeared variables alphabetically
    
    variables = set()

    for formula in formulas:
        for character in formula:
            if "a" <= character <= "z":
                variables.add(character)

    return sorted(variables)


def build_variable_masks(
    variables: List[str],
) -> Tuple[Dict[str, int], int]:
    
    # Creates a bitmask for each variable.

    # The order of valuations:
    #     False before True

    # Example for p and q:
    #     p=False q=False
    #     p=False q=True
    #     p=True  q=False
    #     p=True  q=True
    # p = 1100, q = 1010
    variable_count = len(variables)

    valuation_count = 1 << variable_count

    full_mask = (1 << valuation_count) - 1

    variable_masks: Dict[str, int] = {}

    for index, variable in enumerate(variables):

        block_size = 1 << (variable_count - index - 1)

        pattern = (
            ("1" * block_size)
            + ("0" * block_size)
        )

        repetitions = valuation_count // (2 * block_size)

        bit_string = pattern * repetitions

        variable_masks[variable] = int(bit_string, 2)

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

    # prints valuation alphabetically
    
    variable_count = len(variables)
    result = []

    for index, variable in enumerate(variables):
        shift = variable_count - index - 1

        value = (
            valuation_index >> shift
        ) & 1

        text_value = "True" if value else "False"

        result.append(
            f"{variable}={text_value}"
        )

    return " ".join(result)


def solve(data: str) -> str:
    lines = [
        line.strip()
        for line in data.splitlines()
    ]

    while lines and lines[-1] == "":
        lines.pop()

    if not lines:
        raise ValueError("Input is empty")

    premise_count = int(lines[0])

    if premise_count == 0:
        premises: List[str] = []
        conclusion = lines[1]
    else:
        premises = lines[1:1 + premise_count]
        conclusion = lines[1 + premise_count]

    all_formulas = premises + [conclusion]

    variables = collect_variables(all_formulas)

    variable_masks, full_mask = build_variable_masks(
        variables
    )

    conclusion_result = evaluate_formula(
        formula=conclusion,
        variable_masks=variable_masks,
        full_mask=full_mask,
    )

    if premise_count == 0:
        if conclusion_result == full_mask:
            return "Valid"

        if conclusion_result == 0:
            return "Unsatisfiable"

        return "Satisfiable"


    premises_result = full_mask

    for premise in premises:
        premise_result = evaluate_formula(
            formula=premise,
            variable_masks=variable_masks,
            full_mask=full_mask,
        )

        premises_result &= premise_result

        if premises_result == 0:
            return "Valid"

    counterexample_mask = (
        premises_result
        & (full_mask ^ conclusion_result)
    )

    if counterexample_mask == 0:
        return "Valid"

    first_counterexample = find_first_set_bit(
        counterexample_mask
    )

    valuation_text = format_valuation(
        valuation_index=first_counterexample,
        variables=variables,
    )

    return f"Invalid\n{valuation_text}"


def main() -> None:
    premise_count = int(input().strip())

    premises = [
        input().strip()
        for _ in range(premise_count)
    ]

    conclusion = input().strip()

    input_data = "\n".join(
        [
            str(premise_count),
            *premises,
            conclusion,
        ]
    )

    print(solve(input_data))


if __name__ == "__main__":
    main()
