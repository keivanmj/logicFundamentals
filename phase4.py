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
        # عملگر بلندتر باید اول بررسی شود.

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

        # A -> B  ===  !A | B
        if operator == "->":
            return (self.full_mask ^ left) | right

        # A <-> B
        # وقتی درست است که دو طرف مقدار مساوی داشته باشند.
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

    # تعداد تمام valuationهای ممکن
    valuation_count = 1 << variable_count

    # تمام بیت‌ها برابر 1 هستند.
    full_mask = (1 << valuation_count) - 1

    variable_masks: Dict[str, int] = {}

    for position, variable in enumerate(variables):
        block_size = 1 << (
            variable_count - position - 1
        )

        ones_block = (1 << block_size) - 1

        variable_mask = 0

        # برای هر متغیر، بلوک‌های False و True ساخته می‌شوند.
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


def calculate_conjunction(
    premise_masks: List[int],
    active: List[bool],
    full_mask: int,
) -> int:

    result = full_mask

    for index, premise_mask in enumerate(premise_masks):
        if active[index]:
            result &= premise_mask

            # دیگر لازم نیست ادامه دهیم.
            if result == 0:
                break

    return result


def entails(
    premise_conjunction: int,
    conclusion_mask: int,
    full_mask: int,
) -> bool:

    false_conclusion_mask = (
        full_mask ^ conclusion_mask
    )

    counterexamples = (
        premise_conjunction
        & false_conclusion_mask
    )

    return counterexamples == 0


def find_minimal_entailing_subset(
    premise_masks: List[int],
    conclusion_mask: int,
    full_mask: int,
) -> List[int]:


    premise_count = len(premise_masks)

    active = [True] * premise_count

    for index in range(premise_count):
        # موقتاً مقدمه را حذف می‌کنیم.
        active[index] = False

        candidate_conjunction = calculate_conjunction(
            premise_masks=premise_masks,
            active=active,
            full_mask=full_mask,
        )

        # اگر بدون این مقدمه نیز استنتاج برقرار باشد،
        # حذف آن دائمی می‌شود.
        if entails(
            premise_conjunction=candidate_conjunction,
            conclusion_mask=conclusion_mask,
            full_mask=full_mask,
        ):
            continue

        # در غیر این صورت مقدمه لازم است.
        active[index] = True

    return [
        index + 1
        for index, is_active in enumerate(active)
        if is_active
    ]


def find_minimal_unsatisfiable_subset(
    premise_masks: List[int],
    full_mask: int,
) -> List[int]:


    premise_count = len(premise_masks)

    active = [True] * premise_count

    for index in range(premise_count):
        # موقتاً مقدمه را حذف می‌کنیم.
        active[index] = False

        candidate_conjunction = calculate_conjunction(
            premise_masks=premise_masks,
            active=active,
            full_mask=full_mask,
        )

        if candidate_conjunction == 0:
            continue

        active[index] = True

    return [
        index + 1
        for index, is_active in enumerate(active)
        if is_active
    ]


def solve(input_data: str) -> str:
    lines = [
        line.strip()
        for line in input_data.splitlines()
        if line.strip() != ""
    ]

    if not lines:
        raise ValueError("Input is empty")

    premise_count = int(lines[0])

    expected_line_count = premise_count + 2

    if len(lines) != expected_line_count:
        raise ValueError(
            f"Expected {expected_line_count} input lines, "
            f"but received {len(lines)}"
        )

    premises = lines[1:1 + premise_count]

    conclusion = lines[1 + premise_count]

    all_formulas = premises + [conclusion]

    variables = collect_variables(all_formulas)

    variable_masks, full_mask = build_variable_masks(
        variables
    )

    premise_masks = [
        evaluate_formula(
            formula=premise,
            variable_masks=variable_masks,
            full_mask=full_mask,
        )
        for premise in premises
    ]

    conclusion_mask = evaluate_formula(
        formula=conclusion,
        variable_masks=variable_masks,
        full_mask=full_mask,
    )

    all_active = [True] * premise_count

    full_premise_conjunction = calculate_conjunction(
        premise_masks=premise_masks,
        active=all_active,
        full_mask=full_mask,
    )

    if full_premise_conjunction == 0:
        minimal_indices = (
            find_minimal_unsatisfiable_subset(
                premise_masks=premise_masks,
                full_mask=full_mask,
            )
        )

        indices_text = " ".join(
            str(index)
            for index in minimal_indices
        )

        return (
            "Inconsistent\n"
            + indices_text
        )


    minimal_indices = find_minimal_entailing_subset(
        premise_masks=premise_masks,
        conclusion_mask=conclusion_mask,
        full_mask=full_mask,
    )

    indices_text = " ".join(
        str(index)
        for index in minimal_indices
    )

    return (
        "Minimal Subset\n"
        + indices_text
    )


# Sample input 1

#
# 3
# p
# (p|q)
# q
# (p&q)
#
# Expected output:
#
# Minimal Subset
# 1 3



# Sample input 2
#
# 2
# p
# !p
# q
#
# Expected output:
#
# Inconsistent
# 1 2



# Extra sample 3

#
# 3
# p
# (p->q)
# q
# q
#
# Expected output:
#
# Minimal Subset
# 3


# 4
# p
# !p
# q
# !q
# r
#
# Expected output:
#
# Inconsistent
# 3 4


def main() -> None:
    input_data = sys.stdin.read()

    result = solve(input_data)

    print(result)


if __name__ == "__main__":
    main()