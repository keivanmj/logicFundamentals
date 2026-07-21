import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Set, Tuple


sys.setrecursionlimit(10_000)

# Formula AST

@dataclass(frozen=True)
class Formula:
    kind: str
    value: Optional[str] = None
    left: Optional["Formula"] = None
    right: Optional["Formula"] = None


def make_variable(name: str) -> Formula:
    return Formula(kind="var", value=name)


def make_constant(value: str) -> Formula:
    return Formula(kind="const", value=value)


def make_not(child: Formula) -> Formula:
    return Formula(kind="not", left=child)


def make_binary(
    kind: str,
    left: Formula,
    right: Formula,
) -> Formula:
    return Formula(
        kind=kind,
        left=left,
        right=right,
    )

# Parser

class FormulaParser:
    def __init__(self, text: str):
        self.text = text
        self.position = 0

    def parse(self) -> Formula:
        result = self.parse_formula()

        if self.position != len(self.text):
            raise ValueError(
                f"Unexpected input at position {self.position}: "
                f"{self.text[self.position:]}"
            )

        return result

    def parse_formula(self) -> Formula:
        if self.position >= len(self.text):
            raise ValueError("Unexpected end of formula")

        current = self.text[self.position]

        # Variable
        if "a" <= current <= "z":
            self.position += 1
            return make_variable(current)

        # Constants
        if current in ("T", "F"):
            self.position += 1
            return make_constant(current)

        # Negation
        if current == "!":
            self.position += 1

            child = self.parse_formula()

            return make_not(child)

        # Binary formula
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

            return make_binary(
                kind=operator,
                left=left,
                right=right,
            )

        raise ValueError(
            f"Unexpected character {current!r} "
            f"at position {self.position}"
        )

    def parse_operator(self) -> str:
        # Longer operators must be checked first.

        if self.text.startswith("<->", self.position):
            self.position += 3
            return "iff"

        if self.text.startswith("->", self.position):
            self.position += 2
            return "imp"

        if (
            self.position < len(self.text)
            and self.text[self.position] == "&"
        ):
            self.position += 1
            return "and"

        if (
            self.position < len(self.text)
            and self.text[self.position] == "|"
        ):
            self.position += 1
            return "or"

        raise ValueError(
            f"Expected operator at position {self.position}"
        )

# Formula rendering

def render_formula(formula: Formula) -> str:
    if formula.kind in ("var", "const"):
        return formula.value

    if formula.kind == "not":
        return "!" + render_formula(formula.left)

    operators = {
        "and": "&",
        "or": "|",
        "imp": "->",
        "iff": "<->",
    }

    operator = operators[formula.kind]

    return (
        "("
        + render_formula(formula.left)
        + operator
        + render_formula(formula.right)
        + ")"
    )

# Proof Step

@dataclass
class ProofStep:
    formula: Formula
    rule: str
    references: Tuple[int, ...] = ()


# Proof Search

class ProofSearch:
    def __init__(
        self,
        premises: List[Formula],
        goal: Formula,
    ):
        self.premises = premises
        self.goal = goal

        self.steps: List[ProofStep] = []

        # Formula -> number of its first proof step
        self.known: Dict[Formula, int] = {}

        # The first n steps must be the premises.
        for premise in premises:
            self.steps.append(
                ProofStep(
                    formula=premise,
                    rule="Premise",
                )
            )

            self.known.setdefault(
                premise,
                len(self.steps),
            )

        # Relevant formulas restrict introduction rules and
        # prevent infinite loops, especially for !!.
        self.relevant: Set[Formula] = set()

        for formula in premises:
            self.collect_subformulas(
                formula,
                self.relevant,
            )

        self.collect_subformulas(
            goal,
            self.relevant,
        )

        # <->E can create these two implications.
        biconditionals = [
            formula
            for formula in self.relevant
            if formula.kind == "iff"
        ]

        for formula in biconditionals:
            self.relevant.add(
                make_binary(
                    "imp",
                    formula.left,
                    formula.right,
                )
            )

            self.relevant.add(
                make_binary(
                    "imp",
                    formula.right,
                    formula.left,
                )
            )

        # Subformulas of the final goal receive greater priority.
        self.goal_subformulas: Set[Formula] = set()

        self.collect_subformulas(
            goal,
            self.goal_subformulas,
        )

        self.introduction_candidates = sorted(
            [
                formula
                for formula in self.relevant
                if (
                    formula.kind in ("and", "or")
                    or self.is_double_negation(formula)
                )
            ],
            key=self.candidate_priority,
        )

    # Formula helpers

    def collect_subformulas(
        self,
        formula: Formula,
        destination: Set[Formula],
    ) -> None:
        if formula in destination:
            return

        destination.add(formula)

        if formula.left is not None:
            self.collect_subformulas(
                formula.left,
                destination,
            )

        if formula.right is not None:
            self.collect_subformulas(
                formula.right,
                destination,
            )

    def formula_size(self, formula: Formula) -> int:
        result = 1

        if formula.left is not None:
            result += self.formula_size(formula.left)

        if formula.right is not None:
            result += self.formula_size(formula.right)

        return result

    def candidate_priority(
        self,
        formula: Formula,
    ) -> Tuple[int, int, str]:
        # Goal subformulas first.
        goal_priority = (
            0
            if formula in self.goal_subformulas
            else 1
        )

        return (
            goal_priority,
            self.formula_size(formula),
            render_formula(formula),
        )

    @staticmethod
    def is_double_negation(
        formula: Formula,
    ) -> bool:
        return (
            formula.kind == "not"
            and formula.left is not None
            and formula.left.kind == "not"
        )


    # Proof-step helpers


    def add_step(
        self,
        formula: Formula,
        rule: str,
        references: Tuple[int, ...],
    ) -> bool:
        # Avoid generating the same formula repeatedly.
        if formula in self.known:
            return False

        self.steps.append(
            ProofStep(
                formula=formula,
                rule=rule,
                references=references,
            )
        )

        self.known[formula] = len(self.steps)

        return True


    # Main proof search


    def generate(self) -> List[ProofStep]:
        if self.goal in self.known:
            self.ensure_goal_is_last()
            return self.steps

        false_formula = make_constant("F")

        while self.goal not in self.known:
            changed = False


            # FE: From F derive any formula.


            if false_formula in self.known:
                self.add_step(
                    formula=self.goal,
                    rule="FE",
                    references=(
                        self.known[false_formula],
                    ),
                )

                break


            # Forward elimination rules

            known_snapshot = list(self.known.items())

            for formula, step_number in known_snapshot:

                # &E
                if formula.kind == "and":
                    changed |= self.add_step(
                        formula=formula.left,
                        rule="&E",
                        references=(step_number,),
                    )

                    if self.goal in self.known:
                        break

                    changed |= self.add_step(
                        formula=formula.right,
                        rule="&E",
                        references=(step_number,),
                    )

                # <->E
                elif formula.kind == "iff":
                    forward_implication = make_binary(
                        "imp",
                        formula.left,
                        formula.right,
                    )

                    backward_implication = make_binary(
                        "imp",
                        formula.right,
                        formula.left,
                    )

                    changed |= self.add_step(
                        formula=forward_implication,
                        rule="<->E",
                        references=(step_number,),
                    )

                    if self.goal in self.known:
                        break

                    changed |= self.add_step(
                        formula=backward_implication,
                        rule="<->E",
                        references=(step_number,),
                    )

                # Double-negation elimination
                elif self.is_double_negation(formula):
                    inner_formula = formula.left.left

                    changed |= self.add_step(
                        formula=inner_formula,
                        rule="!!",
                        references=(step_number,),
                    )

                if self.goal in self.known:
                    break

            if self.goal in self.known:
                break


            known_formulas = list(self.known.keys())

            for formula in known_formulas:
                negated_formula = make_not(formula)

                if negated_formula in self.known:
                    changed |= self.add_step(
                        formula=false_formula,
                        rule="!E",
                        references=(
                            self.known[formula],
                            self.known[negated_formula],
                        ),
                    )

                    break

            # F may have just been generated.
            if false_formula in self.known:
                self.add_step(
                    formula=self.goal,
                    rule="FE",
                    references=(
                        self.known[false_formula],
                    ),
                )

                break

            known_snapshot = list(self.known.items())

            for formula, implication_step in known_snapshot:
                if formula.kind != "imp":
                    continue

                antecedent = formula.left
                consequence = formula.right

                if antecedent not in self.known:
                    continue

                changed |= self.add_step(
                    formula=consequence,
                    rule="->E",
                    references=(
                        implication_step,
                        self.known[antecedent],
                    ),
                )

                if self.goal in self.known:
                    break

            if self.goal in self.known:
                break


            for formula in self.introduction_candidates:
                if formula in self.known:
                    continue

                # &I
                if formula.kind == "and":
                    if (
                        formula.left in self.known
                        and formula.right in self.known
                    ):
                        changed |= self.add_step(
                            formula=formula,
                            rule="&I",
                            references=(
                                self.known[formula.left],
                                self.known[formula.right],
                            ),
                        )

                # |I
                elif formula.kind == "or":
                    if formula.left in self.known:
                        changed |= self.add_step(
                            formula=formula,
                            rule="|I",
                            references=(
                                self.known[formula.left],
                            ),
                        )

                    elif formula.right in self.known:
                        changed |= self.add_step(
                            formula=formula,
                            rule="|I",
                            references=(
                                self.known[formula.right],
                            ),
                        )

                # Double-negation introduction
                elif self.is_double_negation(formula):
                    inner_formula = formula.left.left

                    if inner_formula in self.known:
                        changed |= self.add_step(
                            formula=formula,
                            rule="!!",
                            references=(
                                self.known[inner_formula],
                            ),
                        )

                if self.goal in self.known:
                    break

            if not changed:
                raise RuntimeError(
                    "No proof was found with the allowed rules."
                )

            if len(self.steps) > 1000:
                raise RuntimeError(
                    "Generated proof contains more than 1000 steps."
                )

        self.ensure_goal_is_last()

        if len(self.steps) > 1000:
            raise RuntimeError(
                "Generated proof contains more than 1000 steps."
            )

        return self.steps


    def ensure_goal_is_last(self) -> None:
        if (
            self.steps
            and self.steps[-1].formula == self.goal
        ):
            return

        false_formula = make_constant("F")

        # One-step reproduction through FE
        if false_formula in self.known:
            self.steps.append(
                ProofStep(
                    formula=self.goal,
                    rule="FE",
                    references=(
                        self.known[false_formula],
                    ),
                )
            )

            return

        # One-step reproduction through elimination rules
        for formula, step_number in self.known.items():

            if (
                formula.kind == "and"
                and (
                    formula.left == self.goal
                    or formula.right == self.goal
                )
            ):
                self.steps.append(
                    ProofStep(
                        formula=self.goal,
                        rule="&E",
                        references=(step_number,),
                    )
                )

                return

            if formula.kind == "iff":
                first_direction = make_binary(
                    "imp",
                    formula.left,
                    formula.right,
                )

                second_direction = make_binary(
                    "imp",
                    formula.right,
                    formula.left,
                )

                if self.goal in (
                    first_direction,
                    second_direction,
                ):
                    self.steps.append(
                        ProofStep(
                            formula=self.goal,
                            rule="<->E",
                            references=(step_number,),
                        )
                    )

                    return

            if (
                self.is_double_negation(formula)
                and formula.left.left == self.goal
            ):
                self.steps.append(
                    ProofStep(
                        formula=self.goal,
                        rule="!!",
                        references=(step_number,),
                    )
                )

                return

        # One-step reproduction through introduction rules

        if (
            self.goal.kind == "and"
            and self.goal.left in self.known
            and self.goal.right in self.known
        ):
            self.steps.append(
                ProofStep(
                    formula=self.goal,
                    rule="&I",
                    references=(
                        self.known[self.goal.left],
                        self.known[self.goal.right],
                    ),
                )
            )

            return

        if self.goal.kind == "or":
            if self.goal.left in self.known:
                self.steps.append(
                    ProofStep(
                        formula=self.goal,
                        rule="|I",
                        references=(
                            self.known[self.goal.left],
                        ),
                    )
                )

                return

            if self.goal.right in self.known:
                self.steps.append(
                    ProofStep(
                        formula=self.goal,
                        rule="|I",
                        references=(
                            self.known[self.goal.right],
                        ),
                    )
                )

                return

        if self.is_double_negation(self.goal):
            inner_formula = self.goal.left.left

            if inner_formula in self.known:
                self.steps.append(
                    ProofStep(
                        formula=self.goal,
                        rule="!!",
                        references=(
                            self.known[inner_formula],
                        ),
                    )
                )

                return

        # One-step reproduction through Modus Ponens

        for formula, implication_step in self.known.items():
            if (
                formula.kind == "imp"
                and formula.right == self.goal
                and formula.left in self.known
            ):
                self.steps.append(
                    ProofStep(
                        formula=self.goal,
                        rule="->E",
                        references=(
                            implication_step,
                            self.known[formula.left],
                        ),
                    )
                )

                return


        original_goal_step = self.known[self.goal]

        double_negated_goal = make_not(
            make_not(self.goal)
        )

        self.steps.append(
            ProofStep(
                formula=double_negated_goal,
                rule="!!",
                references=(original_goal_step,),
            )
        )

        double_negation_step = len(self.steps)

        self.steps.append(
            ProofStep(
                formula=self.goal,
                rule="!!",
                references=(double_negation_step,),
            )
        )



def format_proof(steps: List[ProofStep]) -> str:
    output = [str(len(steps))]

    for number, step in enumerate(steps, start=1):
        formula_text = render_formula(step.formula)

        if step.references:
            references_text = ",".join(
                str(reference)
                for reference in step.references
            )

            output.append(
                f"{number}. {formula_text} "
                f"[{step.rule}: {references_text}]"
            )
        else:
            output.append(
                f"{number}. {formula_text} "
                f"[{step.rule}]"
            )

    return "\n".join(output)



def solve(
    premise_texts: List[str],
    goal_text: str,
) -> str:
    premises = [
        FormulaParser(text).parse()
        for text in premise_texts
    ]

    goal = FormulaParser(goal_text).parse()

    proof_search = ProofSearch(
        premises=premises,
        goal=goal,
    )

    steps = proof_search.generate()

    return format_proof(steps)



#
# 2
# (p->q)
# p
# q
#
# Expected output:
#
# 3
# 1. (p->q) [Premise]
# 2. p [Premise]
# 3. q [->E: 1,2]


#
# 1
# (p&q)
# p
#
# Expected output:
#
# 2
# 1. (p&q) [Premise]
# 2. p [&E: 1]



#
# 2
# p
# !p
# q
#
# Expected output:
#
# 4
# 1. p [Premise]
# 2. !p [Premise]
# 3. F [!E: 1,2]
# 4. q [FE: 3]



#
# 2
# p
# q
# (p&q)
#
# Expected output:
#
# 3
# 1. p [Premise]
# 2. q [Premise]
# 3. (p&q) [&I: 1,2]



#
# 1
# p
# (p|q)
#
# Expected output:
#
# 2
# 1. p [Premise]
# 2. (p|q) [|I: 1]


#
# 2
# (p<->q)
# p
# q
#
# One valid output:
#
# 5
# 1. (p<->q) [Premise]
# 2. p [Premise]
# 3. (p->q) [<->E: 1]
# 4. (q->p) [<->E: 1]
# 5. q [->E: 3,2]


def main() -> None:
    # First line: number of premises
    premise_count = int(input().strip())

    # Next n lines: premises
    premise_texts = [
        input().strip()
        for _ in range(premise_count)
    ]

    # Last line: conclusion
    goal_text = input().strip()

    print(
        solve(
            premise_texts=premise_texts,
            goal_text=goal_text,
        )
    )


if __name__ == "__main__":
    main()