import string
import itertools
from functools import reduce


class RPN:
    operators = {'>': 1, '&': 2, '|': 2, '/': 2, '^': 3, '~': 4}
    variables = string.ascii_lowercase + "TF"

    def is_operator(self, c):
        """
        :param c: string
        :return: True if sting is a operator
        """
        return c in self.operators

    def get_precedence(self, c):
        """
        :param c: operator
        :return: precedence of given operator
        """
        if self.is_operator(c):
            return self.operators[c]
        else:
            return 0

    def is_binary(self, c):
        """
        :param c: operator
        :return: True if binary operator or False if  unary operator
        """
        if c in ['>', '&', '|', '/', '^']:
            return True
        if c in ['~']:
            return False

    def convert_to_rpn(self, infix):
        """
        :param infix: logic expression in infix form
        :return: logic expression in reversed polish notation
        """
        infix = infix.replace(" ", "")
        if not self.validate_expression(infix):
            return "ERROR"
        postfix = []
        stack = []

        for i in infix:
            if self.is_operator(i):
                while (len(stack) != 0 and ((
                        self.is_binary(i) and (self.get_precedence(i) <= self.get_precedence(stack[-1])) or (
                        not self.is_binary(i) and (self.get_precedence(i) < self.get_precedence(stack[-1])))))):
                    postfix.append(stack.pop());
                stack.append(i)
            elif i == "(":
                stack.append(i)
            elif i == ")":
                while stack[-1] != "(":
                    postfix.append(stack.pop())
                stack.pop()
            else:
                postfix.append(i)

        while len(stack) != 0:
            postfix.append(stack.pop())

        return (postfix)

    def validate_expression(self, infix):
        """
        :param infix: logic expression in infix representation
        :return: True or False depending on expression being valid
        """
        state = True  # True - expecting bracket ( or variable, False - expecting bracket ) or operator
        par_count = 0  # bracket counter
        for char in infix:
            if char == " ":
                continue
            if state:
                if self.is_operator(char) and not self.is_binary(char):
                    continue
                elif char in self.variables:
                    state = False
                elif char == "(":
                    par_count += 1
                else:
                    return False
            else:
                if self.is_operator(char) and self.is_binary(char):
                    state = True
                elif char == ")":
                    par_count -= 1
                else:
                    return False
            if par_count < 0: return False
        return par_count == 0 and not state  # valid expression must end with state False and have closed all brackets

    def get_expression_variables(self, expr):
        return ''.join(sorted(set([char for char in expr if ord(char) in range(ord("a"), ord("z"))])))

    def map_variables(self, expr, values):
        """
        :param expr: logic expression
        :param values: values of every variable
        :return: logic expression with mapped values in place of variables
        """
        variables = "TF" + self.get_expression_variables(expr)
        values = "10" + values
        mapped = list(expr)
        for i, c in enumerate(mapped):
            pos = variables.find(c)
            if pos >= 0:
                mapped[i] = bool(int(values[pos]))
        return mapped

    def evaluate(self, postfix, values):
        """
        :param postfix: logic expression in reversed polish notation
        :param values: entry values for exery variable
        :return: evaluated exrpession to True of False
        """
        postfix = self.map_variables(postfix, values)
        stack = []
        was_nand = False
        for i in postfix:
            if not self.is_operator(i):
                stack.append(i)
            else:
                if i == "&":
                    stack.append(stack.pop() & stack.pop())
                elif i == "|":
                    stack.append(stack.pop() | stack.pop())
                elif i == "^":
                    stack.append(stack.pop() ^ stack.pop())
                elif i == "~":
                    stack.append(not stack.pop())
                elif i == ">":
                    stack.append(stack.pop() or (not stack.pop()))
                elif i == "/":
                    if was_nand:
                        stack.append(not (stack.pop() & (not stack.pop())))
                    else:
                        stack.append(not (stack.pop() & stack.pop()))
                        was_nand = True
                if i != "/":
                    was_nand = False
        p = stack.pop()
        return p

    def generate_binaries(self, n):
        """
        :param n: number of bites
        :return: list of all possible binaries of given lentght
        """
        for i in range(2 ** n):
            yield bin(i)[2:].rjust(n, '0')

    def generate_truth_table(self, postfix):
        """
        :param postfix: logic expression in reversed polish notation
        :return: all binaries that give true for given logic
        """
        variable_count = len(self.get_expression_variables(postfix))
        if variable_count == 0:
            if self.evaluate(postfix, ""):
                return "T"
            else:
                return "F"
        return set([val for val in self.generate_binaries(variable_count) if self.evaluate(postfix, val)])

    def check_expressions_equality(self, expr1, expr2):
        """
        :param expr1: first logic expression
        :param expr2: second logic expression
        :return: True if two logic function are equal
        """
        tt1 = self.generate_truth_table(self.convert_to_rpn(expr1))
        tt2 = self.generate_truth_table(self.convert_to_rpn(expr2))
        return tt1 == tt2

    def construct_tree(self, postfix):
        """
        :param postfix: logic expression in reversed polish notation
        :return: tree representation of given logic
        """
        stack = []

        for char in postfix:

            if not self.is_operator(char):
                stack.append(char)
            else:
                if char == '~':
                    t = (char, stack.pop())
                else:
                    right = stack.pop()
                    left = stack.pop()
                    if right[0] == char and char not in ">":
                        right = right[1]
                    else:
                        right = [right]
                    if left[0] == char:
                        left = left[1]
                    else:
                        left = [left]
                    t = (char, left + right)
                stack.append(t)

        t = stack.pop()
        return t

    def minimize_representation(self, expr):
        """
        :param expr: logic expression to minimize it's representation
        :return: minimized logic expression
        """
        if type(expr) is not tuple:
            return expr
        if expr[0] == '~':
            ne = (expr[0], self.minimize_representation(expr[1]))
        else:
            ne = (expr[0], [self.minimize_representation(e) for e in expr[1]])
        done = False
        while not done:
            expr = ne
            ne = self.find_sheffer_stroke(ne)
            ne = self.find_implications(ne)
            if expr == ne:
                done = True

        return expr

    def find_sheffer_stroke(self, expr):
        """
        :param expr: logic expression
        :return: logix expression with found nand
        """
        if type(expr) is not tuple:
            return expr
        if expr[0] == '~':
            if expr[1][0] == '&':
                expr = ('/', expr[1][1])
        return expr

    def find_implications(self, expr):
        """
        :param expr: logic expression
        :return: logic expression with found implications
        """
        if type(expr) is not tuple:
            return expr
        if expr[0] == '|':
            done = False
            while not done:
                done = True
                for i1, e1 in enumerate(expr[1]):
                    if e1[0] == '~':
                        for i2, e2 in enumerate(expr[1]):
                            if i1 != i2 and e2[0] != '~':
                                expr[1][i1] = ('>', [e1[1][0], e2])
                                del expr[1][i2]
                                done = False
                                break
                        if done:
                            for i2, e2 in enumerate(expr[1]):
                                if i1 != i2:
                                    expr[1][i1] = ('>', [e1[1][0], e2])
                                    del expr[1][i2]
                                    done = False
                                    break
                    if not done:
                        break
            if len(expr[1]) == 1:
                expr = expr[1][0]
        return expr

    def tree_to_rpn(self, expr):
        """
        :param expr: logic expression in form (operator, [expressions])
        :return: reversed polish notation representation of given logic
        """
        if type(expr) is not tuple:
            return [expr]
        result = [expr[0]]

        for i, e in enumerate(reversed(expr[1])):
            result += self.tree_to_rpn(e)
            if i < len(expr[1]) - 3:
                result.append(expr[0])

        return list(reversed(result))

    def tree_to_logic(self, expr, prec):
        """
        :param expr: expression in form (operator, [expressions])
        :param prec: precedens of higher expression
        :return: string representation of given logic expression
        """
        if type(expr) is not tuple:
            return expr
        if expr[0] == '~':
            if type(expr[1]) is tuple:
                result = '~(' + self.tree_to_logic(expr[1]) + ')'
            else:
                result = '~' + expr[1]
        else:
            result = [self.tree_to_logic(e, self.get_precedence(expr[0])) for e in expr[1]]
            result = expr[0].join(result)
            if prec >= self.get_precedence(expr[0]):
                result = '(' + result + ')'
        return result


class QuineMcCluskey:

    def __init__(self, use_xor=False):
        self.use_xor = use_xor  # Whether or not to use XOR and XNOR operations
        self.n_bits = 0  # number of bits

    def simplify(self, minterms):
        """
        :param minterms: set of binaries for logic expression evaluating to True
        :return: set of logic expression for given minterms
        """

        if len(minterms) == 0:
            return None

        # setting number of bits
        self.n_bits = max(len(i) for i in minterms)
        if self.n_bits != min(len(i) for i in minterms):
            return None

        # dict of bianries and set of binaries they originated from
        terms = dict([(t, {t}) for t in minterms])

        # Finding all prime implicants of the function
        prime_implicants = self.__find_prime(terms)

        if not self.use_xor:
            # find the essential prime implicants of the function using Petrick's method
            unate_implicants = self.unate_cover(prime_implicants, minterms)
            return unate_implicants
        else:
            # find the essential prime implicants of the function
            essential_implicants = self.__find_essential(prime_implicants)
            return essential_implicants

    def __reduce_xor(self, term1, term2):
        """
        :param term1:
        :param term2:
        :return: xored term1 and term2
        """
        reduced = dict()
        differences = [0, 0]
        new_term = []
        for c1, c2 in zip(term1[0], term2[0]):
            if c1 in ['^', '~'] or c2 in ['^', '~']:
                return reduced
            elif c1 != c2:
                new_term.append('^')
                differences[c1 == '0'] += 1
            else:
                new_term.append(c1)
        if differences[0] == 1 and differences[1] == 1:
            reduced[''.join(new_term)] = term1[1] | term2[1]
        return reduced

    def __reduce_xnor(self, term1, term2):
        """
        :param term1:
        :param term2:
        :return: xnored term1 and term2
        """
        reduced = dict()
        differences = [0, 0]
        new_term = []
        for c1, c2 in zip(term1[0], term2[0]):
            if c1 in ['^', '~'] or c2 in ['^', '~']:
                return reduced
            elif c1 != c2:
                new_term.append('~')
                differences[c1 == '0'] += 1
            else:
                new_term.append(c1)
        if (differences[0] == 2 and differences[1] == 0) or (differences[0] == 0 and differences[1] == 2):
            reduced[''.join(new_term)] = term1[1] | term2[1]
        return reduced

    def __find_xor_and_xnor(self, terms):
        """
        :param terms: terms of logic function
        :return: terms with xor and xnor
        """
        n_groups = self.n_bits + 1
        groups = [dict() for i in itertools.repeat(None, n_groups)]
        for t in terms.items():
            groups[t[0].count('1')].update(dict([t]))
        for i, group in enumerate(groups):
            for t1, t2 in [(t1, t2) for t1 in group.items() for t2 in group.items()]:
                terms.update(self.__reduce_xor(t1, t2))
            for t1, t2 in [(t1, t2) for t1 in group.items() if i < n_groups - 2 for t2 in groups[i + 2].items()]:
                terms.update(self.__reduce_xnor(t1, t2))
        return terms

    def __find_prime(self, terms):
        """
        :param terms: terms of logic function
        :return: prime implicants of logic function
        """

        marked = dict()

        if self.use_xor:
            terms = self.__find_xor_and_xnor(terms)

        while True:
            groups = dict()
            for t in terms.items():
                key = (t[0].count('1'), t[0].count('^'), t[0].count('~'))
                if key not in groups:
                    groups[key] = dict()
                groups[key].update(dict([t]))

            terms = dict()
            used = dict()

            for group, next_group in [(groups[k], groups[(k[0] + 1, k[1], k[2])]) for k in groups if
                                      (k[0] + 1, k[1], k[2]) in groups]:
                for t1 in group.items():
                    for i, c1 in enumerate(t1[0]):
                        if c1 == '0':
                            t2 = t1[0][:i] + '1' + t1[0][i + 1:]
                            if t2 in next_group:
                                t2 = (t2, next_group[t2])
                                t12 = (t1[0][:i] + '-' + t1[0][i + 1:], t1[1] | t2[1])
                                used.update(dict([t1]))
                                used.update(dict([t2]))
                                terms.update(dict([t12]))

            for group, complement_group in [(groups[k], groups[(k[0] + 1, k[2], k[1])]) for k in groups if
                                            k[1] > 0 and (k[0] + 1, k[2], k[1]) in groups]:
                for t1 in group.items():
                    complement_t1 = t1[0].replace('^', '~')
                    for i, c1 in enumerate(t1[0]):
                        if c1 == '0':
                            t2 = complement_t1[:i] + '1' + complement_t1[i + 1:]
                            if t2 in complement_group:
                                t2 = (t2, complement_group[t2])
                                t12 = (t1[0][:i] + '^' + t1[0][i + 1:], t1[1] | t2[1])
                                used.update(dict([t1]))
                                terms.update(dict([t12]))

            for group, complement_group in [(groups[k], groups[(k[0] + 1, k[2], k[1])]) for k in groups if
                                            k[2] > 0 and (k[0] + 1, k[2], k[1]) in groups]:
                for t1 in group.items():
                    complement_t1 = t1[0].replace('~', '^')
                    for i, c1 in enumerate(t1[0]):
                        if c1 == '0':
                            t2 = complement_t1[:i] + '1' + complement_t1[i + 1:]
                            if t2 in complement_group:
                                t2 = (t2, complement_group[t2])
                                t12 = (t1[0][:i] + '~' + t1[0][i + 1:], t1[1] | t2[1])
                                used.update(dict([t1]))
                                terms.update(dict([t12]))

            marked.update(dict([m for g in list(groups.values()) for m in list(g.items()) if m[0] not in used]))

            if not used:
                break

        return marked

    def __find_essential(self, terms):
        """
        :param terms: prime implicants of logic function
        :return: essential implicants of loogic function
        """
        essential_iplicants_range = set()
        essential_iplicants = dict()

        groups = dict()
        for t in terms.items():
            n = self.__get_term_rank(t)
            if n not in groups:
                groups[n] = dict()
            groups[n].update(dict([t]))

        for t in sorted(list(groups.keys()), reverse=True):
            for g in groups[t].items():
                if not g[1] <= essential_iplicants_range:
                    essential_iplicants.update([g])
                    essential_iplicants_range |= g[1]
        if len(essential_iplicants) == 0:
            essential_iplicants = {'-' * self.n_bits}
        return essential_iplicants

    def __get_term_rank(self, term):
        n = 0
        for t in term[0]:
            if t == "-":
                n += 8
            elif t == "^":
                n += 4
            elif t == "~":
                n += 2
            elif t == "1":
                n += 1
        return 4 * len(term[1]) + n

    def convert_to_logic(self, terms, expr_vars):
        """
        :param terms: essential implicants of logic funtion
        :param expr_vars: variables of logic funtion
        :return: string form of logic funtion
        """
        results = []
        n_terms = len(terms)
        for t in terms:
            if len(t) == t.count('-'):
                return 'T'
            and_result = []
            xor_result = []
            xor = t.count('^')
            xnor = t.count('~')
            fixed = t.count('1') + t.count('0')
            brackets = n_terms > 1 and (fixed > 1 or (fixed > 0 and xor + xnor > 0))
            for i in [ic[0] for ic in enumerate(t) if ic[1] == '1']:
                and_result.append(expr_vars[i])
            for i in [ic[0] for ic in enumerate(t) if ic[1] == '0']:
                and_result.append('~' + expr_vars[i])
            if xor or xnor:
                for i in [ic[0] for ic in enumerate(t) if ic[1] in '~^']:
                    xor_result.append(expr_vars[i])
                if xnor:
                    and_result.append('~(' + '^'.join(xor_result) + ')')
                else:
                    and_result.append('^'.join(xor_result))
            if brackets:
                results.append('(' + '&'.join(and_result) + ')')
            else:
                results.append('&'.join(and_result))
        return '|'.join(results)

    def unate_cover(self, primes, ones):
        """
        Petrick's method for finding essential implicants oof given logic funtion
        :param primes: prime implicants of logic funtion
        :param ones: all binaries of logic function
        :return: essential implicants of logic function
        """
        chart = []
        for one in ones:
            column = []
            for i, prime in enumerate(primes.values()):
                if one in prime:
                    column.append(i)
            chart.append(column)
        covers = []
        if len(chart) > 0:
            covers = [{i} for i in chart[0]]
        for i in range(1, len(chart)):
            new_covers = []
            for cover in covers:
                for prime_index in chart[i]:
                    x = set(cover)
                    x.add(prime_index)
                    append = True
                    for j in range(len(new_covers) - 1, -1, -1):
                        if x <= new_covers[j]:
                            del new_covers[j]
                        elif x > new_covers[j]:
                            append = False
                    if append:
                        new_covers.append(x)
            covers = new_covers
        min_complexity = 99999999
        for cover in covers:
            primes_in_cover = [list(primes.keys())[prime_index] for prime_index in cover]
            complexity = self.calculate_complexity(primes_in_cover)
            if complexity < min_complexity:
                min_complexity = complexity
                result = primes_in_cover

        return result

    def calculate_complexity(self, primes):
        return len(self.convert_to_logic(primes, 'a' * self.n_bits))


def main():
    input_expression = input("Enter logic expression: ").replace(" ", "")

    rpn = RPN()

    input_postfix = rpn.convert_to_rpn(input_expression)

    if input_postfix == "ERROR":
        print("ERROR")
        return

    truth_table = rpn.generate_truth_table(input_postfix)

    if truth_table in ['T', 'F']:
        print(truth_table)
    else:
        input_min_logic = rpn.tree_to_logic(rpn.minimize_representation(rpn.construct_tree(input_postfix)), 0)

        qmc = QuineMcCluskey(False)
        terms = qmc.simplify(truth_table)
        logic = rpn.tree_to_logic(rpn.minimize_representation(rpn.construct_tree(rpn.convert_to_rpn(
            qmc.convert_to_logic(terms, rpn.get_expression_variables(input_postfix))))), 0)

        qmc.use_xor = True
        xor_xnor_terms = qmc.simplify(truth_table)
        xor_xnor_logic = rpn.tree_to_logic(rpn.minimize_representation(rpn.construct_tree(rpn.convert_to_rpn(
            qmc.convert_to_logic(xor_xnor_terms, rpn.get_expression_variables(input_postfix))))), 0)

        shortest_logic = list(filter(lambda x: rpn.check_expressions_equality(x, input_expression),
                        [xor_xnor_logic, logic, input_min_logic]))
        shortest_logic = reduce((lambda x, y: x if len(x) < len(y) else y), shortest_logic, input_expression)

        print(shortest_logic)


if __name__ == "__main__":
    main()
