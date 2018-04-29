import string
import itertools


class RPN:
    operators = {'>': 1, '&': 2, '|': 2, '/': 2, '^': 3, '~': 4}
    variables = string.ascii_lowercase + "TF"

    def is_operator(self, c):
        return c in self.operators

    def get_precedence(self, c):
        if self.is_operator(c):
            return self.operators[c]
        else:
            return 0

    def is_binary(self, c):
        if c in ['>', '&', '|', '/', '^']:
            return True
        if c in ['~']:
            return False

    def convert_to_rpn(self, infix):
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
        """sprawdza poprawność syntaktyczną wyrażenia"""
        state = True  # True - oczekiwany nawias ( lub zmienna, False - oczekiwany nawias ) lub operator
        par_count = 0  # licznik nawiasów
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
        return par_count == 0 and not state  # poprawne wyrażenie musi kończyć sie stanem False i mieć zamknięte wszystkie nawiasy

    def get_expression_variables(self, expr):
        return ''.join(sorted(set([char for char in expr if ord(char) in range(ord("a"), ord("z"))])))

    def map_variables(self, expr, values):
        variables = "TF" + self.get_expression_variables(expr)
        values = "10" + values
        mapped = list(expr)
        for i, c in enumerate(mapped):
            pos = variables.find(c)
            if pos >= 0:
                mapped[i] = bool(int(values[pos]))
        return mapped

    def evaluate(self, postfix, values):
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
        for i in range(2 ** n):
            yield bin(i)[2:].rjust(n, '0')

    def generate_truth_table(self, postfix):
        variable_count = len(self.get_expression_variables(postfix))
        if variable_count == 0:
            if self.evaluate(postfix, ""):
                return "T"
            else:
                return "F"
        return set([val for val in self.generate_binaries(variable_count) if self.evaluate(postfix, val)])

    def construct_tree(self, postfix):
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
        if type(expr) is not tuple:
            return expr
        if expr[0] == '~':
            if expr[1][0] == '&':
                expr = ('/', expr[1][1])
        return expr

    def find_implications(self, expr):
        if type(expr) is not tuple:
            return expr
        if expr[0] == '|':
            done = False
            while not done:
                done = True
                for i1, e1 in enumerate(expr[1]):
                    if e1[0] == '~':
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
        if type(expr) is not tuple:
            return [expr]
        result = [expr[0]]

        for i, e in enumerate(reversed(expr[1])):
            result += self.tree_to_rpn(e)
            if i < len(expr[1]) - 3:
                result.append(expr[0])

        return list(reversed(result))

    def tree_to_logic(self, expr, prec):
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
        self.use_xor = use_xor  # Whether or not to use XOR and XNOR operations.
        self.n_bits = 0  # number of bits (i.e. self.n_bits == len(ones[i]) for every i).

    def simplify(self, minterms):
        if len(minterms) == 0:
            return None

        self.n_bits = max(len(i) for i in minterms)
        if self.n_bits != min(len(i) for i in minterms):
            return None

        terms = dict([(t, {t}) for t in minterms])

        prime_implicants = self.__find_prime(terms)
        essential_implicants = self.__find_essential(prime_implicants)
        if essential_implicants == {'-' * self.n_bits}:
            return essential_implicants
        if not self.use_xor:
            unate_implicants = self.unate_cover(prime_implicants, minterms)
            return unate_implicants
        else:
            return essential_implicants

    def __reduce_xor(self, term1, term2):
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
    expr = input("Enter logic expression: ").replace(" ", "")

    rpn = RPN()

    postfix = rpn.convert_to_rpn(expr)

    if postfix == "ERROR":
        print("ERROR")
        return

    truth_table = rpn.generate_truth_table(postfix)

    if truth_table in ['T', 'F']:
        print(truth_table)
    else:
        qmc = QuineMcCluskey(False)
        terms = qmc.simplify(truth_table)
        qmc.use_xor = True
        x_terms = qmc.simplify(truth_table)
        terms_log = rpn.tree_to_logic(rpn.minimize_representation(
            rpn.construct_tree(rpn.convert_to_rpn(qmc.convert_to_logic(terms, rpn.get_expression_variables(postfix))))),
                                      0)
        x_terms_log = rpn.tree_to_logic(rpn.minimize_representation(rpn.construct_tree(
            rpn.convert_to_rpn(qmc.convert_to_logic(x_terms, rpn.get_expression_variables(postfix))))), 0)
        expr = rpn.tree_to_logic(rpn.minimize_representation(rpn.construct_tree(postfix)), 0)

        if len(expr) < len(x_terms_log) and len(expr) < len(terms_log):
            print(expr)
        if len(x_terms_log) <= len(terms_log):
            print(x_terms_log)
        else:
            print(terms_log)


main()
