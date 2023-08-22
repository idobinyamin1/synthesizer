import logging
import operator
import re

# from z3 import Int, ForAll, Implies, Not, And, Or, Solver, unsat

from adt.tree import Tree
from while_lang.syntax import WhileParser, fill_holes

logging.basicConfig(level=logging.DEBUG)

from z3 import *

x = Int('x')
y = Int('y')
z = Int('z')
t = Int('t')
C0 = Int('C0')
C1 = Int('C1')
C2 = Int('C2')

OP = {'+': operator.add, '-': operator.sub,
      '*': operator.mul, '/': operator.floordiv,
      '!=': operator.ne, '>': operator.gt, '<': operator.lt,
      '<=': operator.le, '>=': operator.ge, '=': operator.eq}


def mk_env(pvars):
    return {v: Int(v) for v in pvars}


def mk_env_t(pvars):
    return {v: Int(v + '_') for v in pvars}


def upd(d, k, v):
    d = d.copy()
    d[k] = v
    return d


def eval_expr(env, expr):
    if expr.root == 'id':
        return env[expr.subtrees[0].root]
    elif expr.root == 'num':
        return expr.subtrees[0].root
    elif expr.root in ['+', '-', '*', '/', '!=', '>', '<', '<=', '>=', '=']:
        return OP[expr.root](eval_expr(env, expr.subtrees[0]), eval_expr(env, expr.subtrees[1]))
    else:
        raise ValueError("Unknown expression: " + expr)


def define_z3_variables(variable_names):
    z3_variables = [Int(var_name) for var_name in variable_names]
    return z3_variables


def verify(P, ast_list, Q_list, linv=None):
    """
    Verifies a Hoare triple {P} c {Q}
    Where P, Q are assertions (see below for examples)
    and ast is the AST of the command c.
    Returns `True` iff the triple is valid.
    Also prints the counterexample (model) returned from Z3 in case
    it is not.
    """
    pvars = []
    env = []
    all_the_signed_from_asserts_so_far = []
    solver = Solver()
    j = 0
    for Q_original in Q_list:
        operator_Q = get_operator(Q_original)
        str_Q = str(Q_original).split(operator_Q)
        all_the_signed_from_asserts_so_far.append(str_Q[0].replace(' ', ''))
    for ast, Q_original in zip(ast_list, Q_list):
        pvars.append(set(v for v in ast.terminals if isinstance(v, str)))
        pvars_union = list(set().union(*pvars))
        pvars_old = [p for p in pvars_union if p[0] != 'C']
        pvars_old_unassigned_in_assert = [i for i in pvars_old if i not in all_the_signed_from_asserts_so_far]
        pvars_old_unassigned = [p for p in pvars_old_unassigned_in_assert if check_if_not_assigned(ast, p)]

        # condition = ForAll([x, y], y == 2 * x)
        # Q_new = lambda d: bool_operator(d[str_Q[0].replace(' ', '')], operator_Q, evaluate_expression(str_Q[1], d))
        # Q_new = lambda d: evaluate_expression(f"(d[str_Q[0].replace(' ', '')] == {str_Q[1]}", d))
        Q_new = lambda d: evaluate_expression(Q_original, d)
        Q = lambda d: Not(Q_new(d))
        env.append(mk_env(pvars[-1]))
        env[-1]['linv'] = linv
        # print("weakest_precondition = ", weakest_precondition(env))

        if pvars_old_unassigned:
            solver.add(ForAll([Int(v) for v in pvars_old_unassigned], (Not(Implies(P(env[-1]), wp(ast, Q)(env[-1]))))))
        else:
            solver.add((Not(Implies(P(env[-1]), wp(ast, Q)(env[-1])))))
        # solver.add(Not(Implies(P(env[-1]), wp(ast, Q)(env[-1]))))

        j += 1

    if solver.check() == sat:
        """for every C0,C1,... we print the value of C0,C1,... and return True"""
        # print(solver.model(), end=" ")
        model = solver.model()
        p_new = [p for p in pvars_union if p not in pvars_old]
        c_values = [model[Int(p)].as_long() for p in p_new]
        # for p in p_new:
        #     print(p, "=", model[Int(p)].as_long(), end =" ; ")
        # print()
        return c_values
    else:
        return False


def check_if_not_assigned(ast, p):
    """Check if the p variable hasn't been assign with ':=' yet
    """
    if ast.root == ':=':
        if ast.subtrees[0].subtrees[0].root == p:
            return False
    for subtree in ast.subtrees:
        if subtree.root == ':=':
            if subtree.subtrees[0].subtrees[0].root == p:
                return False
    return True


def get_operator(Q):
    """Return the operator of the assertion"""
    if '==' in str(Q):
        return '=='
    elif '!=' in str(Q):
        return '!='
    elif '<=' in str(Q):
        return '<='
    elif '>=' in str(Q):
        return '>='
    elif '<' in str(Q):
        return '<'
    elif '>' in str(Q):
        return '>'
    else:
        raise ValueError("Unknown operator: " + Q)


def bool_operator(left_side, operator, right_side):
    """Return the assertion of the operator""
    """
    if operator == '==':
        return left_side == right_side
    elif operator == '!=':
        return left_side != right_side
    elif operator == '<=':
        return left_side <= right_side
    elif operator == '>=':
        return left_side >= right_side
    elif operator == '<':
        return left_side < right_side
    elif operator == '>':
        return left_side > right_side
    else:
        raise ValueError("Unknown operator: " + operator)


def wp(c: Tree, Q: callable) -> callable:
    """ maps a command c and a postcondition Q to the weakest precondition P that
     will make the triple {P} c {Q} valid """
    if c.root == 'skip':
        return Q
    elif c.root == ':=':
        assert c.subtrees[0].root == 'id'
        left_hand = c.subtrees[0].subtrees[0].root
        return lambda env: Q(upd(env, left_hand, eval_expr(env, c.subtrees[1])))
    elif c.root == ';':
        return wp(c.subtrees[0], wp(c.subtrees[1], Q))
    elif c.root == 'if':
        return lambda env: Or(And(eval_expr(env, c.subtrees[0]), wp(c.subtrees[1], Q)(env)), And(Not(eval_expr(env, c.subtrees[0])), wp(c.subtrees[2], Q)(env)))
    elif c.root == 'while':
        # we assume that the invariant is given at env['linv'] and env['linv'] is a callable
        def helper(env):
            pvars = env.keys()
            env_t = mk_env_t(pvars)
            return And(env['linv'](env),
                       And(Implies(And(env['linv'](env_t), eval_expr(env_t, c.subtrees[0])), wp(c.subtrees[1], env['linv'])(env_t)),
                           Implies(And(env['linv'](env_t), Not(eval_expr(env_t, c.subtrees[0]))), Q(env_t))))

        return helper
    else:
        raise Exception("Unknown command: {c}".format(c=c))


def drop_unnew_variables(list_vars):
    """Dispose all the unnew variables in the list_vars
    All the new Vars tsart with 'C' and then a number
    """
    new_list = []
    for var in list_vars:
        if var[0] == 'C':
            new_list.append(var)
    return new_list


def drop_assertion(program):
    """Drop the assertion from the program
    """
    program = program.split(';')
    new_program = []
    for i in range(len(program)):
        if not 'assert' in program[i]:
            new_program.append(program[i])

    listToStr = ';'.join([str(element) for element in new_program])
    return listToStr


def evaluate_expression(expression, variable_dict):
    # Replace variable names with their corresponding values from the dictionary
    #  Do it until no more replacement can be made
    def replace_variables_with_values(expression, variable_dict):
        for var, value in variable_dict.items():
            expression = expression.replace(var, str(value))
        return expression

    while True:
        old_expression = expression
        expression = replace_variables_with_values(expression, variable_dict)
        if old_expression == expression:
            break

    # Evaluate the modified expression

    try:
        result = eval(expression)
        return result

    except:
        return None


def add_assert_for_every_assignment(program):
    """Add an assertion for every assignment
    """
    program = program.split(';')
    new_program = []
    for i in range(len(program)):
        if ':=' in program[i]:
            new_program.append(program[i])
            new_line_assert = program[i]
            change_operator = new_line_assert.replace(':=', '==')
            new_program.append('assert ' + change_operator)
        else:
            new_program.append(program[i])

    listToStr = ';'.join([str(element) for element in new_program]) + ';'
    return listToStr


def from_assert_to_list_to_verify(program):
    """Return a list of the assertions to verify and for each the Q
    """
    op_list = []
    var_a_list = []
    var_b_list = []
    list_ast = []
    list_Q = []
    j = 0
    split_program = program.split(';')
    for i in range(len(split_program)):
        if 'assert' in split_program[i]:
            s_program = split_program[:i]
            listToStrProgram = ';'.join([str(element) for element in s_program])
            new_prog = drop_assertion(listToStrProgram)
            list_ast.append(WhileParser()(new_prog))

            operator_assert = get_operator(split_program[i])
            op_list.append(operator_assert)
            var_a_list.append(split_program[i].split(operator_assert)[0].replace("assert ", ''))
            var_b_list.append(split_program[i].split(operator_assert)[1])

            list_Q.append(var_a_list[j] + op_list[j] + var_b_list[j])

            j += 1

    return list_ast, list_Q


def from_str_Q_list_to_Q_list(list_Q_str):
    """Return a list of the assertions to verify
    """
    list_Q = []
    for i in range(len(list_Q_str)):
        vars_str = str(list_Q_str[i]).split(' ')
        if vars_str[1] == '!=':
            list_Q.append(lambda d: d[str(vars_str[0])] != vars_str[2])
        elif vars_str[1] == '==':
            list_Q.append(lambda d: d[str(vars_str[0])] == vars_str[2])

    return list_Q


class synthesizer:
    def __init__(self, program, linv=None):
        self.program = program
        self.P = lambda _: True
        self.linv = linv

    def __call__(self):
        list_ast, list_Q = from_assert_to_list_to_verify(self.program)
        c_values = verify(self.P, list_ast, list_Q, self.linv)

        # Fill the holes '??' with C0, C1, C2, in the program
        program = fill_holes(self.program)
        # replace in the program all the C0, C1, C2, ... with the values that were found
        #  in the verification process
        for i in range(len(c_values)):
            program = program.replace('C' + str(i), str(c_values[i]))
        return drop_assertion(program)


if __name__ == '__main__':
    # feature2
    tests = []

    # basic test
    input = "y := ?? ; assert y == 10;"
    output = "y := 10 ;"
    tests.append((input, output))

    assert synthesizer(tests[0][0])() == tests[0][1]

    # simple arithmetic
    input = "x := 5 ; y := x + ?? ; assert y == 10;"
    output = "x := 5 ; y := x + 5 ;"
    tests.append((input, output))

    assert synthesizer(tests[1][0])() == tests[1][1]

    # simple arithmetic with dependency between variables in the assert
    input = "y := x * ?? ; assert y == x * 2;"
    output = "y := x * 2 ;"
    tests.append((input, output))

    assert synthesizer(tests[2][0])() == tests[2][1]

    input = "y := x * ?? ; assert y == x + x;"
    output = "y := x * 2 ;"
    tests.append((input, output))

    assert synthesizer(tests[3][0])() == tests[3][1]

    # simple arithmetic with < and >
    input = "y := x + ?? ; assert y > x;"
    output = "y := x + 1 ;"  # could any number that is greater than 1
    tests.append((input, output))

    assert synthesizer(tests[4][0])() == tests[4][1]

    # if condition 1 the test is not good, we dont have a tree for '==' and we need to make sure WhileParser()(input) is Valid
    input = "y := 0 ; x := ?? ; if x = 5 then y := 10  else skip ; assert y == 10;"
    output = "y := 0 ; x := 5 ; if x = 5 then ( y := 10 ) ;"
    tests.append((input, output))

    # assert synthesizer(tests[5][0])() == tests[5][1]




    # assert synthesizer(tests[6][0])() == tests[6][1]

    """
    Tasks:
    1. Make the fix for Q to be valid for any expression on the right side and not just numbers (line 126)
    2. Make the program work with any number of assertions
    3. Make the program work without invariant loop

    At the print get rid of all of the unnew variables
    At the end make sure you can take a program with examples and redefine them as assertions

    note: if one of the new vars C0, C1, C2, ... is not in the output then any value is valid for them 
       (for any value there are values for the other vars that will make the assertion true)
    """

    #
    #
    #
    # # Example 1
    # print('Example 1: Simple case with 1 assertion and 1 new variable in the test')
    # pvars = ['x', 'y']
    # program = "y := ?? *  x; assert y == 0; x := ??; assert x == 2"
    # P = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)
    #
    # #
    # # Example 2
    # print('Example 2: Simple case with 1 assertion and 1 new variable in the test')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x *  ??; assert y == 7; assert x == 7;"
    # P = lambda _: True
    #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)
    #
    #
    # # Example 6
    # print('Example 333: Simple case with 1 assertion and 1 new variable in the test')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x *  ??; assert y == 2 * x ;"
    # P = lambda _: True
    #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)

    #
    # # Example 2
    # print('Example 2: Nothin we can ')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x * ??;assert y == 9; assert y != 1;"
    # P = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)

    # # Example 3
    # print('Example 3: Simple case with 2 assertions and 1 new variable in the test opposite order from Example 2')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x * ??;assert y != 9 ; assert y == 2;"
    # P = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)
    #
    # # Example 5
    # print('Example 5: Simple case with 2 assertions and 1 new variable in the test for solution in a range')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x * ??;assert y > 7; assert y < 10;"
    # P = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)

    # # Example 6
    # print('Example 6: Simple case when there is no solution')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x * ??;assert y > 7; assert y < 6;"
    # P = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)
    #
    # # Example 7
    # print('Example 7: Case with 3 assertions and 2 new variable in the test')
    # pvars = ['x', 'y', 'C0']
    # program = "y := x * ??;assert y == 5; assert y < 10; b:= y + ??; assert b ==2;"
    # P = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=None)

    # # Example 8
    # print('Example 8 Fail: Case with asseret in the middle and in the end with 2 new variables in the test')
    # pvars = ['a', 'b', 'i']
    # program = "a := ?? ; i := 7; assert a==4; b:= a*i+??; assert b == 44"
    # work: program = "a := ?? ; i := 7; assert a==4; b:= a+??; assert b == 44" # Working with 1 operator on the right side
    # P = lambda _: True
    # linv = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=linv)

    # # Example 9
    # print('Example 9 Fail: Simple case with linv, assert at the end of the program')
    # pvars = ['a', 'b', 'i']
    # program = "a := 2 ; i:= 5 ; while i < ?? do ( a := a + 1) ; assert a == 13"
    # P = lambda _: True
    # linv = lambda _: True
    # #
    # list_ast, list_Q = from_assert_to_list_to_verify(program)
    # verify(P, list_ast, list_Q, linv=linv)

    # # Example 2
    # reset_vars()
    # ast = []
    #
    # pvars = ['x', 'y', 'C0']
    # program = "y := x * ??; assert y == 10; assert y > 4;"
    # P = lambda _: True
    #
    # list_verify_each_with_Q, Q_list = from_assert_to_list_to_verify(program)
    # verify(P, ast, Q_list, linv=None)

    #     solution_for_assert need to get rid of unnew variables

    #
    # pvars = ['x', 'y', 'C0']
    # program = "y := 0 ; while y < 11 do ( y := y + ?? )"
    # P = lambda d: True
    # Q = lambda d: d['y'] != 12
    # Q1 = lambda d: d['y'] != 11
    # Q2 = lambda d: d['y'] != 9
    # Q3 = lambda d: d['y'] != 8
    # Q_all = lambda d: And(Q1(d), Q2(d), Q3(d))
    # linv = lambda d: And (d['y'] <= 10)
    # ast = WhileParser()(program)
    # assert verify(P, ast, Q, linv=linv) is True

"""
    a = 2
    b = 3
    assert a == 1

    a = b + 2
    d =2 
    assert d==1

"""

# verify1
"""
    a = 2
    b = 3
    assert a == 1
P= initial
Q = assert
"""

# verify2
"""
    a = 2
    b = 3
    assert a == 1

    a = b + 2
    d =2 
    assert d==1
P= initial 
Q = assert d==1
"""

# and veify