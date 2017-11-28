#!usr/bin/python3
# the assignment 1 of COMP4418 written by YONGXI YANG 
# time for design :  12:00am 24/08/2017
# the student number is Z5103793
# the test envirnment :
#
# Python 3.6.2 (v3.6.2:5fd33b5, Jul  8 2017, 04:14:34) [MSC v.1900 32 bit (Intel)] on win32
# Type "help", "copyright", "credits" or "license" for more information.
#
# the input format is
#        python assn1q3.py '[p imp q, (neg r) imp (neg q)] seq [p imp r]'
#
# But sorry, professor:
#       I forget to design API of print the proving process so the result can only show the Truth or False

import argparse
import re
from collections import deque
import copy

def parserArgument():
    
    parser = argparse.ArgumentParser(description='Automatic Prove Machine')
    parser.add_argument('proposition',type = str,help = "the propsition you need to prove,the format is '[p imp q, (neg r) imp (neg q)] seq [p imp r]'",action = 'store',nargs = '+')
    return parser.parse_args()


def split_proposition(Sequent):
    """
    >>> split_proposition('[] seq []')
    [[], []]
    >>> split_proposition('[p imp q] seq []')
    [['p imp q'], []]
    >>> split_proposition('[] seq [p imp q]')
    [[], ['p imp q']]
    >>> split_proposition('[p imp q] seq [p imp q]')
    [['p imp q'], ['p imp q']]
    """
    condition,result = re.findall('^\[(.*)\] seq \[(.*)\]$',Sequent)[0]

    if condition == '':
        condition = []
    else:
        condition = condition.split(",")
        condition = [i.strip() for i in condition]

    if result == '':
        result = []
    else :
        result = result.split(",")
        result = [i.strip() for i in result]
    
    return [condition,result]


def find_priority(proposition,condition_or_conclusion):
    """
    find the element which has '()'

    >>> find_priority([[], []],0)
    ([[], []], False)
    >>> find_priority([['(q imp a) imp (q imp b)', '(q imp p) imp (q imp c)'], []], 0)
    ([['(q imp p) imp (q imp c)'], []], '(q imp a) imp (q imp b)')
    >>> find_priority([[], ['(q imp a) imp (a iff b)', '(c iff q) imp (a and b)']], 0)
    ([[], ['(q imp a) imp (a iff b)', '(c iff q) imp (a and b)']], False)
    >>> find_priority([['q imp p', '(q imp p) imp (q imp c)', 'q and c'], []],0)
    ([['q imp p', 'q and c'], []], '(q imp p) imp (q imp c)')
    """
    if len(proposition[condition_or_conclusion]) == 0 :
        return proposition,False

    for i in range(len(proposition[condition_or_conclusion])):
        if '(' in proposition[condition_or_conclusion][i]:
            break

    if ")" in  proposition[condition_or_conclusion][i]:
        formular = proposition[condition_or_conclusion][i]
        del(proposition[condition_or_conclusion][i])
        return proposition,formular
    else:
        return proposition,False

def find_formulae(proposition,condition_or_conclusion):
    """
    this function is find the formulae like 'p imp q','neg r'

    >>> find_formulae([[],[]],0)
    ([[], []], False)
    >>> find_formulae([['p','q'],[]],0)
    ([['p', 'q'], []], False)
    >>> find_formulae([[],['q','c']],0)
    ([[], ['q', 'c']], False)
    >>> find_formulae([['p', 'q'],['q','c']],0)
    ([['p', 'q'], ['q', 'c']], False)
    >>> find_formulae([['neg r'],['q']],0)
    ([[], ['q']], 'neg r')
    >>> find_formulae([['p iff q'],[]],0)
    ([[], []], 'p iff q')
    >>> find_formulae([['p imp q'],[]],0)
    ([[], []], 'p imp q')
    >>> find_formulae([['p and q'],[]],0)
    ([[], []], 'p and q')
    >>> find_formulae([['p or q'],[]],0)
    ([[], []], 'p or q')
    >>> find_formulae([['neg r', 'p iff q', 'p imp q', 'p and q', 'p or q'],[]],0)
    ([['p iff q', 'p imp q', 'p and q', 'p or q'], []], 'neg r')
    >>> find_formulae([['p iff q', 'p imp q', 'p and q', 'p or q'],[]],0)
    ([['p imp q', 'p and q', 'p or q'], []], 'p iff q')
    >>> find_formulae([['p imp q', 'p and q', 'p or q'], []],0)
    ([['p and q', 'p or q'], []], 'p imp q')
    >>> find_formulae([['p and q','p or q'], []],0)
    ([['p or q'], []], 'p and q')
    >>> find_formulae([['p iff q', 'p imp q', 'p and q', 'p or q', 'p', 'q', 'c', 'v', 'neg r'],[]],0)
    ([['p iff q', 'p imp q', 'p and q', 'p or q', 'p', 'q', 'c', 'v'], []], 'neg r')
    """
    dir_priority_process = {
        'neg': '^neg [a-zA-Z]+$',
        'iff': '[a-zA-Z]+ iff [a-zA-Z]+$',
        'imp': '[a-zA-Z]+ imp [a-zA-Z]+$',
        'and': '[a-zA-Z]+ and [a-zA-Z]+$',
        'or' : '[a-zA-Z]+ or [a-zA-Z]+$'
    }
    list_priority_process = ['neg','iff','imp','and','or']

    if len(proposition[condition_or_conclusion]) == 0 :
        return proposition,False
    
    for m in list_priority_process:
        for j in range(len(proposition[condition_or_conclusion])):
            if len(re.findall(dir_priority_process[m],proposition[condition_or_conclusion][j])) != 0:
                fomulae = re.findall(dir_priority_process[m],proposition[condition_or_conclusion][j])[0]
                del(proposition[condition_or_conclusion][j])
                return proposition,fomulae
            else:
                continue

    return proposition,False

def degrade(priority):
    """
    this function can split 'p imp q' into ['p', 'imp', 'q']

    >>> degrade('neg r')
    ['', 'neg', 'r']
    >>> degrade('p iff q')
    ['p', 'iff', 'q']
    >>> degrade('p imp q')
    ['p', 'imp', 'q']
    >>> degrade('p and q')
    ['p', 'and', 'q']
    >>> degrade('p or q')
    ['p', 'or', 'q']
    """
    if len(re.findall('^(neg) ([a-zA-Z]+)',priority)) != 0:
        decompose = [''] + list(re.findall('^(neg) ([a-zA-Z]+)',priority)[0])
    elif len(re.findall('([a-zA-Z]+) (imp|iff|and|or) ([a-zA-Z]+)$',priority)):
        decompose = list(re.findall('([a-zA-Z]+) (imp|iff|and|or) ([a-zA-Z]+)$',priority)[0])
    else:
        decompose = priority
    return decompose

def degrade_priority(priority):
    """
    this function can split '(neg q) imp (neg p)' into '['neg q','imp','neg q']'

    >>> degrade_priority('(neg q) imp (neg p)')
    ['neg q', 'imp', 'neg p']
    >>> degrade_priority('(neg q) and (neg p)')
    ['neg q', 'and', 'neg p']
    >>> degrade_priority('(neg q) iff (neg p)')
    ['neg q', 'iff', 'neg p']
    >>> degrade_priority('(neg q) or (neg p)')
    ['neg q', 'or', 'neg p']
    >>> degrade_priority('neg(q imp p)')
    ['', 'neg', 'q imp p']
    >>> degrade_priority('((neg q) or (neg p)) imp (neg p)')
    ['(neg q) or (neg p)', 'imp', 'neg p']
    >>> degrade_priority('((neg q) or (neg p)) imp ((neg q) iff (neg p))')
    ['(neg q) or (neg p)', 'imp', '(neg q) iff (neg p)']
    >>> degrade_priority('(neg q) and (((neg q) or (neg p)) imp ((neg q) iff (neg p)))')
    ['neg q', 'and', '((neg q) or (neg p)) imp ((neg q) iff (neg p))']
    >>> degrade_priority('neg(neg(neg q))')
    ['', 'neg', 'neg(neg q)']
    >>> degrade_priority('q imp (neg p)')
    ['q', 'imp', 'neg p']
    >>> degrade_priority('(neg q) or p')
    ['neg q', 'or', 'p']
    >>> degrade_priority('q iff ((neg p) imp (neg(q imp q)))')
    ['q', 'iff', '(neg p) imp (neg(q imp q))']
    >>> degrade_priority('((neg p) and (neg(q imp q))) and p')
    ['(neg p) and (neg(q imp q))', 'and', 'p']
    """
    if len(re.findall('^neg\((.*)\)',priority)) != 0 :
        decompose = ['','neg']
        decompose.append(re.findall('^neg\((.*)\)',priority)[0])

    elif priority[0] == '(':
        count = 1
        for k in range(1,len(priority)):
            if priority[k] == '(':
                count += 1
            elif priority[k] == ')':
                count -= 1
            elif count == 0:
                break
        decompose = [priority[1:k-1]]
        # print(decompose,priority[0]+priority[k-1:])
        next_decompose = priority[0]+priority[k-1:]  # the format will be like this '() imp (q imp p)' or '() imp q'
        # print(priority[0]+priority[k:])
        if len(re.findall('^\(\) (imp|iff|and|or) \((.*)\)$',next_decompose)) != 0:

            tmp_priority = list(re.findall('^\(\) (imp|iff|and|or) \((.*)\)$',next_decompose)[0])
            decompose += tmp_priority

        elif len(re.findall('^\(\) (imp|iff|and|or) ([a-zA-z]+)$',next_decompose)) != 0:

            tmp_priority = list(re.findall('^\(\) (imp|iff|and|or) ([a-zA-z]+)$',next_decompose)[0])
            decompose += tmp_priority

    elif len(re.findall('^([a-zA-z]+) (imp|iff|and|or) \((.*)\)$',priority)) != 0:

        decompose = list(re.findall('^([a-zA-z]+) (imp|iff|and|or) \((.*)\)$',priority)[0])

    return decompose

def neg_rule(priority_list,proposition_atom,condition_or_conclusion):
    """
    this funtion execute the 'negation' action of proving

    >>> neg_rule(['', 'neg', 'p'],[['a','d'],['q']],0)
    [[['a', 'd'], ['q', 'p']]]
    >>> neg_rule(['', 'neg', 'p'],[['a','d'],['q']],1)
    [[['a', 'd', 'p'], ['q']]]
    >>> neg_rule(['', 'neg', 'p imp q'], [['a','d'],['q']],0)
    [[['a', 'd'], ['q', 'p imp q']]]
    >>> neg_rule(['', 'neg', 'p imp q'], [['a','d'],['q']],1)
    [[['a', 'd', 'p imp q'], ['q']]]
    """

    condition, conclusion = 0, 1
    if condition_or_conclusion == condition :
        proposition_atom[conclusion].append(priority_list[-1])
    elif condition_or_conclusion == conclusion:
        proposition_atom[condition].append(priority_list[-1])
    else:
        pass
    return [proposition_atom]

def iff_rule(priority_list,proposition_atom,condition_or_conclusion):
    """
    this funtion execute the 'if and only if' action of proving

    >>> iff_rule(['d', 'iff', 'p'],[['a'],['q']], 0)
    ([['a', 'd', 'p'], ['q']], [['a'], ['q', 'd', 'p']])
    >>> iff_rule(['d', 'iff', 'p'],[['a'], ['q']], 1)
    ([['a', 'd'], ['q', 'p']], [['a', 'p'], ['q', 'd']])
    >>> iff_rule(['d', 'iff', 'p imp q'], [['a'], ['q']], 0)
    ([['a', 'd', 'p imp q'], ['q']], [['a'], ['q', 'd', 'p imp q']])
    >>> iff_rule(['d', 'iff', 'p imp q'], [['a'], ['q']],1)
    ([['a', 'd'], ['q', 'p imp q']], [['a', 'p imp q'], ['q', 'd']])
    """
    condition, conclusion = 0, 1
    proposition_atom_1 = copy.deepcopy(proposition_atom)
    proposition_atom_2 = copy.deepcopy(proposition_atom)

    if condition_or_conclusion == condition :
        proposition_atom_1[condition].append(priority_list[0])
        proposition_atom_1[condition].append(priority_list[-1])
        proposition_atom_2[conclusion].append(priority_list[0])
        proposition_atom_2[conclusion].append(priority_list[-1])

    elif condition_or_conclusion == conclusion:
        proposition_atom_1[condition].append(priority_list[0])
        proposition_atom_1[conclusion].append(priority_list[-1])
        proposition_atom_2[condition].append(priority_list[-1])
        proposition_atom_2[conclusion].append(priority_list[0])
    else:
        pass
    return proposition_atom_1, proposition_atom_2


def imp_rule(priority_list,proposition_atom,condition_or_conclusion):
    """
    this funtion execute the 'implication' action of proving 

    >>> imp_rule(['d', 'imp', 'p'],[['a'], ['q']], 0)
    ([['a'], ['q', 'd']], [['a', 'p'], ['q']])
    >>> imp_rule(['d', 'imp', 'p'],[['a'], ['q']], 1)
    [[['a', 'd'], ['q', 'p']]]
    >>> imp_rule(['d', 'imp', 'p imp q'], [['a'], ['q']], 0)
    ([['a'], ['q', 'd']], [['a', 'p imp q'], ['q']])
    >>> imp_rule(['d', 'imp', 'p imp q'], [['a'], ['q']],1)
    [[['a', 'd'], ['q', 'p imp q']]]
    """

    condition, conclusion = 0, 1

    if condition_or_conclusion == condition :

        proposition_atom_1 = copy.deepcopy(proposition_atom)
        proposition_atom_2 = copy.deepcopy(proposition_atom)

        proposition_atom_1[conclusion].append(priority_list[0])
        proposition_atom_2[condition].append(priority_list[-1])

        return proposition_atom_1, proposition_atom_2
    elif condition_or_conclusion == conclusion:
        
        proposition_atom[condition].append(priority_list[0])
        proposition_atom[conclusion].append(priority_list[-1])

        return [proposition_atom]
    else:
        return [proposition_atom]

def and_rule(priority_list,proposition_atom,condition_or_conclusion):
    """
    this funtion execute the 'and' action of proving 

    >>> and_rule(['d', 'and', 'p'],[['a'], ['q']], 0)
    [[['a', 'd', 'p'], ['q']]]
    >>> and_rule(['d', 'and', 'p'],[['a'], ['q']], 1)
    ([['a'], ['q', 'd']], [['a'], ['q', 'p']])
    >>> and_rule(['d', 'and', 'p imp q'], [['a'], ['q']], 0)
    [[['a', 'd', 'p imp q'], ['q']]]
    >>> and_rule(['d', 'and', 'p imp q'], [['a'], ['q']],1)
    ([['a'], ['q', 'd']], [['a'], ['q', 'p imp q']])
    """

    condition, conclusion = 0, 1

    if condition_or_conclusion == condition :
        proposition_atom[condition].append(priority_list[0])
        proposition_atom[condition].append(priority_list[-1])
        return [proposition_atom]

    elif condition_or_conclusion == conclusion:
        proposition_atom_1 = copy.deepcopy(proposition_atom)
        proposition_atom_2 = copy.deepcopy(proposition_atom)

        proposition_atom_1[conclusion].append(priority_list[0])
        proposition_atom_2[conclusion].append(priority_list[-1])

        return proposition_atom_1, proposition_atom_2
    else:
        return [proposition_atom]
    

def or_rule(priority_list,proposition_atom,condition_or_conclusion):
    """
    this funtion execute the 'or' action of proving

    >>> or_rule(['d', 'or', 'p'],[['a'], ['q']], 0)
    ([['a', 'd'], ['q']], [['a', 'p'], ['q']])
    >>> or_rule(['d', 'or', 'p'],[['a'], ['q']], 1)
    [[['a'], ['q', 'd', 'p']]]
    >>> or_rule(['d', 'or', 'p imp q'], [['a'], ['q']], 0)
    ([['a', 'd'], ['q']], [['a', 'p imp q'], ['q']])
    >>> or_rule(['d', 'or', 'p imp q'], [['a'], ['q']],1)
    [[['a'], ['q', 'd', 'p imp q']]]
    """

    condition, conclusion = 0, 1

    if condition_or_conclusion == condition :

        proposition_atom_1 = copy.deepcopy(proposition_atom)
        proposition_atom_2 = copy.deepcopy(proposition_atom)

        proposition_atom_1[condition].append(priority_list[0])
        proposition_atom_2[condition].append(priority_list[-1])

        return proposition_atom_1, proposition_atom_2
    elif condition_or_conclusion == conclusion:
        
        proposition_atom[conclusion].append(priority_list[0])
        proposition_atom[conclusion].append(priority_list[-1])

        return [proposition_atom]
    else:
        return [proposition_atom]


def backforward_search(proposition):
    """
    this fuchtion can find the necessary condition of proposition

    >>> backforward_search([[], ['(neg p) or p']])
    [[[], ['neg p', 'p']]]
    >>> backforward_search([[], ['neg p', 'p']])
    [[['p'], ['p']]]
    >>> backforward_search([['p'], ['p']])
    [[['p'], ['p']]]
    >>> backforward_search([['neg(p or q)'], ['neg p']])
    [[[], ['neg p', 'p or q']]]
    >>> backforward_search([[], ['neg p', 'p or q']])
    [[['p'], ['p or q']]]
    >>> backforward_search([['p'], ['p or q']])
    [[['p'], ['p', 'q']]]
    >>> backforward_search([['p'], ['q imp p']])
    [[['p', 'q'], ['p']]]
    >>> backforward_search([['p', 'q'], ['p']])
    [[['p', 'q'], ['p']]]
    >>> backforward_search([['p iff q'], ['(q imp p) imp (p iff r)']])
    [[['p iff q', 'q imp p'], ['p iff r']]]
    >>> backforward_search([['p iff q', 'q imp p'], ['p iff r']])
    [[['q imp p', 'p', 'q'], ['p iff r']], [['q imp p'], ['p iff r', 'p', 'q']]]
    >>> backforward_search([['p iff q'],['(p and q) or ((neg p) and (neg q))']])
    [[['p iff q'], ['p and q', '(neg p) and (neg q)']]]
    >>> backforward_search([['p iff q'], ['p and q', '(neg p) and (neg q)']])
    [[['p iff q'], ['p and q', 'neg p']], [['p iff q'], ['p and q', 'neg q']]]
    >>> backforward_search([['p iff q'], ['p and q', 'neg p']])
    [[['p', 'q'], ['p and q', 'neg p']], [[], ['p and q', 'neg p', 'p', 'q']]]
    """
    condition,conclusion = 0,1

    proposition_1 = copy.deepcopy(proposition)
    proposition_2 = copy.deepcopy(proposition)
    proposition_equal_condition,condition_priority = find_priority(proposition_1, condition)
    proposition_equal_conclusion,conclusion_priority = find_priority(proposition_2, conclusion)

    dir_action_prority = {
        'neg' : neg_rule,
        'imp' : imp_rule,
        'iff' : iff_rule,
        'and' : and_rule,
        'or'  : or_rule
    }
    if condition_priority != False:
        # function of degrade the condition '[['(p imp q) imp (neg c)'],['q imp c']]'
        # priority_list = degrade_priority(condition_priority,condition)
        priority_list = degrade_priority(condition_priority)
        # function for transforming
        degraded_proposition = dir_action_prority[priority_list[1]](priority_list,proposition_equal_condition,condition)
        # print(proposition_equal_condition,condition_priority)
        # return priority_list 
    elif conclusion_priority != False:
        # function of degrade the conclusion '[['p imp q'],['(p imp q) imp (neg c)']]'
        # priority_list = degrade_priority(conclusion_priority,conclusion)
        priority_list = degrade_priority(conclusion_priority)
        # print(priority_list)
        # function for transforming
        degraded_proposition = dir_action_prority[priority_list[1]](priority_list,proposition_equal_conclusion,conclusion)
        # print(proposition_equal_conclusion,conclusion_priority)
        # return priority_list
    else:
        # function of degrade the formular like '[['p imp q'],['q imp c']]'
        # print('dd')
        proposition_1 = copy.deepcopy(proposition)
        proposition_2 = copy.deepcopy(proposition)
        proposition_equal_condition,condition_priority = find_formulae(proposition_1,condition)
        proposition_equal_conclusion,conclusion_priority = find_formulae(proposition_2,conclusion)
        # print(proposition)
        # print(proposition_equal_condition,condition_priority)
        if condition_priority != False :
            #degrade the formulae
            priority_list = degrade(condition_priority)
            # function for transforming
            degraded_proposition = dir_action_prority[priority_list[1]](priority_list,proposition_equal_condition,condition)
        elif conclusion_priority != False :
            #degrade the formulae
            priority_list = degrade(conclusion_priority)
            # function for transforming
            degraded_proposition = dir_action_prority[priority_list[1]](priority_list,proposition_equal_conclusion,conclusion)
        else :
            tmp = []
            tmp.append(proposition)
            return tmp
        
    # return priority_list
    if type(degraded_proposition) == type((1,2,3)):
        return list(degraded_proposition)
    else:
        # tmp = [].append(proposition)
        return degraded_proposition

def truth(atom):
    """
    this function can obtain the truth value of the atom formulae

    >>> truth([['p'], ['p']])
    True
    >>> truth([['p'], ['p','q']])
    True
    >>> truth([['p'], ['c']])
    False
    >>> truth([['p'], ['p', 'p', 'c']])
    True
    >>> truth([[], []])
    True
    >>> truth([[], ['p']])
    False
    >>> truth([['p'], []])
    False
    """
    if len(atom[0]) == 0 and len(atom[1]) == 0:
        return True 
    else:
        sets_condition = set(atom[0])
        sets_conclusion = set(atom[1])
        if len(set.intersection(sets_condition,sets_conclusion)) != 0:
            return True
        else:
            return False


def evaluation(basic_formulars):
    """
    this function can evaluate sets of atom formulars
    >>> evaluation([[['p'], ['p']], [['p'], ['p','q']], [['p'], ['p','a']]])
    True
    >>> evaluation([[['p'], ['p','q']], [[],[]]])
    True
    >>> evaluation([[['p'], ['c']],[['p'], ['p','q']], [['p'], ['p','a']]])
    False
    >>> evaluation([[['p'], ['p', 'p', 'c']]])
    True
    >>> evaluation([[[], []],[[],[]],[[],[]]])
    True
    >>> evaluation([[[], ['p']]])
    False
    >>> evaluation([[['p'], []]])
    False
    """
    bool_value = True
    for basic_formular in basic_formulars:
        bool_value = truth(basic_formular) and bool_value
    return bool_value

def step_format(step):
    """
    """
    condition = '['+', '.join(step[0]) +']'
    conclusion = '['+', '.join(step[1]) +']'

    return condition + ' seq ' + conclusion


def print_process_proving(proving_process):
    """
    print the process of proving
    """
    steps = copy.deepcopy(proving_process)
    steps.reverse()
    for step in steps:
        print(step_format(step))
    return


def main():
    
    argv = parserArgument()

    if len(argv.proposition) != 1:
        unproved_proposition = ' '.join(argv.proposition)
    else:
        unproved_proposition = argv.proposition[0]

    print('the proposition is {}\n'.format(unproved_proposition))

    form_prop = split_proposition(unproved_proposition)
    # print(form_prop)

    # print(check_R)
    fifo = deque([form_prop])
    extended_list = []              # degraded proposition
    print_process = []              # the process of proving
    atom_proposition = []           # the basic formula that can prove the value of the whole proposition

    while len(fifo) > 0:
        propsiton_undegraded = fifo.popleft()
        # L_or_R,model,propsiton_undegraded = find_priority(propsiton_undegraded)
        propsiton_degraded = backforward_search(propsiton_undegraded)

        extended_list.append(propsiton_undegraded)
        one_step_process =  [propsiton_undegraded]
        # print_process[tuple(propsiton_undegraded)] = tuple(propsiton_degraded)

        for i in range(len(propsiton_degraded)): 
            # one_step_process.append(propsiton_degraded[i])
            if propsiton_undegraded == propsiton_degraded[0]:
                atom_proposition.append(propsiton_undegraded)
                continue
            else:
                one_step_process.append(propsiton_degraded[i])
                fifo.append(propsiton_degraded[i])
        print_process.append(one_step_process)


    print("this proposition is {}\n".format(evaluation(atom_proposition)))
    # print(evaluation(atom_proposition))

    print("the total stages of proving:")
    print_process_proving(extended_list)
    print()
    # print_process.reverse()

    # print("the single process of proving:")
    # for i in print_process :
    #     print_process_proving(i)
    #     print('\n')
    # print(extended_list)
    # print(print_process)
    # print(atom_proposition)

        # print_process.append(one_step_process)



def test():
#     m = [['neg(p or q)'],['neg p']]
#     n = [[], ['neg p', 'p or q']]
#     l = [['neg((p or q) imp (neg c))'],['neg p']]
#     L = [[], ['neg p', 'neg(p or q)']]
#     result = backforward_search(m)
    result = backforward_search([['p'], ['q']])

    print(result)

    return

if __name__ == '__main__':
    main()
    # test()
    # import doctest
    # doctest.testmod()

