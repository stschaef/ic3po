# ------------------------------------------
# IC3PO: IC3 for Proving Protocol Properties
# ------------------------------------------
# Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. 
# All rights reserved.
#
# Author: Aman Goel (amangoel@umich.edu), University of Michigan
# ------------------------------------------

from __future__ import print_function
from cStringIO import StringIO # Python3 use: from io import StringIO

import sys
import os
import subprocess
import pysmt
import utils

import repycudd


from utils import *
from problem import *
from vmt_parser import TransitionSystem
from pysmt.environment import get_env
from pysmt.shortcuts import Solver, QuantifierEliminator, Enum
from pysmt.logics import BOOL
from pysmt.solvers.bdd import BddConverter
from _pytest.compat import enum

from ic3po import *
import common

outFile = "out"
outF = None
def fprint(s):
    global outF
    outF.write(s + "\n")

class FR(object):
    def __init__(self, system):
        self.system = system
        self.stat = dict()
        self.time_stat = dict()
        self.query_stat = dict()
        self.init_stats()
        self.qf_fallback_timeout = 0
        self.reset()
        self.debug = False
        self.ordered = "none"
        self.quorums = "none"
        self.random = common.gopts.random
        self.qf = common.gopts.qf
        self.verbose = common.gopts.verbosity
        self.cache_qf = dict()
        self.cache_qu = dict()
        self.eval_wires = False
        self._prop_formula = TRUE()
        self._prop_formula_orig = TRUE()
        self._axiom_formula = TRUE()
        self._init_formula = TRUE()
        self._init_formula_orig = TRUE()
        self._trel_formula = TRUE()
        self.boost_ordered_en = False
        self.boost_quorums_en = False
        self.globalEnum = set()
        self.framesolver = []
        self.exp = False
    
    def set_stat(self, name, value):
        self.stat[name] = value

    def init_solver(self):
        self.solver = Solver(name="z3")
        # return solver

    def reset(self):
        # self.qesolver = QuantifierEliminator(name='z3')
        # self.qesolver = QuantifierEliminator(name='z3')
        self._faxioms = []
        self._axiom_formula = TRUE()
        get_env().fsubstituter.freset()
        self.inferences = []
    
    def new_solver(self):
        s = self.init_solver()
        formulae = []
        formulae.append(axiom_formula(self))
        formulae.append(trel_formula(self))
#         formulae = self.get_formulae(formulae, True)
        formulae = self.get_formulae(formulae)
        assert_permanent(s, formulae)
        return s
    
    def get_qf_form(self, f):
        # qf = self.qesolver.eliminate_quantifiers(f).simplify()
#         print("quantified: \n%s", f.serialize())
#         print("quantifier-free: \n%s", qf.serialize())
        return pysmt.shortcuts.qelim(f)
    
    def get_formulae(self, formula, qf=True):
        formulae = formula
        if not isinstance(formulae, list):
            formulae = [formula]
        if qf:
            push_time()
            q_formula = And(formulae)
            qf = self.get_formula_qf(q_formula)
            qf_formulae = flatten_cube(qf)
            return qf_formulae
        return formulae

    def print_fullsorts(self, fullsorts):
        pass;
        # if len(fullsorts) != 0:
        #     print("(fullsorts)")
        #     for enumsort, qvar in fullsorts:
        #         print("\t%s -> %s" % (str(enumsort), pretty_print_set(qvar)))

    def add_init_frame(self):
        assert(len(self.frames) == 0)
        cubes = set()
        fs = self.new_solver()
        cubes.add(Not(init_formula(self)))
        formula = init_formula(self)
        fs.add_assertion(formula)
        self.frames.append(cubes)
        self.framesolver.append(fs)
        self.frame_summary()
    
    def add_frame(self):
        # print(time_str(), "\nAdding frame %d..." % (len(self.frames)))
        fs = self.new_solver()
        fs.add_assertion(prop_formula(self))
        self.frames.append(set())
        self.framesolver.append(fs)
        if common.gopts.verbosity == 0:
            return
        # print("\n", file=sys.stderr, end="")

    def get_framesolver(self, fin):
        i = fin
        if (i == -1):
            i = len(self.frames) - 1
        
        assert(i < len(self.framesolver))
        return self.framesolver[i]

    def propagate_eq(self, cubeSet, antecedent, ivars, qvars, fullsorts):
        eqMap = dict()
        tmpSet = set()
#         incompleteSorts = set()
        for c in cubeSet:
            if c.node_type() == op.EQUALS:
                lhs = c.arg(0)
                rhs = c.arg(1)
                if (not rhs.is_symbol()) or (lhs in qvars):
                    lhs, rhs = rhs, lhs
#                 print("lhs ", lhs)
#                 print("rhs ", rhs)
                if rhs.is_symbol and rhs in qvars:
                    if (common.gopts.const > 1) or (not lhs.is_function_application()):
                        rhst = rhs.symbol_type()
                        if rhst.is_enum_type() and rhs not in eqMap:
                            eqMap[rhs] = lhs
                            qvars.discard(rhs)
#                             print("add1 %s -> %s" % (rhs, lhs))
#                             incompleteSorts.add(rhst)
                            continue
                        elif rhs in ivars and rhs not in eqMap:
                            eqMap[rhs] = lhs
                            qvars.discard(rhs)
#                             print("add2 %s -> %s" % (rhs, lhs))
                            continue
                        
            tmpSet.add(c)
         
        if len(eqMap) != 0:
            changed = True
            while changed:
                changed = False
                for l, r in eqMap.items():
                    rNew = r.simple_substitute(eqMap)
                    if (rNew != r):
                        changed = True
                    eqMap[l] = rNew
            
            # print("(eq map)")
            # for l, r in eqMap.items():
            #     print("\t%s -> %s" % (pretty_serialize(l), pretty_serialize(r)))
            
            cubeSetNew = set()
            for c in tmpSet:
                c_new = c.simple_substitute(eqMap)
                cubeSetNew.add(c_new)
                
            antecedentNew = dict()
            for enumsort, qvar in antecedent.items():
                vNew = []
                for i in qvar:
                    i_new = i.simple_substitute(eqMap)
#                     if (i_new != i):
#                         cubeSetNew.add(i_new)
#                     else:
#                         vNew.append(i_new)
                    vNew.append(i_new)
                antecedentNew[enumsort] = vNew
            
            fullsortsNew = []
            for fs in fullsorts:
#                 if fs[0] not in incompleteSorts:
#                     fullsortsNew.append(fs)
                rhs = []
                for v in fs[1]:
                    if v in eqMap:
                        v = eqMap[v]
                    rhs.append(v)
                fullsortsNew.append([fs[0], rhs])
                
            # print("(cube eq)")
            # for c in cubeSetNew:
            #     print("\t%s" % pretty_serialize(c))
            
            # print("(qvars eq)")
            # for c in qvars:
            #     print("\t%s" % pretty_serialize(c))
            
            # print("(antecedent eq)")
            # for enumsort, qvar in antecedentNew.items():
            #     print("\t%s" % enumsort)
            #     for c in qvar:
            #         print("\t-> %s" % pretty_serialize(c))
            
            self.print_fullsorts(fullsortsNew)
            
            removedVars = set(eqMap.keys())
            for c in cubeSetNew:
                fv = c.get_free_variables()
                fv_removed = fv.intersection(removedVars)
                if len(fv_removed) != 0:
                    # print("Error: found bound variables as free in %s" % pretty_serialize(c))
                    # for c in fv_removed:
                    #     print("\t%s" % pretty_serialize(c))
                    assert(0)
            
            return eqMap, cubeSetNew, antecedentNew, fullsortsNew
        else:
            return eqMap, cubeSet, antecedent, fullsorts
        
    def propagate_eq_post(self, cube):
        cubeEq = cube

        qvars = set()
        qvarsNew = set()
        v = cube
        if v.is_exists():
            vq = v.quantifier_vars()
            for i in vq:
                qvars.add(i)
                qvarsNew.add(i)
            v = v.args()[0]
        cubeSet = flatten_and(v)
        
        eqMap = dict()
        tmpSet = set()
        for c in cubeSet:
            if c.node_type() == op.EQUALS:
                lhs = c.arg(0)
                rhs = c.arg(1)
                if (not rhs.is_symbol()) or (lhs in qvars):
                    lhs, rhs = rhs, lhs
                if rhs.is_symbol and rhs in qvars:
                    if rhs not in eqMap:
                        eqMap[rhs] = lhs
                        qvarsNew.discard(rhs)
                        continue
            tmpSet.add(c)
            
        if len(eqMap) != 0:
            changed = True
            while changed:
                changed = False
                for l, r in eqMap.items():
                    rNew = r.simple_substitute(eqMap)
                    if (rNew != r):
                        changed = True
                    eqMap[l] = rNew

            # print("(eq map: post)")
            # for l, r in eqMap.items():
            #     print("\t%s -> %s" % (pretty_serialize(l), pretty_serialize(r)))
            
            cubeSetNew = set()
            for c in tmpSet:
                c_new = c.simple_substitute(eqMap)
                cubeSetNew.add(c_new)
                
            # print("(cube eq: post)")
            # for c in cubeSetNew:
            #     print("\t%s" % pretty_serialize(c))
            
            # print("(qvars eq: post)")
            # for c in qvarsNew:
            #     print("\t%s" % pretty_serialize(c))
            
            removedVars = set(eqMap.keys())
            for c in cubeSetNew:
                fv = c.get_free_variables()
                fv_removed = fv.intersection(removedVars)
                if len(fv_removed) != 0:
                    # print("Error: found bound variables as free in %s" % pretty_serialize(c))
                    # for c in fv_removed:
                    #     print("\t%s" % pretty_serialize(c))
                    assert(0)
            
            cubeEq = And(cubeSetNew)
            if len(qvarsNew) != 0:
                cubeEq = Exists(qvarsNew, cubeEq)
        return cubeEq
    
    def print_query(self, solver, fname, prefix, formulae, force):
        if force or (self.verbose > 9):
            if not isinstance(solver, pysmt.solvers.z3.Z3Solver):
                return
            fname = "%s/%s.smt2" % (common.gopts.out, fname)
            f = open(fname, "w+")
            if prefix != "":
                f.write(prefix)
    #         solver.print_query(f, formulae)
            solver.print_query(f)
            f.close()
    
    def check_query(self, solver, formulae=None, timeout=None):
        self.print_query(solver, "last", "", formulae, False)
        if timeout == None:
            timeout = self.qf_fallback_timeout
        solver.set_timeout(timeout)
        try:
            res = solver.solve() if formulae == None else solver.solve(formulae)
            self.last_solver = solver
        except SolverReturnedUnknownResultError:
            if self.qf_fallback_timeout == 0:
                self.print_query(solver, "last", "", formulae, True)
                print("Error in solver result.")
                print("Z3 reason for unknown: %s" % solver.reason_unknown())
#                 assert(0)
            bp, assertions, n = solver.export_assertions()
#             print("backtrack points #%d:\n%s" % (len(bp), bp))
#             print("assertions #%d:\n%s" % (len(assertions), assertions))
#             print("named assertions #%d:" % (len(n)))
#             for i in n:
#                 print("\t", i, " of type %s" % type(i))

#             new_solver = Solver(name="z3", logic="UF", random_seed=self.solver_seed())
            new_solver = self.init_solver(1)
            for i in assertions:
                if isinstance(i, tuple):
                    new_solver.add_assertion(i[2], i[1])
                else:
                    new_solver.add_assertion(i)
            
            if len(self.system._fin2sort) != 0:
                timeout = 0
                print("\t(trying fresh solver)")
            else:
                print("\t(trying qf)")
            new_solver.set_timeout(timeout)
            try:
                res = new_solver.solve() if formulae == None else new_solver.solve(formulae)
                self.last_solver = new_solver
                print("\t(faster)")
            except SolverReturnedUnknownResultError:
                if self.qf_fallback_timeout == 0:
                    self.print_query(new_solver, "last2", "", formulae, True)
                    print("Error in solver result (attempt #2).")
                    print("Z3 reason for unknown (attempt #2): %s" % new_solver.reason_unknown())
                    assert(0)
                print("\t(failed with timeout: %ds)" % (timeout/1000))
                timeout = 3*timeout
                return self.check_query(solver, formulae, timeout)

#                 solver.set_timeout(0)
#                 res = solver.solve() if formulae == None else solver.solve(formulae)
#                 self.last_solver = solver

#         if (len(n) > 0) and not res:
#            print("core: %s" % self.last_solver.get_unsat_core())
#            assert(0)
#         assert(0)
        return res

    def update_max_query(self, solver, name, value, infinite, core):
        name = "time-q-max" + name
        name += "-core" if core else ""
        name += "-infinite" if infinite else "-finite"
        value *= 1000
        modified = self.update_query_stat(name, value)
        if modified:
            prefix = "(set-info :time %.0fms)\n\n" % value
#             print(prefix)
            self.print_query(solver, name, prefix, None, False)

    def solve_formula(self, solver, formula, quiet=False):
        """Check whether formula is satisfiable or not"""
#         print("Formula: %s" % formula.serialize())
        self.update_stat("scalls")
        if len(self.system._sort2fin) > 0:
            self.update_stat("scalls-finite")
            if len(self.system._sort2fin) == len(self.system._sorts):
                self.update_stat("scalls-finite-full")
        else:
            self.update_stat("scalls-infinite")
        
        formulae = None
        if formula != TRUE():
            formulae = self.get_formulae(formula)
        push_time()
        res = self.check_query(solver, formulae)
        if res:
            if (not quiet):
                print("-> SAT")
            self.update_max_query(solver, "", pop_time(), len(self.system._sort2fin) == 0, False)
            return True
        else:
            if (not quiet):
                print("-> UNSAT")
            self.update_max_query(solver, "", pop_time(), len(self.system._sort2fin) == 0, False)
            return False

    def solve_with_model(self, solver, formula, dest, quiet=False):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        result = self.solve_formula(solver, formula, quiet)
        if result:
            model = self.last_solver.get_model()
#             model.print_model()
            sorts = dict()
            isorts = dict()
            if len(self.system._sort2fin) != len(self.system._sorts):
                isorts = model.get_diagram_sorts()       
#             model.get_diagram_funcs()   
            for k, v in isorts.items():
                sorts[k] = v
            for k, v in self.system._enumsorts.items():
                sorts[k] = v
#             print("\tmodel isorts: %s" % isorts)
#             print("\tmodel sorts: %s" % sorts)
            
            conditions = []
            
            for lhs, rhs in self.system.curr._predicates.items():
                assert(lhs.is_function_application())
                s = lhs.function_name()
                a = lhs.args()
                s_type = s.symbol_type()
                assert(len(s_type.param_types) <= 4)

                subs = dict()
                if (len(s_type.param_types) <= 0):
                    rhsNew = rhs.simple_substitute(subs)
                    conditions.append(self.get_predicate_value(rhsNew, model))
                else:
                    subs = {}
                    self.get_predicate_values(s, s_type, model, sorts, conditions, rhs, a, subs, 0)
#                     i_values = sorts[s_type.param_types[0]]
#                     for i in i_values:
#                         subs[a[0]] = i
#                         if (len(s_type.param_types) <= 1):
#                             rhsNew = rhs.simple_substitute(subs)
#                             conditions.append(self.get_predicate_value(rhsNew, model))
#                             continue
#                         j_values = sorts[s_type.param_types[1]]
#                         for j in j_values:
#                             subs[a[1]] = j
#                             if (len(s_type.param_types) <= 2):
#                                 rhsNew = rhs.simple_substitute(subs)
#                                 conditions.append(self.get_predicate_value(rhsNew, model))
#                                 continue
#                             k_values = sorts[s_type.param_types[2]]
#                             for k in k_values:
#                                 subs[a[2]] = k
#                                 if (len(s_type.param_types) <= 3):
#                                     rhsNew = rhs.simple_substitute(subs)
#                                     conditions.append(self.get_predicate_value(rhsNew, model))
#                                     continue
#                                 l_values = sorts[s_type.param_types[3]]
#                                 for l in l_values:
#                                     subs[a[3]] = l
#                                     rhsNew = rhs.simple_substitute(subs)
#                                     conditions.append(self.get_predicate_value(rhsNew, model))
#                                     if (len(s_type.param_types) > 3):
#                                         print("Found a case with more than 5 arguments to a symbol.")
#                                         assert(0)
#             print(conditions)
#             assert(0)

            for s in self.system.curr._states:
                if self.eval_wires:
                    if s in self.system.curr._definitionMap:
                        continue
                
#                 print("Symbol: ", s)
                s_type = s.symbol_type()

                if s_type.is_function_type():
                    args = []
                    self.get_state_values(s, s_type, model, sorts, conditions, args, 0)
#                     i_values = sorts[s_type.param_types[0]]
#                     for i in i_values:
#                         if (len(s_type.param_types) == 1):
#                             args = [i]
#                             conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 2):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 args = [i, j]
#                                 conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 3):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 k_values = sorts[s_type.param_types[2]]
#                                 for k in k_values:
#                                     args = [i, j, k]
#                                     conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 4):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 k_values = sorts[s_type.param_types[2]]
#                                 for k in k_values:
#                                     l_values = sorts[s_type.param_types[3]]
#                                     for l in l_values:
#                                         args = [i, j, k, l]
#                                         conditions.append(self.get_relation_value(s, args, model))
#                         elif (len(s_type.param_types) == 5):
#                             j_values = sorts[s_type.param_types[1]]
#                             for j in j_values:
#                                 k_values = sorts[s_type.param_types[2]]
#                                 for k in k_values:
#                                     l_values = sorts[s_type.param_types[3]]
#                                     for l in l_values:
#                                         m_values = sorts[s_type.param_types[4]]
#                                         for m in m_values:
#                                             args = [i, j, k, l, m]
#                                             conditions.append(self.get_relation_value(s, args, model))
#                         else:
#                             print("Found a case with more than 5 arguments to a symbol.")
#                             assert(0)
                else:
                    f = Function(s, [])
                    if f.is_symbol() and f in self.system.curr._globals:
                        rhs = self.get_state_value(f, model)
                        if rhs.is_enum_constant() and str(rhs.constant_type()).startswith("epoch"):
                            self.globalEnum.add(rhs)
#                             print("adding global enum: %s" % pretty_print_str(rhs))

                    eq = self.get_predicate_value(f, model)
                    if self.ordered == "zero":
                        fstr = pretty_print_str(f)
                        if fstr != "zero" and fstr != "firste":
                            conditions.append(eq)
                    else:
                        conditions.append(eq)
#             for c in conditions:
#                 print("%s" % pretty_serialize(c))
#             assert(0)

            ivars = []
            ivarMap = {}
            for s, values in isorts.items():
                for i in range(len(values)):
                    v = values[i]
                    name = "Q:" + str(s) + str(len(ivarMap))
                    qv = Symbol(name, s)
                    ivarMap[v] = qv
                    ivars.append(qv)
#                     ivars.append(v)
                    for j in range(i+1, len(values)):
                        if i != j:
                            neq = Not(EqualsOrIff(v, values[j]))
                            conditions.append(neq)
#                             print("adding to cube: %s" % str(neq))

            if len(dest) != 0:
                print("(action info)")
                inputConditions = []
                actionIdx = -1
                for idx, f in enumerate(self.system.curr._actions):
                    en = f[2]
                    enValue = self.get_state_value(en, model)
                    if (enValue == TRUE()):
                        actionIdx = idx
                        actionName = f[1]
                        print("\taction: %s" % actionName)
    #                     print("\ten: " + str(en) + " with value " + str(enValue))
                        
                        print("\tinputs:")
                        if actionName in self.system.syntax.action2inputs:
                            actionInputs = self.system.syntax.action2inputs[actionName]
                            for inp in actionInputs:
                                inpValueEnum = self.get_state_value(inp, model)
                                if self.allow_inputs_in_cube:
                                    conditions.append(EqualsOrIff(inp, inpValueEnum))
                                inpValue = inpValueEnum.simple_substitute(ivarMap)
                                print("\t\t" + pretty_print_str(inp) + " -> " + pretty_print_str(inpValue))
                                if inpValue.is_enum_constant() and str(inpValue.constant_type()).startswith("epoch"):
                                    self.globalEnum.add(inpValue)
                                
#                                 name = "Q:" + str(inp)
#                                 qv = Symbol(name, inp.symbol_type())
#                                 ivarMap[inpValueEnum] = qv
#                                 ivars.append(qv)
    
#                         self.print_global_enum()
                        conditions = self.filter_state(conditions)
                        break

            if self.random > 3:
                random.shuffle(conditions)
            cube = And(conditions)        
            
            if len(ivars) != 0:
                cube = cube.simple_substitute(ivarMap)
                cube = Exists(ivars, cube)
                
#             print("cube: %s" % cube)
#             print("cube:")
#             for c in flatten_cube(cube):
#                 print("\t%s" % pretty_serialize(c))
#             assert(0)
            
            self.update_stat("cubes")
            self.update_stat("sz-cube-sum", len(conditions))
            return cube
        else:
            return None

    def init_stats(self):
        self.set_stat("scalls", 0)
        self.set_stat("scalls-finite", 0)
        self.set_stat("scalls-infinite", 0)
        self.set_stat("scalls-finite-full", 0)
        self.set_stat("cti", 0)
        self.set_stat("cubes", 0)
        self.set_stat("subsumed-calls", 0)
        self.set_stat("subsumed-subset", 0)
        self.set_stat("subsumed-varintersect-c", 0)
        self.set_stat("subsumed-varintersect-e", 0)
        self.set_stat("subsumed-query-sat", 0)
        self.set_stat("subsumed-query-unsat", 0)
        self.set_stat("subsumed-eq", 0)
        self.set_stat("unsat-core", 0)
        self.set_stat("sz-unsat-core-sum", 0)
        self.set_stat("sz-unsat-min-sum", 0)
        self.set_stat("sz-cube-sum", 0)
        self.set_stat("antecedent-reduction-sum", 0)
        self.set_stat("antecedent-total-sum", 0)
        self.set_stat("antecedent-calls", 0)
        self.set_stat("antecedent-calls-reduced", 0)
        self.set_stat("antecedent-scalls", 0)
        self.init_time_stats()

    def init_time_stats(self):
        self.set_time_stat("time-cti-bad-sat", 0)
        self.set_time_stat("time-cti-bad-unsat", 0)
        self.set_time_stat("time-cti-sat", 0)
        self.set_time_stat("time-cti-unsat", 0)
        self.set_time_stat("time-forward", 0)
        self.set_time_stat("time-antecedent", 0)
        self.set_time_stat("time-subsume", 0)
        self.set_time_stat("time-subsume-query", 0)
        self.set_time_stat("time-inv-check-finite", 0)
        self.set_time_stat("time-inv-check-infinite", 0)
        self.set_time_stat("time-inv-reuse", 0)
        self.set_time_stat("time-minimize", 0)
        self.set_time_stat("time-qf", 0)
        self.init_query_stats()
        
    def init_query_stats(self):
        self.set_query_stat("time-q-max-finite", 0)
        self.set_query_stat("time-q-max-finite-core", 0)
        self.set_query_stat("time-q-max-infinite", 0)
        self.set_query_stat("time-q-max-infinite-core", 0)

    def set_time_stat(self, name, value):
        self.time_stat[name] = value

    def set_query_stat(self, name, value):
        self.query_stat[name] = value

    def update_stat(self, name, value=1):
        assert name in self.stat
        self.stat[name] += value

    def update_time_stat(self, name, value=1):
        assert name in self.time_stat
        self.time_stat[name] += value

    def update_query_stat(self, name, value=1):
        assert name in self.query_stat
        if self.query_stat[name] < value:
            self.query_stat[name] = value
            return True
        return False

    def get_formula_qf(self, formula):
        if self.qf >= 2:
            if (len(self.system._fin2sort) == 0 
#                 and len(self.system._sort2fin) == len(self.system._sorts)
                ):
                if formula in self.cache_qf:
                    return self.cache_qf[formula]

                qvars = formula.get_quantifier_variables()
                if len(qvars) == 0:
                    return formula
                
                noScalarVar = True
                for v in qvars:
                    if v.symbol_type().is_enum_type():
                        noScalarVar = False
                        break
                if noScalarVar:
                    return formula
                
#                 print("QE: %s" % formula.serialize())
                
                push_time()
                # q_formula = And(formula)
                qf_formula = self.get_qf_form(formula)
                self.update_time_stat("time-qf", pop_time())
                
#                 for f in flatten(qf_formula):
#                     print("--- %s" % f.serialize())
#                 assert(0)

#                 print("Adding QF entry: ", end='')
#                 pretty_print(formula)
#                 pretty_print(qf_formula)
        
                self.cache_qf[formula] = qf_formula
                self.cache_qu[qf_formula] = formula
                return qf_formula
#         else:
#             formula_flat = self.system.replaceDefinitions(formula)
#             self.cache_qu[formula_flat] = formula
#             return formula_flat
        return formula
    
    def get_bdd(self, node):
        bdd_expr = self.converter.convert(node)
        return bdd_expr
    
    def get_symmetric(self, cl, pol=True):
        cube = cl
        if pol:
            cube = Not(cube)
        cubesOut = symmetry_cube(self, cube, 0, False)
        if pol:
            cubesOutNew = set()
            for cubeSym, complex in cubesOut:
                cubeSymNew = Not(cubeSym)
                cubesOutNew.add((cubeSymNew, complex))
            cubesOut = cubesOutNew
        return cubesOut

    def get_state_value(self, f, model):
#         print("val: %s" % (f))
        return model.get_value(f)

    def get_predicate_value(self, f, model):
        value = self.get_state_value(f, model)
#         print("%s -> %s" % (f, value))
        eq = EqualsOrIff(f, value)
        return eq
    
    def get_relation_value(self, s, args, model):
        f = Function(s, args)
        value = self.get_state_value(f, model)
        if self.quorums == "symmetric" and self.system.is_quorum_symbol(s):
            assert(value == TRUE() or value == FALSE())
            return TRUE()
        if self.ordered == "partial" and self.system.curr.is_ordered_state(s):
            assert(value == TRUE() or value == FALSE())
            return TRUE()
        if self.ordered == "zero" and self.system.curr.is_ordered_state(s):
            assert(value == TRUE() or value == FALSE())
            ev = f.get_enum_constants()
            allSet = True
            for v in ev:
                vstr = pretty_print_str(v)
                if vstr != "e0" and vstr != "e1":
                    allSet = False
                    break
            if allSet:
                return TRUE()
#             if (value == TRUE()):
#                 return TRUE()
#         if str(s).startswith("member:"):
#             assert(value == TRUE() or value == FALSE())
#             if (value == FALSE()):
#                 return TRUE()
#         return self.get_predicate_value(f, model)
#         print("%s -> %s" % (f, value))
        eq = EqualsOrIff(f, value)
        return eq

    def get_state_values(self, s, s_type, model, sorts, conditions, args, idx):
        if (idx == len(s_type.param_types)):
            conditions.append(self.get_relation_value(s, args, model))
        else:
            i_values = sorts[s_type.param_types[idx]]
            for i in i_values:
                args.append(i)
                self.get_state_values(s, s_type, model, sorts, conditions, args, idx+1)
                args.pop()
    
    def get_predicate_values(self, s, s_type, model, sorts, conditions, rhs, a, subs, idx):
        if (idx == len(s_type.param_types)):
            rhsNew = rhs.simple_substitute(subs)
            conditions.append(self.get_predicate_value(rhsNew, model))
        else:
            i_values = sorts[s_type.param_types[idx]]
            for i in i_values:
                subs[a[idx]] = i
                self.get_predicate_values(s, s_type, model, sorts, conditions, rhs, a, subs, idx+1)
                del subs[a[idx]]
    
    def get_formula_qu(self, formula):
        if self.qf >= 2:
            if (len(self.system._fin2sort) == 0 
#                 and len(self.system._sort2fin) == len(self.system._sorts)
                ):
#                 if formula.has_quantifier_variables():
#                     print("Formula has quantifiers: %s" % formula)
#                     assert(0)
                if formula in self.cache_qu:
                    return self.cache_qu[formula]
                else:
                    not_formula = Not(formula)
                    if not_formula in self.cache_qu:
                        return Not(self.cache_qu[not_formula])
#                     else:
#                         print("Formula not found: %s" % formula)
#                         assert(0)
#         else:
#             if formula in self.cache_qu:
#                 return self.cache_qu[formula]
#             else:
#                 not_formula = Not(formula)
#                 if not_formula in self.cache_qu:
#                     return Not(self.cache_qu[not_formula])          
        return formula
    
    def get_formula_qf(self, formula):
        if self.qf >= 2:
            if (len(self.system._fin2sort) == 0 
#                 and len(self.system._sort2fin) == len(self.system._sorts)
                ):
                if formula in self.cache_qf:
                    return self.cache_qf[formula]

                qvars = formula.get_quantifier_variables()
                if len(qvars) == 0:
                    return formula
                
                noScalarVar = True
                for v in qvars:
                    if v.symbol_type().is_enum_type():
                        noScalarVar = False
                        break
                if noScalarVar:
                    return formula
                
#                 print("QE: %s" % formula.serialize())
                
                push_time()
                q_formula = And(formula)
                qf_formula = self.get_qf_form(q_formula)
                self.update_time_stat("time-qf", pop_time())
                
#                 for f in flatten(qf_formula):
#                     print("--- %s" % f.serialize())
#                 assert(0)

#                 print("Adding QF entry: ", end='')
#                 pretty_print(formula)
#                 pretty_print(qf_formula)
        
                self.cache_qf[formula] = qf_formula
                self.cache_qu[qf_formula] = formula
                return qf_formula
#         else:
#             formula_flat = self.system.replaceDefinitions(formula)
#             self.cache_qu[formula_flat] = formula
#             return formula_flat
        return formula
    
    def get_formulae_qf(self, formula):
        formulae = formula
        if self.qf >= 2:
            if len(self.system._fin2sort) == 0:
                push_time()
                print("qf for query type: %s" % self.qtype)
                q_formula = And(formulae)
                qf_formula = self.get_qf_form(q_formula)
                qf_formulae = flatten_cube(qf_formula)
                self.update_time_stat("time-qf", pop_time())
                return qf_formulae
#             formulae.append(axiom_formula(self))
#                 fformulae = []
#                 for f in formulae:
#                     fformulae.append(f)
#                     if self._print:
#                         print("--- %s" % f.serialize())
#                         print("------ vars: %s" % f.get_free_variables())
#                 formulae = fformulae
        return formulae
        
    def build_actions(self):
        self.actions = {}
        for f in self.system.curr._actions:
            action = f[0]
            name = f[1]
            if self.system.curr.is_noop(name):
                continue
            eprint(time_str(), "(building bdd for %s)" % name)
            print(time_str(), "(building bdds for %s)" % name)
            if name not in self.actions:
                self.actions[name] = []
            if action.is_exists():
                instances = self.converter._get_children(action)
                queue = []
                for i in instances:
                    bddi = self.converter.convert(i)
                    queue.append(bddi)

                all_vars = set(self.converter.var2node.keys())
                pnabstract = all_vars.difference(self.pvars)
                pnabstract = pnabstract.difference(self.nvars)
                projAll = self.converter.cube_from_var_list(pnabstract)
                for bddq in queue:
#                     bddq = self.ddmanager.ExistAbstract(bddq, projAll)
                    self.actions[name].append(bddq)
                print("\t\tfound #%d bdd instances for %s)" % (len(queue), name))
#                 if name == "ext:grant":
#                     for bdd in self.actions[name]:
#                         self.dump_dot(bdd)
#                         assert(0)
            else:
                q = self.converter.convert(action)
                self.actions[name] = [q]
        
    def build_axioms(self):
        self.axiom = self.converter.typeok
        if axiom_formula(self) != TRUE():
            bddA = self.formula2bdd(axiom_formula(self))
            self.axiom = self.ddmanager.And(self.axiom, bddA)
        
    def formula2bdd(self, formula, quiet=True):
        f = And(self.get_formulae(formula, False))
        return self.get_bdd(f)

    def set_atoms(self):
        self.patoms = {}
        self.natoms = {}
        self.p2natoms = {}
        formulae = []
        formulae.append(init_formula(self))
        formulae.append(trel_formula(self))
        formulae.append(axiom_formula(self))
        formulae.append(prop_formula(self))
        
        formula = And(formulae)
        formula = And(self.get_formulae(formula))
#         atoms = formula.get_atoms()
        atoms = self.converter.atom2var.keys()
        for p in atoms:
            vars = p.get_free_variables()
            ovars = vars.difference(self.system.curr._states)
            if len(ovars) == 0:
#             nvars = vars.intersection(self.system.curr._nex2pre.keys())
#             if len(nvars) == 0:
                bddp = self.get_bdd(p)
                self.patoms[p] = bddp
                # print("adding pre: %s with bdd %s" % (p, bddp.NodeReadIndex()))
                n = pre2nex(self, p)
                bddn = bddp
                if n != p:
                    bddn = self.get_bdd(n)
                self.natoms[n] = bddn
#                 print("adding nex: %s with bdd %s" % (n, bddn))
    
    def add_bddSupport(self, bdd, support):
        ps = self.ddmanager.Support(bdd)
        psA = repycudd.IntArray(self.converter.numvars)
        self.ddmanager.BddToCubeArray(ps, psA)
        for i in range(len(psA)):
            if psA[i] == 0 or psA[i] == 1:
                var = self.converter.idx2var[i]
                support.add(var)
        
    def set_bddvars(self):
        self.pvars = set()
        self.nvars = set()
        # eprint("\t(#%d variables)" % self.converter.numvars)
        # print("\t(#%d variables)" % self.converter.numvars)
        for p in self.patoms:
            self.pvars.add(self.converter.atom2var[p])
#             bdd = self.patoms[p]
#             self.add_bddSupport(bdd, self.pvars)
        for n in self.natoms:
            self.nvars.add(self.converter.atom2var[n])
#             bdd = self.natoms[n]
#             self.add_bddSupport(bdd, self.nvars)
#         print("pvars: %s" % self.pvars)
#         print("nvars: %s" % self.nvars)
        
    def set_p2nVars(self):
        self.p2nvars = {}
        for p in self.patoms:
            n = pre2nex(self, p)
            if n != p:
                pvar = self.converter.atom2var[p]
                nvar = self.converter.atom2var[n]
                self.p2nvars[pvar] = nvar
        pv = set(self.p2nvars.keys())
        nv = set(self.p2nvars.values())
        diff = pv.intersection(nv)
        if len(diff) != 0:
            print(diff)
            assert(0)
    
    def header_espresso(self):
        self.espresso_in = []
        res = ""
        for idx, var in self.converter.idx2var.items():
            if var in self.converter.var2atom:
                atom = self.converter.var2atom[var]
                self.espresso_in.append(atom)
                res += str(atom).replace(" ", "") + " "
            else:
                atom = Symbol("v%d" % idx)
                self.espresso_in.append(atom)
                res += str(atom) + " "
                print("Found ")
                assert(0)
        return res

    def print_espresso(self, bdd, restricted, name):
        global outF
        outF =open(name + ".pla", "w")
        
        str_head = ".ilb "
        self.espresso_head = []
        abvars = set(self.converter.var2atom.keys())
        atomList = []
        for idx in range(self.numvars):
            var = self.converter.idx2var[idx]
            atom = self.converter.var2atom[var]
            atomList.append(atom)
            if atom in restricted:
                self.espresso_head.append(atom)
                abvars.remove(var)
        
        for atom in self.espresso_head:
            str_head += pretty_serialize(atom).replace(" ", "") + " "
        fprint(".i %d" % len(self.espresso_head))
        fprint(".o 1")
        fprint(str_head)
        fprint(".ob out")
        fprint(".phase 0")
        abcube = self.converter.cube_from_var_list(list(abvars))
#         bddnew = bdd
        bddnew = self.ddmanager.ExistAbstract(bdd, abcube)
        print("\t(printing pla)")
        for cube_tup in repycudd.ForeachCubeIterator(self.ddmanager, bddnew):
            str_cube = ""
            for idx, char in enumerate(cube_tup):
                if idx >= self.numvars:
                    break
                atom = atomList[idx]
#                 var = self.converter.idx2var[idx]
#                 atom = self.converter.var2atom[var]
                if atom in restricted:
                    if char == 2:
                        str_cube += '-'
                    else:
                        str_cube += str(char)
            str_cube += " 1"
            fprint(str_cube)
        fprint(".e")
        outF.close()
    
    def execute_espresso(self, bdd, restricted, mode="exact"):
        global outF
        name = "%s/espresso_in" % (common.gopts.out)
        self.print_espresso(bdd, restricted, name)
        cmd = "exec espresso"
        if mode == "exact":
            cmd += " -D exact -o kiss %s.pla" % name
            eprint("\t(running espresso in exact mode)")
            print("\t(running espresso in exact mode)")
        elif mode == "primes":
            cmd += " -D primes -o kiss %s.pla" % name
            eprint("\t(running espresso in primes mode)")
            print("\t(running espresso in primes mode)")
        else:
            cmd += " -e fast -o kiss %s.pla" % name
            eprint("\t(running espresso in fast mode)")
            print("\t(running espresso in fast mode)")
        print(cmd)
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, shell=True)
        (out, err) = proc.communicate()
        
        if err != None:
            print("espresso err: %s" % err)
            assert(0)
        output = out.split(b'\n')
        newCubes = []
        outName = "%s/" % (common.gopts.out)
        if mode == "exact":
            outName += "espresso_out_exact.pla"
        elif mode == "primes":
            outName += "espresso_out_primes.pla"
        else:
            outName += "espresso_out_fast.pla"
        outF =open(outName, "w")
        str_head = ".ilb "
        for atom in self.espresso_head:
            str_head += pretty_serialize(atom).replace(" ", "") + " "
        fprint(".i %d" % len(self.espresso_head))
        fprint(".o 1")
        fprint(str_head)
        fprint(".ob out")
        for l in output:
            if l != "":
                fprint(l)
                cube = []
                cubeMap = {}
                for i in range(len(self.espresso_head)):
                    atom = self.espresso_head[i]
                    val = l[i]
                    if val == "0":
                        cubeMap[atom] = 0
                        cube.append(Not(atom))
                    elif val == "1":
                        cubeMap[atom] = 1
                        cube.append(atom)
                newCubes.append((And(cube), cubeMap, l))
#                 print("%s -> %s" % (l, And(cube)))
        fprint(".e")
        outF.close()
        if len(newCubes) == 0:
            print("No cube in espresso output.")
            print("Something went wrong with espresso (probably memout).")
            assert(0)
        
        return newCubes
    
    def bdd2atoms(self, bdd, atomset=None):
        psA = repycudd.IntArray(self.converter.numvars)
        self.ddmanager.BddToCubeArray(bdd, psA)
        atoms = []
        atomval = {}
        for i in range(len(psA)):
            if psA[i] == 0 or psA[i] == 1:
                var = self.converter.idx2var[i]
                if var in self.converter.var2atom:
                    atom = self.converter.var2atom[var]
#                     print("%d -> %s" % (i, atom))
                    if atomset != None and atom not in atomset:
                        continue
                    if psA[i] == 0:
                        atomval[atom] = 0
                        atom = Not(atom)
                    else:
                        atomval[atom] = 1
                    atoms.append(atom)
        return (And(atoms), atomval)
    
    def extract_pcubes(self, bdd, prefix="Cube"):
        cubes = self.extract_cubes(bdd, self.patoms)
        print("\n %s: #%d \n" % (prefix, len(cubes)))
        if len(cubes) < 500:
            for cube, cubeMap in cubes:
                print(cube)
        return cubes
    
    def extract_ncubes(self, bdd, prefix="Cube"):
        cubes = self.extract_cubes(bdd, self.natoms)
        print("%s: #%d" % (prefix, len(cubes)))
        if len(cubes) < 100:
            for cube, cubeMap in cubes:
                print(cube)
        return cubes
    
    def extract_cubes(self, bdd, allowed):
        cubes = []
        for cube in repycudd.ForeachCubeIterator(self.ddmanager, bdd):
            atoms = []
            atomval = {}
            for i in range(self.numvars):
                lit = cube[i]
                if lit == 0 or lit == 1:
                    var = self.converter.idx2var[i]
                    if var in self.converter.var2atom:
                        atom = self.converter.var2atom[var]
    #                     print("%d -> %s" % (i, atom))
                        if atom not in allowed:
                            continue
                        if lit == 0:
                            atomval[atom] = 0
                            atom = Not(atom)
                        else:
                            atomval[atom] = 1
                        atoms.append(atom)
            cubeNew = (And(atoms), atomval)
            cubes.append(cubeNew)
        return cubes
    
    def dump_dot(self, bdd):
        add = self.ddmanager.BddToAdd(bdd)
        self.ddmanager.DumpDot(add)
        
        idx2atom = {}
        for idx in range(self.numvars):
            var = self.converter.idx2var[idx]
            atom = self.converter.var2atom[var]
            k = "\" %d \"" % idx
            idx2atom[k] = "\" %s \"" % pretty_serialize(atom)
        inF = open('out.dot', 'r')
        str_dot = inF.read()
        inF.close()
        global outF
        outF = open("out.dot", "w")
        for k, v in idx2atom.items():
            str_dot = str_dot.replace(k, v)
        print(str_dot, file=outF)
    
    def dump_blif(self, bdd):
        add = self.ddmanager.BddToAdd(bdd)
        self.ddmanager.DumpBlif(add)
    
    def func2inst(self, f, ft):
        if ft.is_function_type():
            args = []
            i = 0
            for paramt in ft.param_types:
                i += 1
                paramt_name = str(i) + ":" + str(paramt) 
                args.append(Symbol(paramt_name, paramt))
            fi = Function(f, args)
            return fi
        else:
            return f

    def instantiate_function(self, f, ft, fi):
#         print("processing: %s" % f)
        instantiated = True
        if ft.is_function_type():
#             for idx, paramt in enumerate(ft.param_types):
            for idx in range(len(ft.param_types)-1, -1, -1):
                paramt = ft.param_types[idx]
                assert paramt.is_enum_type()
                arg = f.arg(idx)
                if not arg.is_enum_constant():
                    instantiated = False
                    dom = [Enum(d, paramt) for d in paramt.domain]
                    for d in reversed(dom):
                        subs = {}
                        subs[arg] = d
                        fn = f.substitute(subs)
#                         print("%s to %s" % (f, fn))
                        self.instantiate_function(fn, ft, fi)
            
        if instantiated:
            rt = ft
            if ft.is_function_type():
                rt = ft.return_type
            if rt.is_enum_type():
                dom = [Enum(d, rt) for d in rt.domain]
                for d in dom:
                    eq = EqualsOrIff(f, d)
                    if eq not in fi:
                        fi.append(eq)
            elif rt == BOOL:
                if f not in fi:
                    fi.append(f)
            else:
                assert(0)
        
    def initialize_atoms(self):
        self.atoms = []
        self.patoms = {}
        self.natoms = {}
        self.gatoms = {}
        self.p2natoms = {}
        self.pvars = set()
        self.nvars = set()
        self.converter.pre2nex = self.system.curr._pre2nex
        
        states_ordered = {}
        for s in self.system.curr._states:
            currSign = 0
            prefix = "2_"
            st = s.symbol_type()
            if st.is_function_type():
                currSign += len(st.param_types)
                st = st.return_type
            if st.is_enum_type():
                prefix = "1_"
            if s in self.system.curr._globals:
                prefix = "0_"
            states_ordered[prefix+str(currSign)+str(s)] = s
        
        states = sorted(states_ordered.items(), key=lambda v: v, reverse=True)
#         print(states)
        for nf, f in states:
            # print("processing %s" % pretty_serialize(f))
            if self.converter.zero != None and str(f).startswith("zero"):
                # print("skipping %s" % pretty_serialize(f))
                continue
            ft = f.symbol_type()
            fi = []
            self.instantiate_function(self.func2inst(f, ft), ft, fi)
#             print(fi)
            
            for atom in fi:
                self.atoms.append(atom)
                natom = pre2nex(self, atom)
                self.p2natoms[atom] = natom
                if atom != natom:
                    self.atoms.append(natom)
                
                bdd = self.get_bdd(atom)
                self.patoms[atom] = bdd
                var = self.converter.atom2var[atom]
                self.pvars.add(var)
#                 self.add_bddSupport(bdd, self.pvars)
                # print("adding pre: %s <-> %s := %d" % (pretty_serialize(atom), var, bdd.NodeReadIndex()))
                
                if atom == natom:
                    self.gatoms[atom] = bdd
                    
                bdd = self.get_bdd(natom)
                self.natoms[natom] = bdd
                var = self.converter.atom2var[natom]
                self.nvars.add(var)
#                 print("adding nex: %s <-> %s := %d" % (natom, var, bdd.NodeReadIndex()))
                
#                 self.add_bddSupport(bdd, self.nvars)
        # eprint("\t(#%d atoms with #%d variables)" % (len(self.atoms), self.converter.numvars))
        # print("\t(#%d atoms with #%d variables)" % (len(self.atoms), self.converter.numvars))
#         print(self.atoms)
#         print(self.patoms)
#         print(self.natoms)
#         assert(0)
        self.set_p2nVars()
#         self.check_typeok()
        self.print_atoms()
        self.converter.pnset = True
        self.numvars = self.converter.numvars
    
    def print_atoms(self):
        for i in range(self.converter.numvars):
            var = self.converter.idx2var[i]
            if var in self.converter.var2atom:
                atom = self.converter.var2atom[var]
                print("%d -> %s" % (i, pretty_serialize(atom)))
            else:
                print("%d has no var" % (i))
    
    def check_typeok(self):
        pass;
        # print("#typeok = %d" % len(self.converter.typeconst))
#         self.print_atoms()
#         for idx, t in enumerate(self.converter.typeconst):
#             if idx == 2:
#                 bdd = self.converter.typeok
#                 self.dump_dot(bdd)
#                 self.ddmanager.PrintMinterm(bdd)
#                 assert(0)
    
    def set_abstract(self):
        all_vars = set(self.converter.var2node.keys())
        pabstract = all_vars.difference(self.pvars)
        nabstract = all_vars.difference(self.nvars)
        self.projPre = self.converter.cube_from_var_list(pabstract)
        self.projNex = self.converter.cube_from_var_list(nabstract)

        pnabstract = all_vars.difference(self.pvars)
        pnabstract = pnabstract.difference(self.nvars)
        self.projAll = self.converter.cube_from_var_list(pnabstract)

        self.N = len(self.p2nvars)
        self.preV = repycudd.DdArray(self.ddmanager, self.N)
        self.nexV = repycudd.DdArray(self.ddmanager, self.N)
        count = 0
        for pv, nv in self.p2nvars.items():
            self.preV[count] = self.converter.var2node[pv]
            self.nexV[count] = self.converter.var2node[nv]
            assert(self.preV[count] != self.nexV[count])
            count += 1

    def print_pla(self, bddI, bddT):
        self.print_espresso(bddI, self.patoms, common.gopts.out+"/init")
#         bddT = self.axiom
#         for action, actionBdds in self.actions.items():
#             for actionBdd in actionBdds:
#                 bddT = self.ddmanager.Or(bddT, actionBdd)
        allowed = self.patoms
        for k, v in self.natoms.items():
            allowed[k] = v
        self.dump_dot(bddT)
        self.print_espresso(bddT, allowed, common.gopts.out+"/trel_formula")
#         allowed = self.patoms
#         for lhs, rhs in self.natoms.items():
#             if lhs not in allowed:
#                 allowed[lhs] = rhs
#                 name = str(lhs)
#                 self.print_espresso(bddT, allowed, name)
#                 del allowed[lhs]

    def experiment(self, bdd):
        ab_vars = set(self.converter.var2node.keys())
        allowed_atoms = set()
        allowed_atoms.add("__semaphore(s0)")
#         allowed_atoms.add("__semaphore(s1)")
#         allowed_atoms.add("__semaphore(s2)")
        allowed_atoms.add("__link(c0, s0)")
#         allowed_atoms.add("__link(c1, s0)")
        for atom in self.patoms.keys():
            if str(atom) in allowed_atoms:
                var = self.converter.atom2var[atom]
                ab_vars.discard(var)
        proj = self.converter.cube_from_var_list(ab_vars)
        
        bddNew = self.ddmanager.ExistAbstract(bdd, proj)
        self.dump_dot(bddNew)
        assert(0)
    
    def check_safe(self, bdd):
        bddC = self.ddmanager.And(bdd, self.bddnotP)
        return bddC == self.ddmanager.ReadLogicZero()

#             print("-- Finite check: violated --")
#             # self.ddmanager.PrintMinterm(bddC)
# #             bddC = self.ddmanager.ExistAbstract(bddC, self.projPre)
#             self.dump_dot(bddC)
#             assert(0)
        # else:
        #     print("-- Finite check: safe --")
    def label_is_usable(self, label):
        return not(("__" + label) in self.varlabels or label[:3] == "en_" or label[0] == "(")

    # def get_state_vars(self, bdd):



    def print_bdd(self, bdd):
        print("----------------------- BDD -----------------------")
        self.ddmanager.PrintMinterm(bdd)
        print("----------------------- END BDD -----------------------")

    def cube_to_minterm(self, cube, symbols):
        s = ""
        for sym in symbols:
            is_sat = self.solve_formula(self.solver, And(cube, sym), quiet=True)
            if is_sat:
                s += "1"
            else:
                s += "0"
        return s

    def get_all_satisfying_assignments(self, f, symbols):
        sat_assignments = []
        x = []
        cube = self.solve_with_model(self.solver, f, x, quiet=True)
        i = 0
        while cube is not None:
            sat_assignments.append(self.cube_to_minterm(cube, symbols))
            self.solver.push()
            self.solver.add_assertion(Not(cube))
            i += 1
            cube = self.solve_with_model(self.solver, f, x, quiet=True)
        while i > 0:
            self.solver.pop()
            i -= 1
        return sat_assignments

    def cube_to_formula(self, cube, symbols):
        f = TRUE()
        for sym in symbols:
            is_sat = self.solve_formula(self.solver, And(cube, sym), quiet=True)
            if is_sat:
                f = And(f, sym)
            else:
                f = And(f, Not(sym))
        return f

    def forward_reach_sat(self):
        # SAT based forward reachability
        symbols = set()
        for var in self.system.curr._states:
            for abst, conc_list in self.system._enumsorts.items():
                for sort_inst in conc_list:
                    symbols.add(var(sort_inst))
        x = []
        self.init_solver()

        seen = set()
        reachable = set()

        seen.add(self.cube_to_minterm(init_formula(self), symbols))
        reachable.add(self.cube_to_minterm(init_formula(self), symbols))
        queue = [init_formula(self)]
        while len(queue) > 0:
            cube = queue.pop(0)
            for action in self.system.curr._actions:
                if self.solve_formula(self.solver, And(cube, action[0]), quiet=True):
                    cube2 = self.solve_with_model(self.solver, And(cube, action[0]), x, quiet=True)
        



        print(self.get_all_satisfying_assignments(init_formula(self), symbols))

        cube = self.solve_with_model(self.solver, init_formula(self), x, quiet=True)
        if cube is None:
            return
        symbols = list(symbols)
        print(symbols)
        print(self.cube_to_minterm(cube, symbols))
        

    def print_pla(self):
        """Forward Reachability using BDDs."""
        prop = prop_formula(self)

        self.ddmanager = repycudd.DdManager()
        self.converter = BddConverter(environment=get_env(),
                                      ddmanager=self.ddmanager)

        self.build_actions()
        self.build_axioms()
           
        bddI = self.formula2bdd(init_formula(self))
        bddT = self.formula2bdd(trel_formula(self))
        bddA = self.formula2bdd(axiom_formula(self))
        bddP = self.formula2bdd(prop_formula(self))
        self.bddnotP = self.ddmanager.Not(bddP)


        if axiom_formula(self) != TRUE():
            bddT = self.ddmanager.And(bddT, bddA)
  
        self.set_atoms()
        self.set_bddvars()
        self.set_p2nVars()
        self.set_abstract()
        
        self.initialize_atoms()
        sources = list()
        initSrc = self.ddmanager.AndAbstract(bddI, self.axiom, self.projPre)
        totalR = initSrc
        sources.append((initSrc, "init"))
        iteration = 0

        print("BEGIN_VARLABELS")
        self.varlabels = [str(self.converter.var2atom[self.converter.idx2var[i]]) for i in range(self.converter.numvars)]
        for i, label in enumerate(self.varlabels):
            print("%d\t%s" % (i, label))
        print("END_VARLABELS")

        self.print_bdd(bddI)
        return

        equality_constraints = TRUE()
        # ensure that distinguished constants are assigned 
        for equality_predicate_dict in self.converter._bddVarEqEnum.values():
            constraint = FALSE()
            for equality_predicate in equality_predicate_dict.values():
                assignment = TRUE()
                for equality_predicate_2 in equality_predicate_dict.values():
                        if equality_predicate == equality_predicate_2:
                            continue
                        assignment = And(assignment, Not(equality_predicate_2))
                assignment = And(assignment, equality_predicate)
                constraint = Or(constraint, assignment)
            equality_constraints = And(equality_constraints, constraint)
        bddEq = self.formula2bdd(equality_constraints)
        

        # print("\t(running forward reachability)")
        while (len(sources) != 0):
            # print("#sources = %d" % len(sources))
            src, comment = sources.pop()
            iteration += 1
            
            if src == self.ddmanager.ReadLogicZero():
                # print("#%d Found no new states" % iteration)
                continue
            # else:
            #     print("#%d Found #%d new states: %s" % (iteration, len(sources)+1, comment))
#                 src = self.ddmanager.And(src, self.axiom)
            notTotalR = self.ddmanager.Not(totalR)
            
            destinations = []
            for action, actionBdds in self.actions.items():
                # print(action)
                nex = self.ddmanager.Zero()
                done = False
                for actionBdd in actionBdds:
                    image = src
                    image = self.ddmanager.And(src, bddEq)
                    image = self.ddmanager.AndAbstract(image, actionBdd, self.projNex)
                    image = self.ddmanager.And(image, bddA)
                    if image == self.ddmanager.ReadLogicZero(): continue
                    image = self.ddmanager.SwapVariables(image, self.preV, self.nexV, self.N)
                    image = self.ddmanager.AndAbstract(image, self.axiom, self.projPre)
                    image = self.ddmanager.And(image, bddP)
                    if image == self.ddmanager.ReadLogicZero(): continue
                    image = self.ddmanager.And(image, notTotalR)
                    if image == self.ddmanager.ReadLogicZero(): continue
                    nex = self.ddmanager.Or(nex, image)
                    # print(action)
                    # self.ddmanager.PrintMinterm(nex)
                    done = True
#                     print("found a state in %s" % action)
#                         break
                if done:
                    destinations.append((nex, action))
            
            for dest, comment in destinations:
                sources.append((dest, comment))
                totalR = self.ddmanager.Or(totalR, dest)

        
        self.ddmanager.PrintMinterm(totalR)
        # https://stackoverflow.com/questions/24277488/in-python-how-to-capture-the-stdout-from-a-c-shared-library-to-a-variable

def sat_forwardReach(fname):
    global start_time
    utils.start_time = time.time()
    system = TransitionSystem()
    p = FR(system)
    # TODO: this is a bad way to do this but works for now. It reads |epoch|=1 from mock.txt 
    # but this should always be 1
    read_problem(p, fname)
    
    set_axiom_formula(p, False)
    set_prop_formula(p, False)
    set_init_formula(p, False)
    set_trel_formula(p, False)

    if len(p.system.curr._infers) != 0:
        print()
        syntax_infers = []
        for cl, label in p.system.curr._infers.items():
            syntax_infers.append((label, cl))
        pretty_print_inv(syntax_infers, "Syntax-guided inferences")
    
    if not p.system.is_finite():
        print("System has unbounded sorts")
        print("All sorts should be finite for BDD-based forward reachability")
        assert(0)

    p.forward_reach_sat()

def forwardReach(fname):
    global start_time
    utils.start_time = time.time()
    system = TransitionSystem()
    p = FR(system)
    read_problem(p, fname)
    print("\t(running: frpo)")
    
    set_axiom_formula(p, False)
    set_prop_formula(p, False)
    set_init_formula(p, False)
    set_trel_formula(p, False)

    if len(p.system.curr._infers) != 0:
        print()
        syntax_infers = []
        for cl, label in p.system.curr._infers.items():
            syntax_infers.append((label, cl))
        pretty_print_inv(syntax_infers, "Syntax-guided inferences")
    
    if not p.system.is_finite():
        print("System has unbounded sorts")
        print("All sorts should be finite for BDD-based forward reachability")
        assert(0)

    p.print_pla()

#     set_solver(p)
    # inferences = p.execute()
    # eprint("\t(adding %d forward inferences)" % len(inferences))
    # print("\t(adding %d forward inferences)" % len(inferences))
    # p.reset()
    # for tt in p.system._sort2fin.keys():
    #     p.system.unbound_sort(tt)
    # p.system.infinitize()
    # inferences_inf = {}
    # for label, i in inferences:
    #     inferences_inf[i.fsubstitute()] = label
    # for cl, label in inferences_inf.items():
    #     if cl not in p.system.orig._infers:
    #         p.system.orig._infers[cl] = label
            
    # for k, v in p.system._fin2sort.iteritems():
    #     p.system._sort2fin[v] = k
    # p.system._fin2sort.clear()

    # return p.system
    
if __name__ == "__main__":  
    args = sys.argv
    if len(args) != 2:
        print("Usage %s <file.smt2>" % args[0])
        exit(1)
    fname = args[1]
    forwardReach(fname)
