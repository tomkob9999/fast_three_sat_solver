
'''
Fast 3-SAT Solver

This class provides a highly efficient algorithm for solving 3-SAT problems by leveraging a combination of 2-SAT reductions, 
implication chains, and De Morgan transformations. The algorithm is designed to operate in linear time by adhering to the following steps:

1. Implication Generation:
   Each 3-SAT clause generates 6 implications:
   - 3 implications of the form (-a) -> (b, c)
   - 3 implications of the form (-a, -b) -> (c) -> (a, b)

2. Variable Invalidation:
   - The first round of 2-SAT analysis invalidates variables based on (-a) -> (b, c) implications.
   - The second round derives further implications using (-a, -b) -> (c) -> (a, b) and applies 2-SAT again.

3. De Morgan Transformation:
   - Converts invalidated variables and tuples into SAT conditions using De Morgan's law.
   - Merges the transformed conditions and performs a final 2-SAT test to determine satisfiability.

4. Final Decision:
   - The result of the final 2-SAT test provides the definitive answer for the 3-SAT problem.

Complexity:
   - The algorithm is believed to run in linear time relative to the number of clauses and variables.
   - Memory usage is optimized by avoiding exponential growth in implication space, focusing on dynamic implication propagation.

Example Usage:
    solver = FastThreeSATSolver()
    clauses = [(-4, -1, 3), (-3, -2, -1), (-4, 1, 3), (-2, -1, 4), (-4, -2, 1), (1, 2, 4)]
    solver.solve(clauses)


Author: Tomio Kobayashi
Date: 2025/03/03
Version: 1.0.0


'''


import networkx as nx

class FastThreeSATSolver:

    class TwoSATSets:
        def __init__(self):
            self.sets_fwd = {}
            self.sets_bkw = {}  # this coauses duplicates
            self.unsat_pos = set()
            self.unsat_neg = set()
            self.unsat_tup = set()
            
        def append(self, tup):
            if -tup[0] not in self.sets_fwd:
                self.sets_fwd[-tup[0]] = set()
            self.sets_fwd[-tup[0]].add(FastThreeSATSolver.normalize_tuple((tup[1], tup[2])))
            if -tup[1] not in self.sets_fwd:
                self.sets_fwd[-tup[1]] = set()
            self.sets_fwd[-tup[1]].add(FastThreeSATSolver.normalize_tuple((tup[0], tup[2])))
            if -tup[2] not in self.sets_fwd:
                self.sets_fwd[-tup[2]] = set()
            self.sets_fwd[-tup[2]].add(FastThreeSATSolver.normalize_tuple((tup[0], tup[1])))
            
            this_tup = FastThreeSATSolver.normalize_tuple((-tup[1], -tup[2]))
            if this_tup not in self.sets_bkw:
                self.sets_bkw[this_tup] = set()
                self.sets_bkw[this_tup].add(tup[0])


            this_tup = FastThreeSATSolver.normalize_tuple((-tup[0], -tup[1]))
            if this_tup not in self.sets_bkw:
                self.sets_bkw[this_tup] = set()
                self.sets_bkw[this_tup].add(tup[2])
            
            this_tup = FastThreeSATSolver.normalize_tuple((-tup[0], -tup[2]))
            if this_tup not in self.sets_bkw:
                self.sets_bkw[this_tup] = set()
                self.sets_bkw[this_tup].add(tup[1])
            
        def find_unsat(self):
            for k, v in self.sets_fwd.items():
                # print("sets_fwd check", k, v)
                if not FastThreeSATSolver.two_sat(v):
                    # print("k", k)
                    # print("sets_fwd UNSAT", k, v)
                    if k > 0:
                        self.unsat_pos.add(k)
                    else:
                        self.unsat_neg.add(-k)
    
            for k, vv in self.sets_bkw.items():
                for v in vv:
                    # print("sets_bwd check", k, v)
                    # if (-4, -1) == k:
                        # print("k", k, "v", v)
                        # # print(v in self.sets_fwd)
                        # print(self.sets_fwd)
                    # print("v", v)
                    if v in self.sets_fwd:
                        # print("self.sets_fwd[v]", self.sets_fwd[v])
                        # if (-k[1], -k[0]) in self.sets_fwd[v]:
                        # if k in self.sets_fwd[v]:
                        # if k in self.sets_fwd[v] and FastThreeSATSolver.normalize_tuple((k[0], k[1])) in self.sets_fwd[v]  and FastThreeSATSolver.normalize_tuple((-k[0], -k[1])) in self.sets_fwd[v] and FastThreeSATSolver.normalize_tuple((-k[0], k[1])) in self.sets_fwd[v] and FastThreeSATSolver.normalize_tuple((k[0], -k[1])) in self.sets_fwd[v]:
                      
                        # two_sat_cond = [(-k[1], -k[0])] + list(self.sets_fwd[v])
                        two_sat_cond = [k] + list(self.sets_fwd[v])
                        # print("two_sat_cond 1", two_sat_cond)
                        if not FastThreeSATSolver.two_sat(two_sat_cond):
                        # if k in self.sets_fwd[v] and FastThreeSATSolver.normalize_tuple((k[0], k[1])) in self.sets_fwd[v]  and FastThreeSATSolver.normalize_tuple((-k[0], -k[1])) in self.sets_fwd[v] and FastThreeSATSolver.normalize_tuple((-k[0], k[1])) in self.sets_fwd[v] and FastThreeSATSolver.normalize_tuple((k[0], -k[1])) in self.sets_fwd[v]:
                            # self.unsat_tup.add(k)
                            # This should be correct due to DeMorgan
                            self.unsat_tup.add((-k[1], -k[0]))
                            # self.unsat_tup.add(v)
                    # if not FastThreeSATSolver.two_sat(v):
                    #     print("sets_bwd UNSAT", k, v)
                    #     if k > 0:
                    #         self.unsat_pos.add(k)
                    #     else:
                    #         self.unsat_neg.add(-k)
            # print("self.unsat_pos", self.unsat_pos)
            # print("self.unsat_neg", self.unsat_neg)
            # print("self.unsat_tup", self.unsat_tup)
            two_sat_cond = []
            for p in self.unsat_pos:
                two_sat_cond.append((-p,))
            for n in self.unsat_neg:
                two_sat_cond.append((n,))

            two_sat_cond += list(self.unsat_tup)
            # print("two_sat_cond", two_sat_cond)
            
            if not FastThreeSATSolver.two_sat(two_sat_cond):
            # if len((self.unsat_pos & self.unsat_neg)) > 0:
            #     print("Contradictions:", (self.unsat_pos & self.unsat_neg))
            #     return True
            # elif len(self.unsat_tup) > 0:
            # elif not FastThreeSATSolver.two_sat(self.unsat_tup):
                # print("self.unsat_tup two_sat", FastThreeSATSolver.two_sat(self.unsat_tup))
                # print("Contradictions:",self.unsat_tup)
                # print("Contradictions:", two_sat_cond)
                return True
            else:
                return False
    
    def __init__(self):
        # self.implications = {}  # Dictionary of sets {literal: set(implications)}
        # self.banned = set()  # Set for banned variables (1-element or 2-element tuples)
        self.twosat_sets = FastThreeSATSolver.TwoSATSets()
        
    def normalize_tuple(pair):
        """Ensures that (x, y) is always stored in sorted order."""
        if len(pair) == 1:
            return (-pair[0],)
        else:
            x, y = pair
            return (x, y) if x < y else (y, x)

    def add_clause(self, clause):
        """Processes a new 3-SAT clause (a, b, c)."""

        self.twosat_sets.append(clause)

    def solve(self, clauses):
        """Processes all clauses and determines SAT/UNSAT."""
        
        variables = sorted(set([abs(v) for vv in clauses for v in vv]))

        for clause in clauses:
            self.add_clause(clause)

        if self.twosat_sets.find_unsat():
            print("UNSAT")
            return False
        else:
            print("SAT")
            return True

    # use networkx
    def two_sat(clauses):

        G = nx.DiGraph()
        
        for clause in clauses:
            if len(clause) == 1:
                x = clause[0]
                G.add_edge(-x, x)  # Implication: If not x, then x (contradiction)
                G.add_edge(x, x)    # Maintain consistency for the unit clause
            elif len(clause) == 2:
                x, y = clause
                G.add_edge(-x, y)  # If not x, then y
                G.add_edge(-y, x)  # If not y, then x
        
        # Find Strongly Connected Components (SCCs)
        scc = list(nx.strongly_connected_components(G))
        
        # Map nodes to their SCC index
        node_to_scc = {node: i for i, comp in enumerate(scc) for node in comp}
        
        # Check for contradictions: a variable and its negation in the same SCC
        for var in G.nodes():
            if -var in G.nodes() and node_to_scc[var] == node_to_scc[-var]:
                return False  # UNSAT
        
        return True  # SAT

    # no graph
    # def two_sat2(clauses):
    #     # Extract all variables from clauses
    #     variables = set(abs(var) for clause in clauses for var in clause)
        
    #     # Generate all possible truth assignments (1=True, -1=False)
    #     for assignment in product([True, False], repeat=len(variables)):
    #         # Map variable to its truth value
    #         assignment_dict = {var: value for var, value in zip(sorted(variables), assignment)}
            
    #         # Evaluate all clauses
    #         if all(any((lit > 0 and assignment_dict[abs(lit)]) or (lit < 0 and not assignment_dict[abs(lit)]) for lit in clause) for clause in clauses):
    #             # Found a satisfying assignment
    #             model = {var: assignment_dict[var] for var in variables}
    #             is_satisfiable = True
    #             break
    #     else:
    #         # No satisfying assignment found
    #         model = None
    #         is_satisfiable = False
    #     return is_satisfiable
# Example CNF (3-SAT clauses)



clauses = [
           (-4, -1, 3), 
           (-3, -2, -1), 
           (-4, 1, 3), 
           (-2, -1, 4), 
           (-4, -2, 1), 
           (1, 2, 4), 
           (-1, 2, 3), 
           (-4, -3, 2), 
           (-3, -1, 4), 
           (-2, 1, 4), 
          ]  # -5


print("TEST UNSAT")
# UNSAT Cases
clauses =  [(-4, -2, 1), (-4, 1, 3), (1, 2, 3), (-4, -3, 1), (-4, -1, 3), (-2, 3, 4), (-2, -1, 4), (-4, 1, 2), (-3, -1, 2), (-1, 2, 4), (-4, -2, -1), (-4, -1, 2), (-4, -3, -1), (-3, -2, 1), (1, 3, 4), (-3, 2, 4), (-4, -3, -2), (-4, -2, 1), (-4, -3, -2), (-4, -3, -1)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-2, -1, 4), (1, 3, 4), (1, 2, 4), (-4, 1, 2), (-3, -2, -1), (-1, 2, 4), (-4, -3, -2), (-1, 2, 4), (-2, 3, 4), (1, 2, 4), (-4, -2, 1), (-4, -1, 2), (-4, -1, 3), (-4, -3, 2), (-4, -2, 3), (-3, -2, 4), (1, 2, 3), (-3, 1, 4), (-4, -3, 2), (-2, -1, 3)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-2, 3, 4), (-2, -1, 3), (1, 2, 3), (-2, 1, 3), (-4, -2, 3), (-1, 2, 4), (-4, -3, 2), (-4, -3, -1), (-3, 1, 4), (1, 2, 3), (-3, -2, 4), (-4, 2, 3), (-4, -3, -2), (-3, -2, 1), (-2, -1, 4), (-4, -3, -1), (-4, -1, 2), (-3, -1, 2), (-3, -2, 4), (-4, -3, -2)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-1, 2, 4), (-4, 1, 2), (-3, 1, 2), (-2, 3, 4), (2, 3, 4), (-4, -3, -1), (-4, -3, -1), (1, 2, 3), (-2, 1, 4), (-2, -1, 4), (-4, -2, -1), (-4, -1, 3), (2, 3, 4), (-4, 2, 3), (-4, -2, 3), (-3, -2, 1), (-3, -1, 4), (-1, 2, 3), (-2, 3, 4), (-2, 1, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, 2), (-4, 1, 2), (-1, 2, 4), (-4, -3, -1), (-4, -2, 1), (-2, 3, 4), (-3, -2, 4), (1, 2, 4), (-2, 1, 4), (-4, -2, 1), (-2, 3, 4), (-2, 1, 4), (-3, 1, 2), (2, 3, 4), (-3, -2, -1), (-4, -1, 3), (-1, 3, 4), (-3, -2, 4), (-3, 2, 4), (-4, 1, 2)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-3, -2, -1), (-3, 1, 2), (-1, 2, 4), (-3, -1, 4), (-2, -1, 3), (-4, -1, 2), (-4, 1, 2), (-4, -2, 3), (-4, -3, 2), (-3, 1, 2), (-4, 1, 3), (1, 2, 3), (-4, -3, 1), (-3, -2, 4), (-3, -2, 4), (-3, -1, 4), (-3, -1, 2), (1, 2, 4), (-3, 2, 4), (-2, 1, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-2, 1, 4), (-4, 1, 2), (-3, -2, 4), (-3, -2, 4), (-4, -3, 1), (-4, 1, 2), (-4, -3, -1), (-4, -2, -1), (-4, -2, 3), (-1, 3, 4), (-4, -3, -1), (1, 2, 3), (-4, -3, -1), (1, 2, 4), (-3, 2, 4), (-4, -3, -1), (-4, 2, 3), (-4, 1, 2), (2, 3, 4), (-2, 3, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-3, -2, 4), (-1, 2, 4), (-2, 3, 4), (1, 2, 4), (-3, -1, 4), (-4, -3, 2), (-3, -1, 2), (-4, -3, 2), (-4, -3, 1), (2, 3, 4), (-2, -1, 4), (-4, -2, -1), (-1, 2, 3), (-3, -1, 2), (-4, -1, 3), (-4, -1, 3), (-4, -2, 1), (-4, -1, 3), (-4, 1, 2), (-2, 3, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, 2), (2, 3, 4), (-4, -3, 2), (-4, -3, -2), (2, 3, 4), (-3, 1, 2), (-4, -3, -2), (-1, 3, 4), (-3, -2, 1), (-3, -2, 4), (-4, 2, 3), (-1, 2, 3), (-3, -1, 2), (-2, -1, 4), (-3, 1, 2), (-2, 1, 3), (-1, 2, 4), (-2, -1, 3), (-2, -1, 4), (-2, 1, 3)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, 1), (1, 2, 3), (-4, -2, 1), (-4, -2, 1), (-2, 1, 3), (-4, 1, 3), (-4, -3, -2), (-3, -2, 4), (-2, -1, 4), (-4, -2, 1), (-1, 3, 4), (-4, -1, 3), (-1, 2, 4), (1, 2, 3), (1, 2, 4), (-2, 1, 4), (1, 2, 4), (-3, -1, 2), (-4, 1, 3), (-2, 3, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-3, -2, 1), (-4, 2, 3), (-2, 1, 3), (-1, 2, 4), (-3, -2, 1), (-2, -1, 4), (1, 3, 4), (-3, -1, 2), (-4, -1, 2), (-4, -3, 2), (-3, -1, 2), (-2, -1, 4), (-3, 2, 4), (-4, -2, -1), (-2, -1, 3), (-2, 1, 3), (-3, -1, 4), (-4, -1, 2), (-2, 1, 3), (-4, 1, 3)]

print("TEST SAT")
# SAT
clauses =  [(-4, 1, 3), (-4, -3, -2), (-4, -3, -1), (-4, -2, 3), (-4, -2, 3), (-3, 1, 4), (-3, -2, 4), (-3, 1, 2), (-4, 1, 2), (-3, -2, -1), (-4, 1, 2), (-2, 1, 4), (1, 3, 4), (-4, -1, 3), (-3, -1, 2), (1, 2, 4), (-2, -1, 4), (-2, 3, 4), (-3, -2, 4), (-3, 1, 2)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, -2), (-4, 1, 3), (-1, 3, 4), (-3, 2, 4), (1, 2, 4), (-4, 1, 3), (-4, -3, -2), (-4, -3, -2), (1, 3, 4), (1, 2, 3), (-3, -2, -1), (-3, -2, 4), (-3, 1, 4), (-4, 1, 3), (-4, 2, 3), (-4, -2, -1), (-3, 2, 4), (-4, -3, -2), (-4, -3, -2), (-4, -2, 3)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-1, 2, 4), (-2, -1, 4), (-3, -2, -1), (-1, 2, 4), (-2, -1, 4), (2, 3, 4), (-3, 2, 4), (-3, -1, 2), (-3, 2, 4), (2, 3, 4), (-4, -2, -1), (-2, -1, 3), (-3, 2, 4), (-3, 1, 4), (-4, -2, -1), (2, 3, 4), (-3, -1, 2), (-4, -2, 3), (-3, -1, 4), (-1, 3, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, 2), (-1, 2, 3), (-3, -2, 1), (-2, 3, 4), (-4, -3, 2), (-2, 1, 4), (-4, -3, -2), (-2, 1, 3), (-2, -1, 4), (-4, -3, 2), (-3, -1, 2), (-4, -3, 1), (-4, 1, 3), (-2, -1, 3), (-3, -1, 2), (-4, -1, 2), (-2, 1, 4), (-3, -2, -1), (-1, 2, 3), (-4, -3, -1)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, 2), (1, 2, 3), (-4, -3, 2), (-4, -2, -1), (-3, -2, 4), (-2, 1, 3), (-3, -2, -1), (-4, -1, 3), (-4, 1, 3), (-1, 2, 3), (-3, -1, 2), (-3, 2, 4), (1, 2, 3), (-2, 3, 4), (1, 3, 4), (-3, 1, 4), (-3, -2, -1), (1, 2, 4), (-4, 1, 2), (-4, -1, 2)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-3, 1, 2), (-2, 1, 3), (2, 3, 4), (-4, 1, 2), (-2, 1, 4), (-3, -1, 2), (1, 3, 4), (-4, 2, 3), (-4, -2, 3), (-4, -3, 2), (-3, 1, 2), (-4, -1, 2), (-4, -3, -2), (-2, -1, 3), (1, 2, 4), (-1, 2, 4), (-4, 2, 3), (-2, 1, 3), (-4, -2, -1), (-2, -1, 3)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(2, 3, 4), (-3, -2, 1), (-3, 2, 4), (-4, -3, -1), (-2, 1, 3), (-2, -1, 3), (-3, -2, 1), (-2, -1, 4), (-3, 1, 4), (-4, -3, -2), (-1, 2, 3), (-1, 3, 4), (-2, -1, 3), (-3, -1, 4), (-4, -1, 2), (-3, 1, 2), (-2, 1, 4), (1, 2, 4), (-3, 1, 2), (1, 3, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -1, 3), (1, 3, 4), (-3, -1, 2), (-4, 1, 2), (-1, 2, 3), (2, 3, 4), (1, 3, 4), (-2, -1, 3), (-2, 1, 3), (-1, 3, 4), (-2, -1, 4), (-4, -3, 2), (-3, -2, 1), (-4, 1, 2), (-2, 1, 3), (-2, 3, 4), (-3, 2, 4), (-4, 1, 3), (-3, 1, 4), (-3, -1, 2)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-4, -3, -2), (1, 2, 3), (-3, -2, 1), (1, 3, 4), (-1, 2, 4), (-3, -1, 2), (1, 3, 4), (-3, 1, 2), (-2, -1, 4), (-4, -2, -1), (2, 3, 4), (-1, 3, 4), (2, 3, 4), (-4, -2, -1), (-3, 2, 4), (1, 3, 4), (-4, -3, 2), (-4, -3, -1), (-4, -3, 1), (-4, -3, -1)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-3, -1, 4), (-3, 1, 2), (-4, -2, 1), (1, 2, 3), (1, 2, 4), (1, 2, 4), (-2, 3, 4), (2, 3, 4), (-4, 1, 3), (1, 3, 4), (-4, -3, 2), (-4, 1, 3), (-4, 1, 2), (-3, -2, -1), (-3, -1, 4), (-2, -1, 3), (-3, -2, -1), (-4, 1, 2), (-4, -3, 2), (-3, -2, 4)]
print(FastThreeSATSolver().solve(clauses))
clauses =  [(-3, -1, 2), (-4, 2, 3), (-4, -3, 1), (-3, -1, 2), (-3, -2, 4), (-4, 1, 2), (-3, -2, -1), (-4, -1, 2), (-4, -1, 3), (-3, -2, 4), (-2, 1, 3), (-3, -1, 2), (-3, -2, 1), (-4, -3, 2), (1, 2, 3), (-2, 1, 3), (-2, -1, 3), (-1, 2, 4), (-3, -2, 1), (-3, -1, 2)]
print(FastThreeSATSolver().solve(clauses))


# Example Usage
print(FastThreeSATSolver().solve(clauses))  # Output: SAT or UNSAT