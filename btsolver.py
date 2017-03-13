import time
from collections import Counter

import constraint
import constraintnetwork
import domain
import filereader
import gameboard
import trail
import variable

VariableSelectionHeuristic = {'None': 0, 'MRV': 1, 'DH': 2}
ValueSelectionHeuristic = {'None': 0, 'LCV': 1}
ConsistencyCheck = {
    'None': 0,
    'ForwardChecking': 1,
    'ArcConsistency': 2,
    'NKT': 3,
    'NKP': 4
}
HeuristicCheck = {'None': 0, 'NKP': 1, 'NKT': 2}


class BTSolver:
    "Backtracking solver"

    def __init__(self, gb):
        self.network = filereader.GameBoardToConstraintNetwork(gb)
        self.trail = trail.masterTrailVariable
        self.hassolution = False
        self.gameboard = gb

        self.numAssignments = 0
        self.numBacktracks = 0
        self.preprocessing_startTime = 0
        self.preprocessing_endTime = 0
        self.startTime = None
        self.endTime = None

        # refers to which variable selection heuristic in use(0 means default,
        # 1 means MRV, 2 means DEGREE)
        self.varHeuristics = 0
        # refers to which value selection heuristic in use(0 means default, 1
        # means LCV)
        self.valHeuristics = 0
        # refers to which consistency check will be run(0 for backtracking, 1
        # for forward checking, 2 for arc consistency)
        self.cChecks = 0
        self.heuristicChecks = 0
        # self.runCheckOnce = False
        self.tokens = []  # tokens(heuristics to use)

    def setTokens(self, tokens):
        ''' set the set of heuristics to be taken into consideration'''
        self.tokens = tokens

    def setVariableSelectionHeuristic(self, vsh):
        '''modify the variable selection heuristic'''
        self.varHeuristics = vsh

    def setValueSelectionHeuristic(self, vsh):
        '''modify the value selection heuristic'''
        self.valHeuristics = vsh

    def setConsistencyChecks(self, cc):
        '''modify the consistency check'''
        self.cChecks = cc

    def setHeuristicChecks(self, hc):
        '''modify the heurisic check (naked pairs and triples)'''
        self.heuristicChecks += hc

    def getSolution(self):
        return self.gameboard

    def getTimeTaken(self):
        return self.endTime - self.startTime

    def checkConsistency(self):
        if self.cChecks == 0:
            return self.assignmentsCheck()
        elif self.cChecks == 1:
            return self.forwardChecking()
        elif self.cChecks == 2:
            return self.arcConsistency()
        elif self.cChecks == 3:
            return self.nakedTriple()
        elif self.cChecks == 4:
            return self.nakedPairs()
        else:
            return self.assignmentsCheck()

    def checkHeuristics(self):
        if self.heuristicChecks == 1:
            return self.nakedPairs()
        elif self.heuristicChecks == 2:
            return self.nakedTriples()
        elif self.heuristicChecks == 3:
            return self.nakedPairs() and self.nakedTriples()
        else:
            return True

    def assignmentsCheck(self):
        for v in self.network.variables:
            if v.isAssigned():
                for vOther in self.network.getNeighborsOfVariable(v):
                    if v.getAssignment() == vOther.getAssignment():
                        return False
        return True

    def nakedPairs(self):
        for v in self.network.variables:
            neighbors = self.network.getNeighborsOfVariable(v)
            for n in neighbors:
                if not (v.isAssigned() or n.isAssigned()):
                    vvals = v.Values()
                    nvals = n.Values()
                    if len(vvals) == len(nvals) == 2 and \
                       set(vvals) == set(nvals):
                        common = [
                            list(filter(lambda x: x in c1, sublist))
                            for sublist in [
                                neighbors,
                                self.network.getNeighborsOfVariable(n)
                            ]
                        ]
                        for c in common:
                            for val in vvals:
                                if val in c.Values():
                                    c.removeValueFromDomain(val)
                elif v.getAssignment() == n.getAssignment():
                    return False
        return True

    def nakedTriples(self):
        """
           TODO:  Implement naked triples heuristic.
        """
        pass

    def forwardChecking(self):
        """
           TODO:  Implement forward checking.
        """
        pass

    def arcConsistency(self):
        for v in self.network.variables:
            if v.isAssigned():
                for n in self.network.getNeighborsOfVariable(v):
                    if not n.isAssigned():
                        n.removeValueFromDomain(v.getAssignment())
                    elif v.getAssignment() == n.getAssignment():
                        return False
        return True

    def selectNextVariable(self):
        if self.varHeuristics == 0:
            return self.getfirstUnassignedVariable()
        elif self.varHeuristics == 1:
            return self.getMRV()
        elif self.varHeuristics == 2:
            return self.getDegree()
        else:
            return self.getfirstUnassignedVariable()

    def getfirstUnassignedVariable(self):
        for v in self.network.variables:
            if not v.isAssigned():
                return v
        return None

    def getMRV(self):
        """
        TODO: Implement MRV heuristic
        @return variable with minimum remaining values that isn't assigned,
        null if all variables are assigned.
        """
        pass

    def getDegree(self):
        """
        TODO: Implement Degree heuristic
        @return variable constrained by the most unassigned variables, null if
        all variables are assigned.
        """
        pass

    def getNextValues(self, v):
        """
        Value Selection Heuristics. Orders the values in
        the domain of the variable
        passed as a parameter and returns them as a list.
        @return List of values in the domain of a
                variable in a specified order.
        """
        if self.valHeuristics == 0:
            return self.getValuesInOrder(v)
        elif self.valHeuristics == 1:
            return self.getValuesLCVOrder(v)
        else:
            return self.getValuesInOrder(v)

    def getValuesInOrder(self, v):
        """
            Default value ordering.
            @param v Variable whose values need to be ordered
            @return values ordered by lowest to highest.
        """
        values = v.domain.values
        return sorted(values)

    def getValuesLCVOrder(self, v):
        nvalues = list()
        for n in self.network.getNeighborsOfVariable(v):
            nvalues += n.domain.values
        values = v.domain.values + nvalues
        values = [item for items, c in Counter(values).most_common()
                  for item in [items] * c]
        values.reverse()
        return set(values)

    def success(self):
        """ Called when solver finds a solution """
        self.hassolution = True
        self.gameboard = filereader.ConstraintNetworkToGameBoard(
            self.network,
            self.gameboard.N,
            self.gameboard.p,
            self.gameboard.q)

    def solve(self):
        """ Method to start the solver """
        self.startTime = time.time()
        # try:
        self.solveLevel(0)
        # except:
        # print("Error with variable selection heuristic.")
        self.endTime = time.time()
        # trail.masterTrailVariable.trailStack = []
        self.trail.trailStack = []

    def solveLevel(self, level):
        """
        Solver Level
        @param level How deep the solver is in its recursion.
        @throws VariableSelectionException
        contains some comments that can be uncommented
        for more in depth analysis
        """
        # print("=.=.=.=.=.=.=.=.=.=.=.=.=.=.=.=")
        # print("BEFORE ANY SOLVE LEVEL START")
        # print(self.network)
        # print("=.=.=.=.=.=.=.=.=.=.=.=.=.=.=.=")

        if self.hassolution:
            return

        # Select unassigned variable
        v = self.selectNextVariable()
        # print("V SELECTED --> " + str(v))

        # check if the assigment is complete
        if (v is None):
            # print("!!! GETTING IN V == NONE !!!")
            for var in self.network.variables:
                if not var.isAssigned():
                    raise ValueError(
                        "Something happened with the \
                        variable selection heuristic")
            self.success()
            return

        # loop through the values of the variable being checked LCV
        # print("getNextValues(v): " + str(self.getNextValues(v)))
        for i in self.getNextValues(v):
            # print("next value to test --> " + str(i))
            self.trail.placeTrailMarker()

            # check a value
            v.updateDomain(domain.Domain(i))
            self.numAssignments += 1

            # move to the next assignment
            if self.checkConsistency() and self.checkHeuristics():
                self.solveLevel(level + 1)

            # if this assignment failed at any stage, backtrack
            if not self.hassolution:
                # print("=======================================")
                # print("AFTER PROCESSED:")
                # print(self.network)
                # print("================ ")
                # print("self.trail before revert change: ")
                for i in self.trail.trailStack:
                    pass
                    # print("variable --> " + str(i[0]))
                    # print("domain backup --> " + str(i[1]))
                # print("================= ")

                self.trail.undo()
                self.numBacktracks += 1
                # print("REVERT CHANGES:")
                # print(self.network)
                # print("================ ")
                # print("self.trail after revert change: ")
                for i in self.trail.trailStack:
                    pass
                    # print("variable --> " + str(i[0]))
                    # print("domain backup --> " + str(i[1]))
                # print("================= ")

            else:
                return
