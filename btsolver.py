import time
from itertools import combinations, product
from operator import itemgetter

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
    'ArcConsistency': 2
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

        self.varHeuristics = 0
        self.valHeuristics = 0
        self.cChecks = 0
        self.heuristicChecks = 0

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
        else:
            return self.assignmentsCheck()

    def checkHeuristics(self):
        if self.heuristicChecks == 1:
            return self.nakedPairs()
        elif self.heuristicChecks == 2:
            return self.nakedTriples()
        elif self.heuristicChecks == 3:
            return self.nakedPairs() or self.nakedTriples()
        else:
            return True

    def assignmentsCheck(self):
        for v in self.network.variables:
            if v.isAssigned():
                for vOther in self.network.getNeighborsOfVariable(v):
                    if v.getAssignment() == vOther.getAssignment():
                        return False
        return True

    def naked(self, length=2):
        for v in self.network.variables:
            neighbors = self.network.getNeighborsOfVariable(v)
            for n in neighbors:
                if not (v.isAssigned() or n.isAssigned()):
                    vvals = v.Values()
                    nvals = n.Values()
                    if len(vvals) == len(nvals) == length and \
                       set(vvals) == set(nvals):
                        nneighbors = self.network.getNeighborsOfVariable(n)
                        common = [val for val in neighbors
                                  if val in nneighbors]
                        for c in common:
                            for val in vvals:
                                if val in c.Values() and c.domain.size() > 1:
                                    c.removeValueFromDomain(val)
                elif v.getAssignment() == n.getAssignment():
                    return False
        return True

    def nakedPairs(self):
        return self.naked()

    def nakedTriples(self):
        return self.naked(length=3)

    def forwardChecking(self):
        """
           TODO:  Implement forward checking.
        """
        pass

    def arcConsistency(self):
        variables = [var for var in self.network.variables if var.isAssigned()]
        neighbors = map(self.network.getNeighborsOfVariable,
                        variables)
        final = list()
        for v, n in zip(variables, neighbors):
            final.append(product([v], n))
        final = [item for sublist in final for item in sublist]
        for v, n in final:
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
        values = dict()
        domain = v.Values()
        for n in self.network.getNeighborsOfVariable(v):
            domain += n.Values()
        for value in domain:
            values[value] = values.get(value, 0) + 1
        return [x for x, _
                in sorted(values.items(),
                          key=itemgetter(1))]

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
        self.solveLevel(0)
        self.endTime = time.time()
        self.trail.trailStack = []

    def solveLevel(self, level):
        """
        Solver Level
        @param level How deep the solver is in its recursion.
        @throws VariableSelectionException
        contains some comments that can be uncommented
        for more in depth analysis
        """

        if self.hassolution:
            return

        v = self.selectNextVariable()

        if (v is None):
            for var in self.network.variables:
                if not var.isAssigned():
                    raise ValueError(
                        "Something happened with the \
                        variable selection heuristic")
            self.success()
            return

        for i in self.getNextValues(v):
            self.trail.placeTrailMarker()

            v.updateDomain(domain.Domain(i))
            self.numAssignments += 1

            if self.checkConsistency() and self.checkHeuristics():
                self.solveLevel(level + 1)

            if not self.hassolution:
                for i in self.trail.trailStack:
                    pass

                self.trail.undo()
                self.numBacktracks += 1
                for i in self.trail.trailStack:
                    pass

            else:
                return
