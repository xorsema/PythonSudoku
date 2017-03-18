import filereader
import gameboard
import variable
import domain
import trail
import constraint
import constraintnetwork
import time
import itertools as it

# dictionary mapping heuristic to number
'''

for example, to set the variable selection heuristic to MRV,
you would say,
self.setVariableSelectionHeuristic(VariableSelectionHeuristic['MinimumRemainingValue'])
this is needed when you have more than one heuristic to break ties or use one over the other in precedence.
you can also manually set the heuristics in the main.py file when reading the parameters
as the primary heuristics to use and then break ties within the functions you implement
It follows similarly to the other heuristics and chekcs
'''
VariableSelectionHeuristic = {'None': 0, 'MRV': 1, 'DH': 2}
ValueSelectionHeuristic = {'None': 0, 'LCV': 1}
ConsistencyCheck = {'None': 0, 'ForwardChecking': 1, 'ArcConsistency': 2}
HeuristicCheck = {'None': 0, 'NKP': 1, 'NKT': 2}


class BTSolver:
    "Backtracking solver"

    ######### Constructors Method #########
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

        self.varHeuristics = 0  # refers to which variable selection heuristic in use(0 means default, 1 means MRV, 2 means DEGREE)
        self.valHeuristics = 0  # refers to which value selection heuristic in use(0 means default, 1 means LCV)
        self.cChecks = 0  # refers to which consistency check will be run(0 for backtracking, 1 for forward checking, 2 for arc consistency)
        self.heuristicChecks = 0
        # self.runCheckOnce = False
        self.tokens = []  # tokens(heuristics to use)

    ######### Modifiers Method #########


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

    ######### Accessors Method #########
    def getSolution(self):
        return self.gameboard

    # @return time required for the solver to attain in seconds
    def getTimeTaken(self):
        return self.endTime - self.startTime

    ######### Helper Method #########
    def checkConsistency(self):
        '''which consistency check to run but it is up to you when implementing the heuristics to break ties using the other heuristics passed in'''
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
            return self.nakedPairs() and self.nakedTriples()
        else:
            return True    

    def assignmentsCheck(self):
        """
            default consistency check. Ensures no two variables are assigned to the same value.
            @return true if consistent, false otherwise.
        """
        for v in self.network.variables:
            if v.isAssigned():
                for vOther in self.network.getNeighborsOfVariable(v):
                    if v.getAssignment() == vOther.getAssignment():
                        return False
        return True

    def nakedPairs(self):
        """
           TODO: Implement naked pairs heuristic.
        """
        pass

    def nakedTriples(self):
        """
           TODO:  Implement naked triples heuristic.
        """
        pass 


    def forwardChecking(self):
        """
           TODO:  Implement forward checking.
        """        
        for v in self.network.variables:
            if v.isAssigned() and v.isModified():
                for u in self.network.getNeighborsOfVariable(v):
                    if u.getAssignment() == v.getAssignment():
                        return False
                    if not u.isAssigned():
                        u.removeValueFromDomain(v.getAssignment())
                        if u.size() == 0:
                            return False
        return True

    def generalAC3(self, queue):
        def revise(a, b):
            revised = False
            sameCount = 0
            for x in a.Values():
                sameCount = 0
                for y in b.Values():
                    if x == y:
                        sameCount += 1
                if sameCount == b.size():
                    a.removeValueFromDomain(x)
                    revised = True
            return revised
        while len(queue) != 0:
            xi, xj = queue.pop(0)
            if revise(xi, xj):
                if xi.size() == 0:
                    return False
                n = self.network.getNeighborsOfVariable(xi)
                n.remove(xj)
                for xk in n:
                    queue.append((xk, xi))
        return True
            
                

    def arcConsistency(self):
        """
            TODO: Implement Maintaining Arc Consistency.
        """
        queue = []
        for a in self.network.variables:
            if a.isAssigned() and a.isModified():
                for b in filter(lambda x: not x.isAssigned(), self.network.getNeighborsOfVariable(a)):
                    queue.append((b, a))
                        
        return self.generalAC3(queue)
        

    def selectNextVariable(self):
        """
            Selects the next variable to check.
            @return next variable to check. null if there are no more variables to check.
        """
        if self.varHeuristics == 0:
            return self.getfirstUnassignedVariable()
        elif self.varHeuristics == 1:
            return self.getMRV()
        elif self.varHeuristics == 2:
            return self.getDegree()
        else:
            return self.getfirstUnassignedVariable()

    def getfirstUnassignedVariable(self):
        """
            default next variable selection heuristic. Selects the first unassigned variable.
            @return first unassigned variable. null if no variables are unassigned.
        """
        for v in self.network.variables:
            if not v.isAssigned():
                return v
        return None

    def getMRV(self):
        """
            TODO: Implement MRV heuristic
            @return variable with minimum remaining values that isn't assigned, null if all variables are assigned.
        """
        notAssigned = []
        theVar = None
        for v in self.network.variables:
            if v.isAssigned():
                continue
            if theVar == None:
                theVar = v
            if v.size() < theVar.size():
                theVar = v
        
        return theVar

    def getDegree(self):
        """
            TODO: Implement Degree heuristic
            @return variable constrained by the most unassigned variables, null if all variables are assigned.
        """
        theVar = None
        theVars = 0
        for v in self.network.variables:
            s = len(filter(lambda x: not x.isAssigned(), self.network.getNeighborsOfVariable(v)))
            if s > theVars:
                theVar = v
        return theVar

    def getNextValues(self, v):
        """
            Value Selection Heuristics. Orders the values in the domain of the variable
            passed as a parameter and returns them as a list.
            @return List of values in the domain of a variable in a specified order.
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
        """
            TODO: LCV heuristic
        """
        var = self.selectNextVariable()
        sameCount = 0
        vals = []
        
        for val in var.Values():
            sameCount = 0
            for v in self.network.getNeighborsOfVariable(var):
                if v.domain.contains(val):
                    sameCount += 1
            vals.append((val, sameCount))
                        
        return sorted(vals, key=lambda y: y[1])

    def success(self):
        """ Called when solver finds a solution """
        self.hassolution = True
        self.gameboard = filereader.ConstraintNetworkToGameBoard(self.network,
                                                                 self.gameboard.N,
                                                                 self.gameboard.p,
                                                                 self.gameboard.q)


    ######### Solver Method #########
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
        contains some comments that can be uncommented for more in depth analysis
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
        if (v == None):
            # print("!!! GETTING IN V == NONE !!!")
            for var in self.network.variables:
                if not var.isAssigned():
                    raise ValueError("Something happened with the variable selection heuristic")
            self.success()
            return

        # loop through the values of the variable being checked LCV
        # print("getNextValues(v): " + str(self.getNextValues(v)))
        for i in self.getNextValues(v):
            # print("next value to test --> " + str(i))
            self.trail.placeTrailMarker()

            # check a value
            # print("-->CALL v.updateDomain(domain.Domain(i)) to start to test next value.")
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
