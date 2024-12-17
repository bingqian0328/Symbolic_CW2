from time import time as currenttime
from ortools.sat.python import cp_model
import re
import itertools
import numpy

# Helper function
def transform_output(d):
    crlf = '\r\n'
    s = ''.join(kk + crlf for kk in d['sol'])
    s = d['sat'] + crlf + s + d['mul_sol']
    return crlf + s + crlf + str(d['exe_time']) if 'exe_time' in d else s

class VarArraySolutionPrinter(cp_model.CpSolverSolutionCallback):
    """Print intermediate solutions."""
    def __init__(self, variables, limit):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0
        self.__solution_limit = limit

    def on_solution_callback(self):
        self.__solution_count += 1
        for v in self.__variables:
            for user in range(len(v)):
                if self.Value(v[user]) == 1:
                    print(f'[{v[user]}]', end=' ')
        print()
        if self.__solution_count >= self.__solution_limit:
            print(f'\nStop searching after {self.__solution_limit} solutions found')
            self.StopSearch()

    def solution_count(self):
        return self.__solution_count

class Instance:
    def __init__(self):
        self.number_of_steps = 0
        self.number_of_users = 0
        self.number_of_constraints = 0
        self.auth = []  # List of steps authorized for each user
        self.SOD = []   # Separation-of-duty constraints
        self.BOD = []   # Binding-of-duty constraints
        self.at_most_k = []  # At-most-k constraints
        self.one_team = []   # One-team constraints

# Read input file and parse constraints
def read_file(filename):
    def read_attribute(name):
        line = f.readline()
        match = re.match(f'{name}:\\s*(\\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception(f"Could not parse line {line}; expected the {name} attribute")

    instance = Instance()
    with open(filename) as f:
        instance.number_of_steps = read_attribute("#Steps")
        instance.number_of_users = read_attribute("#Users")
        instance.number_of_constraints = read_attribute("#Constraints")

        instance.auth = [[] for _ in range(instance.number_of_users)]

        for _ in range(instance.number_of_constraints):
            l = f.readline()

            # Parse constraints using the walrus operator
            if m := re.match(r"Authorisations u(\d+)(?: s\d+)*", l):
                user_id = int(m.group(1))
                steps = [-1]
                for m in re.finditer(r's(\d+)', l):
                    if -1 in steps:
                        steps.remove(-1)
                    steps.append(int(m.group(1)) - 1)
                instance.auth[user_id - 1].extend(steps)
                continue

            if m := re.match(r"Separation-of-duty s(\d+) s(\d+)", l):
                steps = (int(m.group(1)) - 1, int(m.group(2)) - 1)
                instance.SOD.append(steps)
                continue

            if m := re.match(r"Binding-of-duty s(\d+) s(\d+)", l):
                steps = (int(m.group(1)) - 1, int(m.group(2)) - 1)
                instance.BOD.append(steps)
                continue

            if m := re.match(r"At-most-k (\d+) (s\d+)(?: (s\d+))*", l):
                k = int(m.group(1))
                steps = [int(m.group(1)) - 1 for m in re.finditer(r's(\d+)', l)]
                instance.at_most_k.append((k, steps))
                continue

            if m := re.match(r"One-team\s+(s\d+)(?: s\d+)* (\((u\d+)*\))*", l):
                steps = [int(m.group(1)) - 1 for m in re.finditer(r's(\d+)', l)]
                teams = []
                for m in re.finditer(r'\((u\d+\s*)+\)', l):
                    team = [int(users.group(1)) - 1 for users in re.finditer(r'u(\d+)', m.group(0))]
                    teams.append(team)
                instance.one_team.append((steps, teams))
                continue

            raise Exception(f'Failed to parse this line: {l}')

    return instance

def Solver(instance, filename):
    print("=====================================================")
    print(f'\tFile: {filename}')
    print(f'\tNumber of Steps: {instance.number_of_steps}')
    print(f'\tNumber of Users: {instance.number_of_users}')
    print(f'\tNumber of Constraints: {instance.number_of_constraints}')
    print(f'\tAuthorisations: {instance.auth}')
    print(f'\tSeparation-of-duty: {instance.SOD}')
    print(f'\tBinding-of-duty: {instance.BOD}')
    print(f'\tAt-most-k: {instance.at_most_k}')
    print(f'\tOne-team: {instance.one_team}')
    print("=====================================================")

    model = cp_model.CpModel()
    user_assignment = [[model.NewBoolVar(f's{s + 1}: u{u + 1}') for u in range(instance.number_of_users)] for s in range(instance.number_of_steps)]

    # Step-to-user assignment constraints
    for step in range(instance.number_of_steps):
        model.AddExactlyOne(user_assignment[step][user] for user in range(instance.number_of_users))

    # Authorization constraints
    for user in range(instance.number_of_users):
        if instance.auth[user]:
            for step in range(instance.number_of_steps):
                if step not in instance.auth[user]:
                    model.Add(user_assignment[step][user] == 0)

    # Separation-of-duty constraints
    for (step1, step2) in instance.SOD:
        for user in range(instance.number_of_users):
            model.Add(user_assignment[step2][user] == 0).OnlyEnforceIf(user_assignment[step1][user])

    # Binding-of-duty constraints
    for (step1, step2) in instance.BOD:
        for user in range(instance.number_of_users):
            model.Add(user_assignment[step2][user] == 1).OnlyEnforceIf(user_assignment[step1][user])

    # At-most-k constraints
    # Loop for every value in the atmostk variable that stores the relevant constraints
    for (k, steps) in instance.at_most_k:
        
        # Get each combination of steps for length k + 1
        for steps_combination in itertools.combinations(steps, k + 1):
            
            # Create a list to hold boolean variables
            is_equal_bool = []
            
            # Generate combinations of step pairs
            for (step1, step2) in itertools.combinations(steps_combination, 2):
                
                # Create a boolean variable to represent equality between assignments of two steps
                bool_var = model.NewBoolVar(f'Equal_s{step1+1}_s{step2+1}')
                
                # Add a constraint that this boolean is true if the two steps are assigned to the same user
                for user in range(instance.number_of_users):
                    model.Add(user_assignment[step1][user] == user_assignment[step2][user]).OnlyEnforceIf(bool_var)
                
                # Append the boolean variable to the list
                is_equal_bool.append(bool_var)
            
            # Require at least one of these booleans to be true
            model.Add(sum(is_equal_bool) >= 1)

    # One-team constraints
    for (steps, teams) in instance.one_team:
        team_flags = [model.NewBoolVar(f'team{t}') for t in range(len(teams))]
        model.AddExactlyOne(team_flags)
        for team_index in range (len(teams)):
            for step in steps:
                for user in teams[team_index]:
                    model.Add(user_assignment[step][user] == 0).OnlyEnforceIf(team_flags[team_index].Not())
            
            #steps cannot be assigned to users that are not listed in team
            users_in_teams = list(numpy.concatenate(teams).flat)
            for step in steps:
                for user in range(instance.number_of_users):
                    if user not in users_in_teams:
                        model.Add(user_assignment[step][user] == 0)

    # Max-load constraint
    max_steps_per_user = 10  # Set the maximum steps per user (this can be made dynamic based on instance)
    for user in range(instance.number_of_users):
        model.Add(sum(user_assignment[step][user] for step in range(instance.number_of_steps)) <= max_steps_per_user)

     # At-Least-One Constraint
    # Ensure every step is assigned to at least one user
    for step in range(instance.number_of_steps):
        model.Add(sum(user_assignment[step][user] for user in range(instance.number_of_users)) >= 1)
     
    # Measure execution time
    start_time = currenttime() * 1000
    solver = cp_model.CpSolver()
    solution_printer = VarArraySolutionPrinter(user_assignment, 1000)
    solver.parameters.enumerate_all_solutions = True
    status = solver.Solve(model, solution_printer)
    end_time = currenttime() * 1000

    result = {
        'sat': 'unsat',
        'sol': [],
        'mul_sol': "",
        'exe_time': f'{end_time - start_time}ms'
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        result['sat'] = 'sat'
        result['sol'] = [f's{s + 1}: u{u + 1}' for s in range(instance.number_of_steps) for u in range(instance.number_of_users) if solver.Value(user_assignment[s][u])]
        result['mul_sol'] = f'other solutions exist, {solution_printer.solution_count()} solutions found' if solution_printer.solution_count() > 1 else "this is the only solution"

    print(f'\nStatus: {solver.StatusName(status)}')
    print(f'Number of solutions found: {solution_printer.solution_count()}')

    return result

if __name__ == '__main__':
    dpath = 'instances/3-constraint/4.txt'
    inst = read_file(dpath)
    result = Solver(inst, dpath)
    output = transform_output(result)
    print(output)
