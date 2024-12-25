import itertools
import re
import numpy
from z3 import *
from time import time as currenttime
import psutil

# Helper function for formatting solver output
def transform_output(d):
    crlf = '\r\n'
    # Combine solution, satisfiability status, and execution time into a formatted string
    s = ''.join(kk + crlf for kk in d['sol'])
    s = d['sat'] + crlf + s + d['mul_sol']
    return crlf + s + crlf + str(d['exe_time']) if 'exe_time' in d else s

# Instance class to hold problem details
class Instance:
    def __init__(self):
        self.number_of_steps = 0  # Number of workflow steps
        self.number_of_users = 0  # Number of users
        self.number_of_constraints = 0  # Total number of constraints
        self.auth = []  # Steps authorized for each user
        self.SOD = []  # Separation-of-duty constraints
        self.BOD = []  # Binding-of-duty constraints
        self.at_most_k = []  # At-most-k constraints
        self.one_team = []  # One-team constraints

# Function to read the problem instance from a file
def read_file(filename):
    def read_attribute(name):
        # Read a named attribute from the file and parse it as an integer
        line = f.readline()
        match = re.match(f'{name}:\s*(\d+)$', line)
        if match:
            return int(match.group(1))
        else:
            raise Exception(f"Could not parse line {line}; expected the {name} attribute")

    instance = Instance()
    with open(filename) as f:
        # Read basic problem details
        instance.number_of_steps = read_attribute("#Steps")
        instance.number_of_users = read_attribute("#Users")
        instance.number_of_constraints = read_attribute("#Constraints")
        instance.auth = [[] for _ in range(instance.number_of_users)]

        # Parse each constraint in the file
        for _ in range(instance.number_of_constraints):
            l = f.readline()

            # Parse authorizations
            if m := re.match(r"Authorisations u(\d+)(?: s\d+)*", l):
                user_id = int(m.group(1))
                steps = [-1]
                for m in re.finditer(r's(\d+)', l):
                    if -1 in steps:
                        steps.remove(-1)
                    steps.append(int(m.group(1)) - 1)
                instance.auth[user_id - 1].extend(steps)
                continue

            # Parse separation-of-duty constraints
            if m := re.match(r"Separation-of-duty s(\d+) s(\d+)", l):
                steps = (int(m.group(1)) - 1, int(m.group(2)) - 1)
                instance.SOD.append(steps)
                continue

            # Parse binding-of-duty constraints
            if m := re.match(r"Binding-of-duty s(\d+) s(\d+)", l):
                steps = (int(m.group(1)) - 1, int(m.group(2)) - 1)
                instance.BOD.append(steps)
                continue

            # Parse at-most-k constraints
            if m := re.match(r"At-most-k (\d+) (s\d+)(?: (s\d+))*", l):
                k = int(m.group(1))
                steps = [int(m.group(1)) - 1 for m in re.finditer(r's(\d+)', l)]
                instance.at_most_k.append((k, steps))
                continue

            # Parse one-team constraints
            if m := re.match(r"One-team\s+(s\d+)(?:\s+s\d+)*(\s+\(u\d+(?:\s+u\d+)*\))+", l):
                steps = [int(step.group(1)) - 1 for step in re.finditer(r's(\d+)', l)]
                teams = []
                for team_match in re.finditer(r'\((u\d+(?:\s+u\d+)*)\)', l):
                    team = [int(user.group(1)) - 1 for user in re.finditer(r'u(\d+)', team_match.group(1))]
                    teams.append(team)
                instance.one_team.append((steps, teams))
                continue

            raise Exception(f'Failed to parse this line: {l}')

    return instance

# Function to solve the workflow satisfiability problem using Z3
def Solver_z3(instance, filename):
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

    # Create Z3 solver
    s = Solver()
    
    # Create Boolean variables for user assignments
    user_assignment = [[Bool(f's{s + 1}_u{u + 1}') 
                       for u in range(instance.number_of_users)] 
                      for s in range(instance.number_of_steps)]

    # Ensure each step is assigned to exactly one user
    for step in range(instance.number_of_steps):
        s.add(Or(user_assignment[step]))  # At least one user is assigned to the step
        s.add(AtMost(*user_assignment[step], 1))  # At most one user is assigned to the step

    # Authorization constraints
    for user in range(instance.number_of_users):
        if instance.auth[user]:
            for step in range(instance.number_of_steps):
                if step not in instance.auth[user]:
                    s.add(Not(user_assignment[step][user]))

    # Separation-of-duty constraints
    for (step1, step2) in instance.SOD:
        s.add(And([Not(And(user_assignment[step1][user], user_assignment[step2][user]))
                for user in range(instance.number_of_users)]))

    # Binding-of-duty constraints
    for (step1, step2) in instance.BOD:
        for user in range(instance.number_of_users):
            s.add(user_assignment[step1][user] == user_assignment[step2][user])

    # At-Most-K constraints
    for (k, steps) in instance.at_most_k: 
        for steps_combination in itertools.combinations(steps, k + 1):    
            is_bool = []   
            for (step1, step2) in itertools.combinations(steps_combination, 2):
                bool_var = Bool(f'Equal_s{step1+1}_s{step2+1}')
                for user in range(instance.number_of_users):
                    s.add(Implies(bool_var, user_assignment[step1][user] == user_assignment[step2][user]))
                is_bool.append(bool_var)
            s.add(Sum([If(b, 1, 0) for b in is_bool]) >= 1)

    # One-team constraints
    for (steps, teams) in instance.one_team:
        team_conditions = []
        for team in teams:
            team_condition = And([Or([user_assignment[step][user] for user in team]) for step in steps])
            team_conditions.append(team_condition)
        s.add(Or(team_conditions))

    # Maximum workload constraint
    max_workload = 10
    for user in range(instance.number_of_users):
        s.add(Sum([If(user_assignment[step][user], 1, 0) 
                  for step in range(instance.number_of_steps)]) <= max_workload)

    # Solve and process results
    start_time = currenttime() * 1000
    process = psutil.Process()
    start_memory = process.memory_info().rss / (1024 ** 2)  # Memory in MB
    result = {
        'sat': 'unsat',
        'sol': [],
        'mul_sol': '',
        'exe_time': 0,
        'memory_usage': 0
    }

    if s.check() == sat:
        result['sat'] = 'Status: Satisfiable'
        m = s.model()
        
        # Extract solution
        solution = []
        for step in range(instance.number_of_steps):
            for user in range(instance.number_of_users):
                if is_true(m.evaluate(user_assignment[step][user])):
                    solution.append(f's{step + 1}: u{user + 1}')
        result['sol'] = solution

        # Check for multiple solutions
        block = []
        for step in range(instance.number_of_steps):
            for user in range(instance.number_of_users):
                if is_true(m.evaluate(user_assignment[step][user])):
                    block.append(Not(user_assignment[step][user]))
                else:
                    block.append(user_assignment[step][user])
        s.add(Or(block))

        if s.check() == sat:
            result['mul_sol'] = f"other solutions exist, 2 solutions found"
        else:
            result['mul_sol'] = "this is the only solution"

    end_time = currenttime() * 1000
    end_memory = process.memory_info().rss / (1024 ** 2)  # Memory in MB

    result['exe_time'] = f'Time taken: {int(end_time - start_time)}ms'
    result['memory_usage'] = f'Memory usage: {end_memory - start_memory:.2f}MB'

    return result

if __name__ == '__main__':
    dpath = 'instances/5-constraint/2.txt'
    inst = read_file(dpath)
    result = Solver_z3(inst, dpath)

    print(f"Instance Tested: {dpath}")
    print("Solver Results:")
    print(f"{result['sat']}")
    for sol in result['sol']:
        print(sol)
    print(result['mul_sol'])
    print(result['exe_time'])
    print(result['memory_usage'])
