from z3 import *
import re
import itertools
from time import time as currenttime

# Helper function for formatting output
def transform_output(d):
    crlf = '\r\n'
    s = ''.join(kk + crlf for kk in d['sol'])
    s = d['sat'] + crlf + s + d['mul_sol']
    return crlf + s + crlf + str(d['exe_time']) if 'exe_time' in d else s

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

def run_solver(instance, filename):
    print("=====================================================")
    print(f'\tFile: {filename}')
    print(f'\tNumber of Steps: {instance.number_of_steps}')
    print(f'\tNumber of Users: {instance.number_of_users}')
    print(f'\tNumber of Constraints: {instance.number_of_constraints}')
    print("=====================================================")

    solver = Solver()
    solver.set("timeout", 30000)  # Timeout of 30 seconds
    user_assignment = [[Bool(f's{step}_u{user}') for user in range(instance.number_of_users)]
                       for step in range(instance.number_of_steps)]

    # Step-to-user assignment constraints
    for step in range(instance.number_of_steps):
        solver.add(Or([user_assignment[step][user] for user in range(instance.number_of_users)]))

    # Authorization constraints
    for user, auth_steps in enumerate(instance.auth):
        for step in range(instance.number_of_steps):
            if step not in auth_steps:
                solver.add(Not(user_assignment[step][user]))

    # Optimized Separation-of-duty constraints
    for (step1, step2) in instance.SOD:
        for user in range(instance.number_of_users):
            solver.add(Or(Not(user_assignment[step1][user]), Not(user_assignment[step2][user])))

    # Efficient At-most-k constraints
    for (k, steps) in instance.at_most_k:
        for step in steps:
            solver.add(Sum([If(user_assignment[step][user], 1, 0)
                            for user in range(instance.number_of_users)]) <= k)

        # One-Team constraints
    for (steps, teams) in instance.one_team:
        team_flags = [Bool(f"team_active_{i}") for i in range(len(teams))]
        solver.add(Or(team_flags))  # At least one team must be active

        for i, team in enumerate(teams):
            # If this team is active, all steps must be performed by users in the team
            for step in steps:
                solver.add(Implies(team_flags[i], Or([user_assignment[step][user] for user in team])))
            
            # If this team is active, users outside the team cannot perform the steps
            for step in steps:
                for user in range(instance.number_of_users):
                    if user not in team:
                        solver.add(Implies(team_flags[i], Not(user_assignment[step][user])))

        # Ensure only one team is active
        solver.add(AtMost(*team_flags, 1))


    # Solve the constraints
    start_time = currenttime() * 1000
    result = {'sat': 'unsat', 'sol': [], 'mul_sol': '', 'exe_time': ''}
    if solver.check() == sat:
        model = solver.model()
        result['sat'] = 'sat'
        result['mul_sol'] = 'solution found'
        for step in range(instance.number_of_steps):
            for user in range(instance.number_of_users):
                if is_true(model.evaluate(user_assignment[step][user])):
                    result['sol'].append(f's{step + 1}: u{user + 1}')
    else:
        result['mul_sol'] = 'no solution'

    end_time = currenttime() * 1000
    result['exe_time'] = f'{end_time - start_time:.2f}ms'

    return result

if __name__ == '__main__':
    dpath = 'instances/5-constraint/2.txt'
    inst = read_file(dpath)
    result = run_solver(inst, dpath)
    output = transform_output(result)
    print(output)
