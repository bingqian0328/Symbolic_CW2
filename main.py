from time import time as currenttime
from ortools.sat.python import cp_model
import re
import itertools
import numpy as np
import numpy
import tkinter as tk  
from tkinter import ttk  
from tkinter import filedialog, messagebox, scrolledtext  
import matplotlib.pyplot as plt
import psutil 

# Helper function to format the solver output
def transform_output(d):
    crlf = '\r\n'
    status = "Status: Satisfiable" if d['sat'] == 'sat' else "Status: Unsatisfiable"
    s = ''.join(kk + crlf for kk in d['sol'])
    s = status + crlf + s + d['mul_sol']
    memory = f"Memory Usage: {d['memory_usage']}"
    return crlf + s + crlf + d['exe_time'] + crlf + memory if 'exe_time' in d else s

# Callback class for printing intermediate solutions
class VarArraySolutionPrinter(cp_model.CpSolverSolutionCallback):
    """Print intermediate solutions."""
    def __init__(self, variables, limit):
        cp_model.CpSolverSolutionCallback.__init__(self)
        self.__variables = variables
        self.__solution_count = 0
        self.__solution_limit = limit

    def on_solution_callback(self):
        self.__solution_count += 1
        # Print each solution found
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

# Class to represent the problem instance
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

    # Read basic problem details
    instance = Instance()
    with open(filename) as f:
        instance.number_of_steps = read_attribute("#Steps")
        instance.number_of_users = read_attribute("#Users")
        instance.number_of_constraints = read_attribute("#Constraints")

        instance.auth = [[] for _ in range(instance.number_of_users)]

        # Parse constraints
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
            
            # Parse Separation-of-Duty constraints
            if m := re.match(r"Separation-of-duty s(\d+) s(\d+)", l):
                steps = (int(m.group(1)) - 1, int(m.group(2)) - 1)
                instance.SOD.append(steps)
                continue
            
            #Parse Binding-of-Duty constraints
            if m := re.match(r"Binding-of-duty s(\d+) s(\d+)", l):
                steps = (int(m.group(1)) - 1, int(m.group(2)) - 1)
                instance.BOD.append(steps)
                continue
            
            # Parse At-most-k constraints
            if m := re.match(r"At-most-k (\d+)((?: s\d+)+)", l):
                k = int(m.group(1))
                steps = [int(step) - 1 for step in re.findall(r's(\d+)', m.group(2))]
                instance.at_most_k.append((k, steps))
                continue

            # Parse One-Team constraints
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

# Function to solve the problem using OR-Tools
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
    for (k, steps) in instance.at_most_k:
        
        # Get each combination of steps for length k + 1
        for steps_combination in itertools.combinations(steps, k + 1):
            
            # to store boolean variables
            is_bool = []
            
            # Generate combinations of step pairs
            for (step1, step2) in itertools.combinations(steps_combination, 2):
                
                # Create a boolean variable to represent equality between assignments of two steps
                bool_var = model.NewBoolVar(f'Equal_s{step1+1}_s{step2+1}')
                
                # Add a constraint that this boolean is true if the two steps are assigned to the same user
                for user in range(instance.number_of_users):
                    model.Add(user_assignment[step1][user] == user_assignment[step2][user]).OnlyEnforceIf(bool_var)
                
                # Append boolean variable to the list
                is_bool.append(bool_var)
            
            # Require at least one of these booleans to be true
            model.Add(sum(is_bool) >= 1)

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
    max_steps_per_user = 10  # Set the maximum steps per user 
    for user in range(instance.number_of_users):
        model.Add(sum(user_assignment[step][user] for step in range(instance.number_of_steps)) <= max_steps_per_user)
     
    # Solve the model
    start_time = currenttime() * 1000 #Execution time in ms
    process = psutil.Process()
    start_memory = process.memory_info().rss / (1024 ** 2)  # Memory in MB
    solver = cp_model.CpSolver()
    solution_printer = VarArraySolutionPrinter(user_assignment, 1000)
    solver.parameters.enumerate_all_solutions = True
    status = solver.Solve(model, solution_printer)
    end_time = currenttime() * 1000#Execution time in ms
    end_memory = process.memory_info().rss / (1024 ** 2)  # Memory in MB

    result = {
        'sat': 'unsat',
        'sol': [],
        'mul_sol': "",
        'exe_time': f'Time taken: {int(end_time - start_time)}ms',
        'memory_usage': f'{end_memory - start_memory:.2f} MB'
    }

    if status in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        result['sat'] = 'sat'
        result['sol'] = [f's{s + 1}: u{u + 1}' for s in range(instance.number_of_steps) for u in range(instance.number_of_users) if solver.Value(user_assignment[s][u])]
        result['mul_sol'] = f'other solutions exist, {solution_printer.solution_count()} solutions found' if solution_printer.solution_count() > 1 else "this is the only solution"

    #Display in terminal just in case GUI does not work
    print(f'\nStatus: {solver.StatusName(status)}')
    print(f'Number of solutions found: {solution_printer.solution_count()}')
    print(f'{result["exe_time"]}')
    print(f'Memory Usage: {result["memory_usage"]}')

    return result

def create_gantt_chart(solution, instance):
    """Create and display a Gantt chart for the step-to-user assignments."""
    if not solution:
        messagebox.showerror("Error", "No solution available to generate Gantt chart. Run the solver first.")
        return

    steps = instance.number_of_steps
    users = instance.number_of_users

    # Parse solution into step-user assignments
    assignments = []
    for sol in solution:
        step, user = map(int, re.findall(r'\d+', sol))
        assignments.append((step - 1, user - 1))

    # Prepare Gantt chart data
    user_colors = plt.cm.get_cmap("tab10", users)  # Use a color map for users
    fig, ax = plt.subplots(figsize=(10, 6))
    
    for step, user in assignments:
        ax.broken_barh([(step, 1)], (user, 0.8), facecolors=user_colors(user))

    # Configure chart
    ax.set_xlabel("Steps")
    ax.set_ylabel("Users")
    ax.set_title("Gantt Chart: Step Assignments to Users")
    ax.set_xticks(range(steps))
    ax.set_yticks(range(users))
    ax.set_yticklabels([f"User {u+1}" for u in range(users)])
    ax.grid(True, which="both", linestyle="--", linewidth=0.5)

    # Show chart
    plt.show()

#Make constraints descriptions in GUI
def show_constraints_description():
    """Display a pop-up window with descriptions of all constraints."""
    description_window = tk.Toplevel()
    description_window.title("Constraints Description")

    constraints_text = (
        "Constraints Implemented:\n\n\n"
        "1. Step-to-user assignment constraints:\n"
        "   - Ensure that each step in the workflow is assigned to exactly one user.\n\n"
        "2. Authorization Constraints:\n"
        "   - Ensure that only authorized users can perform specific steps.\n\n"
        "3. Separation-of-Duty (SOD) Constraints:\n"
        "   - Ensure that certain steps must be performed by different users to avoid conflicts of interest.\n\n"
        "4. Binding-of-Duty (BOD) Constraints:\n"
        "   - Ensure that certain steps must be performed by the same user for consistency.\n\n"
        "5. At-Most-K Constraints:\n"
        "   - Limit the number of steps that can be assigned to the same user within a specific group.\n\n"
        "6. One-Team Constraints:\n"
        "   - Ensure that steps are assigned to users within a specific team or group.\n\n"
        "7. Max Load Constraints:\n"
        "   - ensures a balanced workload distribution by limiting the maximum number of tasks that can be assigned to a single user. .\n"
    )

    text_widget = tk.Text(description_window, wrap=tk.WORD, width=70, height=15, padx=10, pady=10)
    text_widget.insert(tk.END, constraints_text)
    text_widget.config(state=tk.DISABLED)  # Make the text widget read-only
    text_widget.pack(padx=10, pady=10)

    close_button = tk.Button(description_window, text="Close", command=description_window.destroy)
    close_button.pack(pady=5)

#Function to run gui
def run_gui():
    def select_file():
        filename = filedialog.askopenfilename(title="Select an instance file")
        if filename:
            file_path_entry.delete(0, tk.END)
            file_path_entry.insert(0, filename)

    def execute_solver():
        filepath = file_path_entry.get()
        if not filepath:
            messagebox.showerror("Error", "Please select a file")
            return

        try:
            global current_result  # Store result globally for export
            global current_instance  # Store instance globally for Gantt chart
            current_instance = read_file(filepath)
            current_result = Solver(current_instance, filepath)
            output = transform_output(current_result)
            output_text.delete(1.0, tk.END)
            output_text.insert(tk.END, output)  # Includes memory usage
        except Exception as e:
            messagebox.showerror("Error", str(e))


    def export_results():
        if not current_result:
            messagebox.showerror("Error", "No solver results to save. Run the solver first.")
            return

        save_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Text files", "*.txt")],
            title="Save Results As"
        )
        if save_path:
            try:
                instance_name = file_path_entry.get()
                with open(save_path, 'w') as file:
                    file.write(f"Instance Tested: {instance_name}\n")
                    file.write("Solver Results:\n")
                    file.write(transform_output(current_result))
                messagebox.showinfo("Success", f"Results saved successfully to {save_path}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save results: {str(e)}")

    def show_gantt_chart():
        if not current_result or not current_instance:
            messagebox.showerror("Error", "No solution available. Run the solver first.")
            return
        create_gantt_chart(current_result['sol'], current_instance)

    # GUI setup
    root = tk.Tk()
    root.title("WSP Solver GUI")

    # Add heading at the top
    heading = tk.Label(root, text="Workflow Satisfiability Problem Solver (WSP)", font=("Helvetica", 16, "bold"))
    heading.pack(pady=10)

    tk.Label(root, text="Select Instance File:").pack(pady=5)

    file_frame = tk.Frame(root)
    file_frame.pack(pady=5)

    file_path_entry = tk.Entry(file_frame, width=50)
    file_path_entry.pack(side=tk.LEFT)

    browse_button = tk.Button(file_frame, text="Browse", command=select_file)
    browse_button.pack(side=tk.LEFT, padx=5)

    run_button = tk.Button(root, text="Run Solver", command=execute_solver)
    run_button.pack(pady=10)

    constraints_button = tk.Button(root, text="Constraints Description", command=show_constraints_description)
    constraints_button.pack(pady=5)

    export_button = tk.Button(root, text="Save Results", command=export_results)
    export_button.pack(pady=5)

    gantt_button = tk.Button(root, text="Show Gantt Chart", command=show_gantt_chart)
    gantt_button.pack(pady=5)

    tk.Label(root, text="Solver Output:").pack(pady=5)

    output_text = scrolledtext.ScrolledText(root, width=80, height=20)
    output_text.pack(pady=10)

    # Initialize global result variables
    global current_result
    global current_instance
    current_result = None
    current_instance = None

    root.mainloop()


if __name__ == '__main__':
    run_gui()

