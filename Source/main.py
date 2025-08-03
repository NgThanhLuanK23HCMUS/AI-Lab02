from pysat.solvers import Solver
from pysat.card import CardEnc
from itertools import combinations, product,count
from collections import defaultdict, deque
import heapq
import os
import time
class HashiwokakeroCNF:
    def __init__(self, grid):
        self.grid = grid
        self.H = len(grid)
        self.W = len(grid[0])
        self.var_counter = 1
        self.var_map = {}  # (i1,j1,i2,j2,k) -> var
        self.inv_map = {}  # var -> (i1,j1,i2,j2,k)
        self.clauses = []

    def new_aux_var(self):
        self.var_counter += 1
        return self.var_counter

    def is_island(self, i, j):
        return self.grid[i][j] != 0

    def get_islands(self):
        return [(i, j) for i in range(self.H) for j in range(self.W) if self.is_island(i, j)]

    def new_var(self, i1, j1, i2, j2, k):
        if (i1, j1) > (i2, j2):
            i1, j1, i2, j2 = i2, j2, i1, j1
        key = (i1, j1, i2, j2, k)
        if key not in self.var_map:
            var = self.var_counter
            self.var_counter += 1
            self.var_map[key] = var
            self.inv_map[var] = key
        return self.var_map[key]

    def gen_bridge_vars(self):
        islands = self.get_islands()
        for (i, j) in islands:
            for dx, dy in [(0, 1), (1, 0)]:
                ni, nj = i + dx, j + dy
                while 0 <= ni < self.H and 0 <= nj < self.W:
                    if self.is_island(ni, nj):
                        for k in [1, 2]:
                            self.new_var(i, j, ni, nj, k)
                        break
                
                    ni += dx
                    nj += dy

    def no_double_connection(self):
        for (i1, j1, i2, j2, _) in self.var_map:
            v1 = self.var_map.get((i1, j1, i2, j2, 1))
            v2 = self.var_map.get((i1, j1, i2, j2, 2))
            if v1 and v2:
                self.clauses.append([-v1, -v2])

    def degree_constraints(self):
        degree_map = defaultdict(list)

        for (i1, j1, i2, j2, k), var in self.var_map.items():
            degree_map[(i1, j1)].append((var, k))
            degree_map[(i2, j2)].append((var, k))

        for (i, j), edge_vars in degree_map.items():
            if self.grid[i][j] == 0:
                continue

            required = int(self.grid[i][j])
            if not edge_vars:
                print(f"Warning: Island at ({i},{j}) has no edges")
                self.clauses.append([])  # UNSAT
                return

            valid_combinations = []

            for r in range(1, len(edge_vars) + 1):
                for subset in combinations(edge_vars, r):
                    total = sum(k for _, k in subset)
                    if total != required:
                        continue

                    pair_ids = set()
                    valid = True
                    for var, _ in subset:
                        if var not in self.inv_map:
                            valid = False
                            break
                        i1, j1, i2, j2, _ = self.inv_map[var]
                        pair_id = tuple(sorted([(i1, j1), (i2, j2)]))
                        if pair_id in pair_ids:
                            valid = False
                            break
                        pair_ids.add(pair_id)

                    if valid:
                        valid_combinations.append(subset)

            if not valid_combinations:
                print(f"Island at ({i},{j}) has no valid combinations to reach {required} bridges.")
                self.clauses.append([])  # UNSAT
                return

            aux_vars = []
            all_vars_involved = set(var for var, _ in edge_vars)

            for combo in valid_combinations:
                aux = self.new_aux_var()
                aux_vars.append(aux)

                combo_vars = [var for var, _ in combo]

                # (¬v1 ∨ ¬v2 ∨ ... ∨ aux)
                self.clauses.append([aux] + [-v for v in combo_vars])

                # (aux → vi) <=> (¬aux ∨ vi)
                for v in combo_vars:
                    self.clauses.append([-aux, v])

            # Exactly one combination is true
            self.clauses.append(aux_vars)  # At least one
            for i in range(len(aux_vars)):
                for j in range(i + 1, len(aux_vars)):
                    self.clauses.append([-aux_vars[i], -aux_vars[j]])  # At most one

            # Optional (đảm bảo loại bỏ biến không thuộc tổ hợp nào đã chọn)
            # Cách làm: mỗi biến chỉ xuất hiện trong tổ hợp có đúng 1 aux → ta ràng buộc ngược lại
            for var in all_vars_involved:
                related_auxs = []
                for idx, combo in enumerate(valid_combinations):
                    if any(v == var for v, _ in combo):
                        related_auxs.append(aux_vars[idx])
                if related_auxs:
                    self.clauses.append([-var] + related_auxs)
            
    def add_non_crossing_constraints(self):
        for bridge1, var1 in self.var_map.items():
            (x1, y1, x2, y2, _) = bridge1
            for bridge2, var2 in self.var_map.items():
                if var1 >= var2:
                    continue  # Tránh lặp lại
                (x3, y3, x4, y4, _) = bridge2

                if self.crosses((x1, y1), (x2, y2), (x3, y3), (x4, y4)):
                    self.clauses.append([-var1, -var2])

    def crosses(self, a1, a2, b1, b2):
    # Chỉ kiểm tra giao cắt giữa horizontal và vertical
        if self.is_horizontal(a1, a2) and self.is_vertical(b1, b2):
            return (min(a1[0], a2[0]) < b1[0] < max(a1[0], a2[0]) and
                    min(b1[1], b2[1]) < a1[1] < max(b1[1], b2[1]))
        elif self.is_vertical(a1, a2) and self.is_horizontal(b1, b2):
            return (min(b1[0], b2[0]) < a1[0] < max(b1[0], b2[0]) and
                    min(a1[1], a2[1]) < b1[1] < max(a1[1], a2[1]))
        return False

    def is_horizontal(self, p1, p2):
        return p1[1] == p2[1] and p1[0] != p2[0]

    def is_vertical(self, p1, p2):
        return p1[0] == p2[0] and p1[1] != p2[1]

    def is_connected(self, model):
        adj = defaultdict(list)
        for var in model:
            if var > 0 and var in self.inv_map:
                i1, j1, i2, j2, _ = self.inv_map[var]
                adj[(i1, j1)].append((i2, j2))
                adj[(i2, j2)].append((i1, j1))

        islands = self.get_islands()
        visited = set()
        queue = deque([islands[0]])

        while queue:
            node = queue.popleft()
            if node in visited:
                continue
            visited.add(node)
            for neighbor in adj[node]:
                if neighbor not in visited:
                    queue.append(neighbor)

        return len(visited) == len(islands)

    def solve(self,file_path="Output/output.txt"):
        self.gen_bridge_vars()
        self.no_double_connection()
        self.degree_constraints()
        self.add_non_crossing_constraints()

        with Solver(name='glucose3') as solver:
            for clause in self.clauses:
                solver.add_clause(clause)

            #loop until a connected model found
            while solver.solve():
                model = solver.get_model()
                
                if self.is_connected(model):
                    self.display_solution(model)
                    
                    return model
                else:
                    # exclude invalid model from resolutions
                    blocking_clause = [-lit for lit in model]
                    solver.add_clause(blocking_clause)
            
            print("No connected solution found.")

    def display_solution(self, model):
        grid = [[' ' for _ in range(self.W)] for _ in range(self.H)]
        # print("\nCác biến được gán ĐÚNG (True):")
        # for var in model:
        #     if var > 0 and var in self.inv_map:
        #         print(f"var {var}: {self.inv_map[var]}")
        for var in model:
            if var > 0 and var in self.inv_map:
                i1, j1, i2, j2, k = self.inv_map[var]
                if i1 == i2:
                    row = i1
                    for col in range(min(j1, j2) + 1, max(j1, j2)):
                        grid[row][col] = '=' if k == 2 else '-'
                elif j1 == j2:
                    col = j1
                    for row in range(min(i1, i2) + 1, max(i1, i2)):
                        grid[row][col] = '$' if k == 2 else '|'
        for i in range(self.H):
            for j in range(self.W):
                if self.is_island(i, j):
                    grid[i][j] = str(self.grid[i][j])
        print("\nSolution:")
        for row in grid:
            print(' '.join(row))

    def printVar(self):
        for key, var in self.var_map.items():
            i1, j1, i2, j2, k = key
            print(f"Var {var}: ({i1},{j1}) -> ({i2},{j2}) with {k} bridge(s)")

    def print_clauses(self):
        print("Tất cả các mệnh đề (clauses):")
        for idx, clause in enumerate(self.clauses, 1):
            print(f"Clause {idx}: {clause}")

    def display_satisfied_clauses(self, model):
        model_set = set(model)  # để tra nhanh
        print("\nMệnh đề được thỏa mãn:")
        for clause in self.clauses:
            if any(lit in model_set for lit in clause):
                print(clause)

    def to_dimacs_file(self, filename="output.cnf"):
        """
        Ghi các mệnh đề CNF trong self.clauses ra file theo định dạng DIMACS chuẩn.
        """
        with open(filename, "w") as f:
            num_vars = self.var_counter - 1  # Biến bắt đầu từ 1
            num_clauses = len(self.clauses)
            f.write(f"p cnf {num_vars} {num_clauses}\n")
            for clause in self.clauses:
                f.write(" ".join(str(lit) for lit in clause) + " 0\n")

    def unsatisfied_clauses(self, true_vars):
        """
        Trả về danh sách các mệnh đề không được thỏa mãn.

        Args:
            clauses: List[List[int]] — Danh sách các mệnh đề (CNF), ví dụ: [[1, -2], [-1, 3]]
            true_vars: List[int] — Danh sách các biến đúng (được gán True), ví dụ: [1, 3]

        Returns:
            List[List[int]] — Danh sách các mệnh đề không thỏa mãn
        """
        true_vars_set = set(true_vars)
        false_vars_set = set(-v for v in true_vars)

        unsatisfied = []
        for clause in self.clauses:
            satisfied = False
            for literal in clause:
                if literal in true_vars_set:   # biến dương đúng
                    satisfied = True
                    break
                if literal < 0 and -literal not in true_vars_set:  # biến âm đúng (tức biến dương sai)
                    satisfied = True
                    break
            if not satisfied:
                unsatisfied.append(clause)
        return unsatisfied
    
    def solve_by_brute_force(self):
        self.gen_bridge_vars()
        self.no_double_connection()
        self.degree_constraints()
        self.add_non_crossing_constraints()

        all_vars = list(range(1, self.var_counter + 1))
        n = len(all_vars)

        # print(f"→ Brute-force testing {2**n} assignments...")

        for assignment in product([True, False], repeat=n):
            model = [var if val else -var for var, val in zip(all_vars, assignment)]
            
            satisfied = True
            for clause in self.clauses:
                if not any(lit in model for lit in clause):
                    satisfied = False
                    break

            if not satisfied:
                continue

            # Kiểm tra liên thông
            if not self.is_connected(model):
                continue

            self.display_solution(model)
            return model

        print("Brute-force: No solution found.")

    def solve_by_A_star(self):
        self.gen_bridge_vars()
        self.no_double_connection()
        self.degree_constraints()
        self.add_non_crossing_constraints()

        counter = count()
        all_vars = list(range(1, self.var_counter + 1))
        initial_assignment = {}
        
        heap = []
        
        def heuristic(assignment):
            model = [v if assignment.get(v, None) else -v for v in all_vars if v in assignment]
            unsat = 0
            for clause in self.clauses:
                clause_vars = [abs(lit) for lit in clause]
                if all(v in assignment for v in clause_vars):
                    if not any(lit in model for lit in clause):
                        unsat += 1
            return unsat

        heapq.heappush(heap, (0, next(counter), 0, initial_assignment))

        while heap:
            f, _, g, assignment = heapq.heappop(heap)
            
            if len(assignment) == len(all_vars):
                model = [v if assignment[v] else -v for v in all_vars]
                if self.is_connected(model):
                    self.display_solution(model)
                    return model
                continue
            
            for var in all_vars:
                if var not in assignment:
                    for val in [True, False]:
                        new_assign = assignment.copy()
                        new_assign[var] = val

                        model = [v if new_assign.get(v, False) else -v for v in all_vars if v in new_assign]
                        invalid = False
                        for clause in self.clauses:
                            clause_vars = [abs(lit) for lit in clause]
                            if all(v in new_assign for v in clause_vars):
                                if not any(lit in model for lit in clause):
                                    invalid = True
                                    break
                        if invalid:
                            continue

                        g_new = g + 1
                        h_new = heuristic(new_assign)
                        f_new = g_new + h_new

                        heapq.heappush(heap, (f_new, next(counter), g_new, new_assign))
                    break 

        print("A*: No solution found.")

    def solve_by_backtracking(self):
        self.gen_bridge_vars()
        self.no_double_connection()
        self.degree_constraints()
        self.add_non_crossing_constraints()

        all_vars = list(range(1, self.var_counter + 1))
        assignment = [None] * (self.var_counter + 1)  # None: chưa gán

        def is_satisfied_partial():
            model = [v if assignment[v] else -v for v in all_vars if assignment[v] is not None]
            for clause in self.clauses:
                clause_vars = [abs(lit) for lit in clause]
                if all(assignment[v] is not None for v in clause_vars):
                    if not any(lit in model for lit in clause):
                        return False
            return True

        def backtrack(index):
            if index == len(all_vars):
                model = [v if assignment[v] else -v for v in all_vars]
                if not self.is_connected(model):
                    return False
                self.display_solution(model)
                return True

            var = all_vars[index]
            for val in [True, False]:
                assignment[var] = val
                if is_satisfied_partial():
                    if backtrack(index + 1):
                        return True
                assignment[var] = None  # undo

            return False

        if not backtrack(0):
            print("Backtracking: No solution found.")
        model = model = [v if assignment[v] else -v for v in all_vars if assignment[v] is not None]
        return model
    
    def write_solution_to_file(self, model, file_path="Output/output.txt"):
        
        
        if model is None:
            with open(file_path, "w", encoding="utf-8") as f:
                f.write("[]")
            return
        
        # Initialize grid with ' ' (temporary placeholder)
        grid = [[' ' for _ in range(self.W)] for _ in range(self.H)]

        # Mark bridges based on model
        for var in model:
            if var > 0 and var in self.inv_map:
                i1, j1, i2, j2, k = self.inv_map[var]
                if i1 == i2:
                    row = i1
                    for col in range(min(j1, j2) + 1, max(j1, j2)):
                        grid[row][col] = '=' if k == 2 else '-'
                elif j1 == j2:
                    col = j1
                    for row in range(min(i1, i2) + 1, max(i1, i2)):
                        grid[row][col] = '$' if k == 2 else '|'

        # Fill islands with numbers
        for i in range(self.H):
            for j in range(self.W):
                if self.is_island(i, j):
                    grid[i][j] = str(self.grid[i][j])

        # Fill remaining empty cells with "0"
        for i in range(self.H):
            for j in range(self.W):
                if grid[i][j] == ' ':
                    grid[i][j] = '0'

        # Write to file in requested format
            with open(file_path, "w", encoding="utf-8") as f:
                for row in grid:
                    line = "[ " + " , ".join(f'"{cell}"' for cell in row) + " ]\n"
                    f.write(line)

def read_input_file(file_path):
    grid = []
    with open(file_path, "r", encoding="utf-8") as f:
        for line in f:
            # Strip newline and whitespace, then split by comma
            row = [int(cell.strip()) for cell in line.strip().split(',')]
            grid.append(row)
    return grid

# === DEMO ===
# puzzle = [
#     [0, 2, 0, 5, 0, 0, 2],
#     [0, 0, 0, 0, 0, 0, 0],
#     [4, 0, 2, 0, 2, 0, 4],
#     [0, 0, 0, 0, 0, 0, 0],
#     [0, 1, 0, 5, 0, 2, 0],
#     [0, 0, 0, 0, 0, 0, 0],
#     [4, 0, 0, 0, 0, 0, 3]
# ]

# puzzle = [
#     [4, 0, 0, 4, 0, 0],
#     [0, 0, 0, 0, 0, 0],
#     [0, 1, 0, 5, 0, 0],
#     [3, 0, 1, 0, 0, 0],
#     [0, 0, 0, 0, 0, 0],
#     [0, 0, 0, 2, 0, 0]
# ]
# puzzle = [
#     [4,  '=', '=', 4, 0, 0],
#     ['$', 0,   0, '$', 0, 0],
#     ['$', 1,  '_', 4, 0, 0],
#     [3,  '_',  1, '|', 0, 0],
#     [0,   0,   0, '|', 0, 0],
#     [0,   0,   0,  1, 0, 0]
# ]

# puzzle2 = [
#     [2, 0, 2],
#     [0, 0, 0],
#     [2, 0, 2],
# ]

def to_xx(less100) :
    return ("00" + str(less100))[-2:]


# def test():
#     for i in range(1,8):
#         puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
#         solver = HashiwokakeroCNF(puzzle)
#         solver.solve(f'Outputs/output-{to_xx(i)}.txt')

def test():
    for i in range(1,11):
        puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
        solver = HashiwokakeroCNF(puzzle)        
        start_time = time.perf_counter()
        model = solver.solve()
        end_time = time.perf_counter()
        execution_time = end_time - start_time
        print(f"Execution {i} time: {execution_time:.6f} seconds")
        solver.write_solution_to_file(model , f'Outputs/output-{to_xx(i)}.txt')


def testAStar():
    for i in range(1,11):
        puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
        solver = HashiwokakeroCNF(puzzle)        
        start_time = time.perf_counter()
        model = solver.solve_by_A_star()
        end_time = time.perf_counter()
        execution_time = end_time - start_time
        print(f"Execution {i} time: {execution_time:.6f} seconds")
        solver.write_solution_to_file(model , f'Outputs/output-{to_xx(i)}.txt')
    


def testBackTrack():
    for i in range(1,11):
        puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
        solver = HashiwokakeroCNF(puzzle)        
        start_time = time.perf_counter()
        model = solver.solve_by_backtracking()
        end_time = time.perf_counter()
        execution_time = end_time - start_time
        print(f"Execution {i} time: {execution_time:.6f} seconds")
        solver.write_solution_to_file(model , f'Outputs/output-{to_xx(i)}.txt')
    

def testBackTrack():
    for i in range(1, 11):
        puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
        solver = HashiwokakeroCNF(puzzle)        
        start_time = time.perf_counter()
        model = solver.solve_by_backtracking()
        end_time = time.perf_counter()
        execution_time = end_time - start_time
        print(f"Execution {i} time: {execution_time:.6f} seconds")
        solver.write_solution_to_file(model , f'Outputs/output-{to_xx(i)}.txt')


def testBruteForce():
    for i in range(1,11):
        puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
        solver = HashiwokakeroCNF(puzzle)        
        start_time = time.perf_counter()
        model = solver.solve_by_brute_force()
        end_time = time.perf_counter()
        execution_time = end_time - start_time
        print(f"Execution {i} time: {execution_time:.6f} seconds")
        solver.write_solution_to_file(model , f'Outputs/output-{to_xx(i)}.txt')


# solver.solve()

# test brute-force
# solver = HashiwokakeroCNF(puzzle2)
# solver.solve_by_brute_force()

# solver.printVar()l

# solver.print_clauses()
# print(solver.unsatisfied_clauses([2, 3, 6, 7, 10, 12, 14, 16, 18, 19, 22, 24, 26]))

##implemented PYSAT
#test()


def compare ():
    os.system("rm Outputs/*")
    methods = ['solve', 'solve_by_backtracking', 'solve_by_A_star', 'solve_by_brute_force']
    for method in methods:
        print(method)
        # only the 5x5 tests
        for i in range(1,5):
            puzzle = read_input_file(f'Inputs/input-{to_xx(i)}.txt')
            solver = HashiwokakeroCNF(puzzle)        
            start_time = time.perf_counter()
            model = getattr(solver, method)()
            end_time = time.perf_counter()
            execution_time = end_time - start_time
            print(f"Execution of input {i} using {method} time: {execution_time:.6f} seconds")
            solver.write_solution_to_file(model , f'Outputs/output-{to_xx(i)}.txt')


# test()
# testBackTrack()
# testBruteForce()
# testAStar()
compare()