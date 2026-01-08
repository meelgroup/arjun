#!/usr/bin/env python3
import sys

def convert_cnf_simple(input_file, output_file):
    with open(input_file, 'r') as f:
        content = f.read().splitlines()

    var_count = 0
    clause_count = 0
    a_vars = []
    e_vars = []
    clauses = []

    for line in content:
        line = line.strip()
        if not line:
            continue

        if line.startswith('p cnf'):
            parts = line.split()
            var_count = int(parts[2])
            clause_count = int(parts[3])
            continue

        if line.startswith('a '):
            parts = line.split()
            a_vars = [int(x) for x in parts[3:] if x != '0']
            continue

        if line.startswith('e '):
            parts = line.split()
            e_vars = [int(x) for x in parts[3:] if x != '0']
            continue

        if not line.startswith('c'):
            clauses.append(line)

    # Prepare output
    output_lines = []
    output_lines.append(f"p cnf {var_count} {clause_count}")

    # Add 'c p show' line (existential variables)
    if a_vars:
        output_lines.append('c p show  ' + ' '.join(str(v) for v in a_vars) + ' 0')

    # Add clauses
    output_lines.extend(clauses)

    # Write output
    with open(output_file, 'w') as f:
        f.write('\n'.join(output_lines))

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python script.py input.cnf output.cnf")
        sys.exit(1)

    convert_cnf_simple(sys.argv[1], sys.argv[2])
    print(f"Converted {sys.argv[1]} to {sys.argv[2]}")
