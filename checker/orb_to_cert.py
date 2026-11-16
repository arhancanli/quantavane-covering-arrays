"""Compact orbit file (search coding, point id x q + y) -> the same file in the ca-tools coding (q^2 + x q + y).
Header lines are kept ('best ...' becomes a '#' line); only the representative rows change. Usage: q SRC DST"""
import sys
q = int(sys.argv[1])
with open(sys.argv[2]) as f, open(sys.argv[3], "w") as g:
    for line in f:
        if line.startswith("best"):
            g.write("# " + line)
        elif line[:1].isdigit():
            g.write(" ".join(str(q * q + int(v)) for v in line.split()) + "\n")
        else:
            g.write(line)
