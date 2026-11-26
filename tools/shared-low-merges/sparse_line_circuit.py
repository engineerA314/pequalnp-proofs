"""Binary monotone circuits for shared merges and sparse active lines.

The two-witness construction applies to every plane order q and indeed to
any finite incidence system with at least two points per line. On each line
w mark two different points p[w], r[w]. Build A as the OR of all terms
y[w] AND x[p[w]] and B likewise with r[w]. The single gate A OR B is a low
merge at every line, with disjoint singleton operand profiles on that line.
Its entire cone has exactly 4*L-1 gates for L lines. Adding an OR of the
unmarked incidence terms gives an exact circuit on arbitrary inputs. The
marked incidences really need the shared gate in this implementation.

For q = 2**k and N = q*q + q + 1 the base circuit is correct on every
point assignment whenever at most one line is active. Its gate count is
at most 30*q*q. Group the ordinary line inputs y[a,b] by slope a and
separately by intercept b. With one active ordinary line both groups are
one-hot. Encode both values of every address bit by ORs of these groups.
For each x, multiplication by x is a binary linear map in a polynomial
basis. At most k*k dual-rail XORs give all bits of a*x+b. A binary
multiplexer tree then selects the incident point in the column x. The
ordinary points at infinity, vertical lines and line at infinity are
handled directly. No gate implements NOT.

The group ORs cost 2*q*(q-1), the bit encoders at most 2*q*k, the linear
maps at most 6*q*k*k, the column multiplexers 3*q*(q-1), and all other
gates at most q*(q-1) + 8*q + 5. The uniform bound follows from k <= q
and k*k <= 2*q for every k >= 1.

The small prefix can sit in a circuit correct on ALL point and line sets.
Let F denote true incidence, and let B be the OR of the all-points AND
and one term y[w] AND (OR of the points on w) per line. The output A AND B,
where A is the sparse prefix, equals F. Every true incidence forces A by
monotonicity. B accepts just one extra input, all points and no lines,
which A rejects. A itself accepts a false input with two lines, as tested
below, so both operands matter. No OR in B can be a low merge on two lines:
its point-only OR trees have line-independent singleton profiles, and two
points belong to at most one line together. In the final OR tree at most
one leaf has a nonempty singleton profile on each line. Thus EVERY shared
low merge in the exact circuit lies in A, with at most 30*q*q gates in the
union of their cones. In fact the same q-1 binary OR gates joining the
q column answers give q*q*(q-1) genuine new merges. For each of the q*q
ordinary lines there is exactly one point in each column. Before the
column answers are joined, every low wire has at most one alive point on
this line. A wire either uses no point input, or uses points of just one
column, or is an individual primary input. On that line each node of
the OR tree then merges its two disjoint column blocks. Earlier nodes
are descendants of one operand or have disjoint leaves, so these blocks
were in different components. This proves a superlinear count of
genuine uses entirely inside a linear-size cone. The implemented exact
completion has |A| + N*(q+3) gates. Computing the direct line terms for
F and taking their OR takes only N*(q+2)-1 gates.

For two active lines, partition the line labels by each binary digit.
Within each partition run a copy of the base circuit per side and OR
the two results. AND across partitions. An actual incidence survives
every partition by monotonicity. For any pair some digit separates it,
so that partition also rejects every independent input. The cost is
O(N log N). More generally for 2 <= t <= N use t*t buckets per map.
A uniform random map fails to separate a fixed t-set with probability
at most binom(t,2)/(t*t) < 1/2. Among ceil(t log2 N)+1 independent maps
there exists a family separating every t-set, by the union bound over at
most N**t sets. Smaller sets can be extended to size t. The same OR/AND
construction costs O(N*t**3*log N) and is exact for at most t lines.
The arbitrary-t argument is an existence proof for nonuniform circuits.

Run this file to build the actual one- and two-line networks and verify
them against an incidence oracle. For each actual set of active lines
the probes suffice for every point assignment by monotonicity.
"""

from itertools import combinations


def polynomial_remainder(value, divisor):
    while value and value.bit_length() >= divisor.bit_length():
        value ^= divisor << (value.bit_length() - divisor.bit_length())
    return value


def irreducible(k):
    """Find a monic degree-k polynomial with no factor of degree <= k/2."""
    if k < 1:
        raise ValueError("a field degree must be positive")
    for candidate in range((1 << k) + 1, 1 << (k + 1), 2):
        if all(polynomial_remainder(candidate, divisor) for divisor in range(2, 1 << (k // 2 + 1))):
            return candidate
    raise AssertionError("no irreducible polynomial of the requested degree")


def multiply(a, b, modulus):
    product = 0
    while b:
        if b & 1:
            product ^= a
        a <<= 1
        b >>= 1
    return polynomial_remainder(product, modulus)


class Circuit:
    def __init__(self, inputs):
        self.inputs = inputs
        self.gates = []
        self.output = None

    def gate(self, op, left, right):
        index = self.inputs + len(self.gates)
        assert op in ("and", "or")
        assert 0 <= left < index and 0 <= right < index
        self.gates.append((op, left, right))
        return index

    def fold(self, op, wires):
        row = list(wires)
        if not row:
            raise ValueError("an OR or AND tree needs at least one leaf")
        while len(row) > 1:
            pairs = [self.gate(op, row[i], row[i + 1]) for i in range(0, len(row) - 1, 2)]
            row = pairs + (row[-1:] if len(row) % 2 else [])
        return row[0]

    def wires(self, inputs):
        """Each bit is a separate Boolean assignment."""
        assert len(inputs) == self.inputs
        values = list(inputs)
        for op, a, b in self.gates:
            if op == "or":
                values.append(values[a] | values[b])
            else:
                values.append(values[a] & values[b])
        return values

    def evaluate(self, inputs):
        return self.wires(inputs)[self.output]


def xor_rails(circuit, a, b):
    """Return the zero and one indicators from two pairs of indicators."""
    def paired(i, j):
        return circuit.gate("and", a[i], b[j])
    zero = circuit.gate("or", paired(0, 0), paired(1, 1))
    one = circuit.gate("or", paired(0, 1), paired(1, 0))
    return zero, one


def one_line_circuit(k):
    q = 1 << k
    modulus = irreducible(k)
    n = q*q + q + 1
    c = Circuit(2*n)
    ordinary = [[n + a*q + b for b in range(q)] for a in range(q)]
    slopes = [c.fold("or", row) for row in ordinary]
    intercepts = [c.fold("or", col) for col in zip(*ordinary)]

    def encode(groups):
        return [tuple(c.fold("or", (groups[z] for z in range(q) if ((z >> i) & 1) == rail))
                      for rail in (0, 1)) for i in range(k)]

    a_bits, b_bits = encode(slopes), encode(intercepts)
    hits = []
    for x in range(q):
        address = list(b_bits)
        for i in range(k):
            column = multiply(x, 1 << i, modulus)
            for j in range(k):
                if (column >> j) & 1:
                    address[j] = xor_rails(c, address[j], a_bits[i])
        row = [x*q + z for z in range(q)]
        for zero, one in address:
            row = [c.gate("or", c.gate("and", zero, lo), c.gate("and", one, hi))
                   for lo, hi in zip(row[::2], row[1::2])]
        hits.append(row[0])
    ordinary_active = c.fold("or", slopes)
    first_join = len(c.gates)
    some_column = c.fold("or", hits)
    column_joins = range(first_join, len(c.gates))
    affine = c.gate("and", ordinary_active, some_column)
    directions = c.fold("or", (c.gate("and", slopes[a], q*q + a) for a in range(q)))
    vertical_hits = []
    for x in range(q):
        on_vertical = c.fold("or", [x*q + z for z in range(q)] + [n - 1])
        vertical_hits.append(c.gate("and", n + q*q + x, on_vertical))
    infinity = c.gate("and", 2*n - 1, c.fold("or", range(q*q, n)))
    c.output = c.fold("or", [affine, directions, c.fold("or", vertical_hits), infinity])
    assert len(c.gates) <= 30*q*q
    return c, column_joins


def two_line_circuit(base):
    n = base.inputs // 2
    c = Circuit(2*n)
    results = []
    for bit in range((n - 1).bit_length()):
        bucket_outputs = []
        for side in (0, 1):
            # None denotes substitution of a constant zero during construction.
            # Folding it away leaves only binary AND and OR gates in the netlist.
            mapping = list(range(n)) + [n + w if ((w >> bit) & 1) == side else None for w in range(n)]
            for op, a, b in base.gates:
                left, right = mapping[a], mapping[b]
                if left is not None and right is not None:
                    wire = c.gate(op, left, right)
                elif op == "and":
                    wire = None
                else:
                    wire = right if left is None else left
                mapping.append(wire)
            assert mapping[base.output] is not None
            bucket_outputs.append(mapping[base.output])
        results.append(c.fold("or", bucket_outputs))
    c.output = c.fold("and", results)
    return c


def line_point_masks(k):
    """Independent incidence specification using scalar field arithmetic."""
    q, modulus = 1 << k, irreducible(k)
    masks = []
    for a in range(q):
        for b in range(q):
            affine = [x*q + (multiply(a, x, modulus) ^ b) for x in range(q)]
            masks.append(sum(1 << p for p in affine + [q*q + a]))
    for x in range(q):
        masks.append(sum(1 << p for p in [x*q + z for z in range(q)] + [q*q + q]))
    masks.append(sum(1 << p for p in range(q*q, q*q + q + 1)))
    return masks


def two_witness_circuit(point_count, masks):
    """Return an exact circuit and the size of its initial shared cone."""
    c = Circuit(point_count + len(masks))
    first, second, unmarked = [], [], []
    for w, mask in enumerate(masks):
        points = [p for p in range(point_count) if (mask >> p) & 1]
        assert len(points) >= 2
        y = point_count + w
        first.append(c.gate("and", y, points[0]))
        second.append(c.gate("and", y, points[1]))
        unmarked.extend((y, p) for p in points[2:])
    shared = c.gate("or", c.fold("or", first), c.fold("or", second))
    front_size = len(c.gates)
    assert front_size == 4*len(masks) - 1
    c.output = shared
    if unmarked:
        rest = c.fold("or", (c.gate("and", y, p) for y, p in unmarked))
        c.output = c.gate("or", shared, rest)
    return c, front_size


def complete_sparse_prefix(base, masks):
    n = len(masks)
    c = Circuit(base.inputs)
    c.gates = base.gates.copy()
    other = c.fold("and", range(n))
    for w, mask in enumerate(masks):
        points = (p for p in range(n) if (mask >> p) & 1)
        term = c.gate("and", n + w, c.fold("or", points))
        other = c.gate("or", other, term)
    c.output = c.gate("and", base.output, other)
    return c


def singleton_probes(n, covered):
    return [(1 << p) | (((covered >> p & 1) ^ 1) << n) for p in range(n)]


def shared_merges(circuit, masks):
    """Compute the project predicate from its definition on all wires/lines."""
    n = len(masks)
    point_bits = (1 << n) - 1
    negative_probe = 1 << n
    counts = [0]*len(circuit.gates)
    for w, covered in enumerate(masks):
        y = [0]*n
        y[w] = point_bits | negative_probe
        values = circuit.wires(singleton_probes(n, covered) + y)
        for j, (op, left, right) in enumerate(circuit.gates):
            if op != "or" or values[circuit.inputs + j] & negative_probe:
                continue
            a, b = values[left] & point_bits, values[right] & point_bits
            if (a & ~b) and (b & ~a):
                counts[j] += 1
    return counts


def cone_size(circuit, gate_indices):
    roots = {circuit.inputs + j for j in gate_indices}
    size = 0
    for j in reversed(range(len(circuit.gates))):
        if circuit.inputs + j in roots:
            size += 1
            _, left, right = circuit.gates[j]
            roots.update([left, right])
    return size


def verify_new_column_joins(circuit, masks, q, joins):
    """Track the components of earlier low alive sets, as in IsNewLowMerge."""
    n = len(masks)
    assert len(joins) == q - 1
    for w in range(q*q):
        y = [0]*n
        y[w] = (1 << (n + 1)) - 1
        values = circuit.wires(singleton_probes(n, masks[w]) + y)
        # Each component starts at a single point. Primary wires that are
        # low have an empty or singleton profile and cannot join components.
        labels = list(range(n))
        for j in range(joins.stop):
            value = values[circuit.inputs + j]
            if (value >> n) or (value & (value - 1)) == 0:
                assert j not in joins
                continue
            points = value
            met = set()
            while points:
                bit = points & -points
                met.add(labels[bit.bit_length() - 1])
                points ^= bit
            if j in joins:
                assert len(met) == 2
            if len(met) > 1:
                merged = max(met)
                labels = [merged if label in met else label for label in labels]


def verify(circuit, masks, limit):
    n = len(masks)
    full = (1 << (n + 1)) - 1
    # The first n assignments turn on singleton points. The last assignment
    # turns on every point outside the union of the actual active lines.
    checked = 0
    for size in range(limit + 1):
        for active in combinations(range(n), size):
            covered = 0
            y = [0]*n
            for w in active:
                covered |= masks[w]
                y[w] = full
            x = singleton_probes(n, covered)
            assert circuit.evaluate(x + y) == covered, active
            checked += 1
    return checked


def main():
    if not __debug__:
        raise SystemExit("Run Python without -O so the replay assertions are active.")
    for k in (1, 2, 3, 4):
        q = 1 << k
        base, joins = one_line_circuit(k)
        masks = line_point_masks(k)
        n = len(masks)
        assert all(bin(m).count("1") == q + 1 for m in masks)
        assert all(bin(a & b).count("1") == 1 for a, b in combinations(masks, 2))
        exact, size = two_witness_circuit(n, masks)
        assert size >= n + 2*q
        assert cone_size(exact, [size - 1]) == size
        assert shared_merges(exact, masks)[size - 1] == n
        if k == 1:
            assert verify(exact, masks, n) == 1 << n
        one = verify(base, masks, 1)
        # y=0 and y=x+1 both miss (1,1). The base also sees the hybrid y=1.
        inputs = [0]*(2*n)
        inputs[q + 1] = inputs[n] = inputs[n + q + 1] = 1
        assert not ((masks[0] | masks[q + 1]) & (1 << (q + 1)))
        assert base.evaluate(inputs) == 1
        complete = complete_sparse_prefix(base, masks)
        assert len(complete.gates) == len(base.gates) + n*(q + 3)
        assert n*(q + 2) - 1 < len(complete.gates)
        assert complete.evaluate(inputs) == 0
        assert complete.evaluate([1]*n + [0]*n) == 0
        if k == 1:
            assert verify(complete, masks, n) == 1 << n
        counts = shared_merges(complete, masks)
        verify_new_column_joins(complete, masks, q, joins)
        assert all(counts[j] >= q*q for j in joins)
        shared = [j for j, count in enumerate(counts) if count >= 2]
        uses = sum(counts[j] for j in shared)
        front = cone_size(complete, shared)
        assert all(j < len(base.gates) for j in shared)
        assert sum(counts[:len(base.gates)]) >= n*q
        assert uses >= n*q-len(base.gates) and front <= len(base.gates)
        print(f"q={q}, N={n}, exact-circuit shared cone={size}, "
              f"one-line gates={len(base.gates)}, line sets checked={one}")
        print(f"  completed sparse prefix: shared uses={uses}, distinct gates in their cones={front}")
        print(f"  new column joins on ordinary lines={q*q*len(joins)}")
        if k <= 3:
            wrapper = two_line_circuit(base)
            two = verify(wrapper, masks, 2)
            assert wrapper.evaluate(inputs) == 0
            print(f"  two-line gates={len(wrapper.gates)}, line sets checked={two}")


if __name__ == "__main__":
    main()
