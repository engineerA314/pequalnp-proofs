"""Integer coefficient arrays for asymmetric interpolation at zero and one."""
from functools import lru_cache
from math import comb


@lru_cache(None)
def blend(a, b):
    if min(a, b) < 0:
        raise ValueError("Precision must be nonnegative.")
    if a == 0:
        return (1,)
    if b == 0:
        return (0,)
    left, right = blend(a-1, b), blend(a, b-1)
    out = [0]*(max(len(left), len(right))+1)
    for j, coefficient in enumerate(left):
        out[j+1] += coefficient
    for j, coefficient in enumerate(right):
        out[j] += coefficient
        out[j+1] -= coefficient
    return tuple(out)


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value*x + coefficient
    return value


def check():
    tests = 0
    for a in range(1, 9):
        for b in range(1, 9):
            coefficients = blend(a, b)
            assert len(coefficients) == a+b
            assert coefficients[-1] == (-1)**(b-1)*comb(a+b-2, a-1)
            assert not any(coefficients[:a])
            at_one = [sum(comb(t, j)*coefficients[t] for t in range(j, len(coefficients))) for j in range(b)]
            assert at_one == [1]+[0]*(b-1)
            for m in range(1, 25):
                for x in range(-3*m, 3*m+2):
                    value = evaluate(coefficients, x)
                    assert x % m or value % m**a == 0
                    assert (x-1) % m or (value-1) % m**b == 0
                    tests += 1
    print(f"64 asymmetric pairs; {tests} signed integer and modulus checks")
    print(f"precision (2, 3), coefficients in increasing order: {blend(2,3)}")


if __name__ == "__main__":
    check()
