"""Exact algebra for the walk energy in Appendix A. Requires SymPy."""

from math import comb

from sympy import Poly, Rational, cancel, diff, symbols


def equal(label, left, right):
    difference = cancel(left - right)
    if difference != 0:
        raise ArithmeticError(f"{label}: residual {difference}")


def check():
    q, u, v, h, x = symbols("q u v h x")
    half = Rational(1, 2)

    # Applying q*d/dq + 1/2 attaches one factor of j + 1/2 to q^j.
    def weight(series):
        return cancel(q * diff(series, q) + half * series)

    first = weight(1 / (1 - q))
    third = weight(weight(first))
    moment = (h + x) * (h - x)**2 / 2
    cubic = moment / 4 + 3 * h * x * (h + x)
    for scale, ratio in [(h, x/h), (x, h/x)]:
        prefactor = scale**3 * (1 - ratio)**4
        equal("first scalar sum", prefactor * first.subs(q, ratio), moment)
        equal("cubic scalar sum", prefactor * third.subs(q, ratio), cubic)

    # Sum g_j(u)g_j(v) on each branch before taking the mixed derivative.
    product = (u**2 - x)**2 * (v**2 - x)**2
    kernel = (u*v + x) * product / (2 * (u*v - x)**2)
    for scale, ratio in [(u*v, x/(u*v)), (x, u*v/x)]:
        equal("two-point sum", product / scale * first.subs(q, ratio), kernel)
    slope = Rational(3, 2) * (3*h**2 + x**2)
    equal("derivative sum", diff(kernel, u, v).subs(v, u), slope.subs(h, u**2))

    w = 4 - h
    density = (w**2 * (Rational(37, 4)*moment + 3*h*x*(h + x))
               + w**3*slope + 4*h*w*moment - 4*h*w**2*diff(moment, h))
    weighted_kernel = (4 - u**2) * (4 - v**2) * kernel
    energy = (w**2 * (cubic + 9*moment)).subs(h, u**2)
    energy += (4 - u**2) * diff(weighted_kernel, u, v).subs(v, u)
    equal("energy density", energy, density.subs(h, u**2))
    equal("switching value", density.subs(h, x), 24*x**2*(4-x)**2)

    # Each monomial h^i gives the central binomial coefficient after h = u^2.
    value = sum(c * comb(2*i, i) for (i,), c in Poly(density, h).terms())
    equal("return moments", value, (127*x**3 + 94*x**2 - 23*x + 374)/4)
    equal("margin for x >= 1", 143*x**3 - value, (x-1)*(445*x**2 + 351*x + 374)/4)
    if Rational(25, 18) * Rational(22, 7) * 143 >= 25**2:
        raise ArithmeticError("final strict inequality")
    print("Verified both geometric branches, the energy density, the return moments, and the bound.")


if __name__ == "__main__":
    check()
