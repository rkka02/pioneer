"""Check all antipodal lifts of a binary quotient by equations over F_2."""
import argparse


def endpoint(n):
    return (1 << n) - (1 << (n.bit_length() - 1))


def check_certificate(r, modulus, pivot, representations):
    """Re-evaluate the integer witnesses and XOR their equations from scratch."""
    powers = [1 << i for i in range(r)]
    parity = [0] * r
    right = 0
    for counts in representations:
        assert len(counts) == r and min(counts) >= 0 and counts[pivot] == 0
        assert sum(counts) == r + 1
        delta = sum(x * (m - 1) for x, m in zip(powers, counts)) - powers[pivot]
        assert delta % modulus == 0
        for i in range(r):
            if i != pivot:
                parity[i] ^= (counts[i] - 1) % 2
        right ^= (delta // modulus) % 2
    assert not any(parity) and right == 1


def audit(r, modulus, pivot):
    """Return a contradiction or a consistent system after all compositions."""
    pivots = {}
    independent = []
    certificate = []
    counts = [0] * r
    target = (1 << r) - 1 + (1 << pivot)
    n = r + 1
    rows = 0

    def insert(mask, rhs):
        nonlocal rows
        rows += 1
        combination = 0
        while mask:
            i = mask.bit_length() - 1
            if i not in pivots:
                source = 1 << len(independent)
                independent.append(tuple(counts))
                pivots[i] = (mask, rhs, source ^ combination)
                return True
            old_mask, old_rhs, sources = pivots[i]
            mask ^= old_mask
            rhs ^= old_rhs
            combination ^= sources
        if rhs:
            certificate.extend(v for j, v in enumerate(independent) if combination >> j & 1)
            certificate.append(tuple(counts))
            return False
        return True

    def visit(i, total, slots, mask, rhs):
        if slots == 0:
            return total != 0 or insert(mask, rhs)
        if i < 0 or total < slots or total > slots << i:
            return True
        v = 1 << i
        if total // v + (total % v).bit_count() > slots:
            return True
        if i == pivot:
            return visit(i - 1, total, slots, mask, rhs)
        if i == 0:
            if total != slots:
                return True
            counts[0] = slots
            ok = insert(mask ^ (slots & 1), rhs)
            counts[0] = 0
            return ok
        half = v // 2
        lower = max(0, (total - slots * half + half - 1) // half)
        for m in range(min(slots, total // v), lower - 1, -1):
            counts[i] = m
            if not visit(i - 1, total - m * v, slots - m, mask ^ ((m & 1) << i), rhs):
                return False
        counts[i] = 0
        return True

    initial_mask = ((1 << r) - 1) ^ (1 << pivot)
    for total in range(target % modulus, n * (1 << (r - 1)) + 1, modulus):
        if not visit(r - 1, total, n, initial_mask, (total - target) // modulus % 2):
            check_certificate(r, modulus, pivot, certificate)
            return rows, certificate
    return rows, None


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--show", type=int, help="show the contradictory counts for this n")
    args = cli.parse_args()
    for n in range(8, 26):
        r = n - 1
        modulus = endpoint(r)
        if 2 * modulus >= endpoint(n):
            print(n, "endpoint doubling reaches the threshold")
            continue
        results = [audit(r, modulus, j) for j in range(r)]
        if any(cert is None for _, cert in results):
            raise RuntimeError(f"consistent system at n={n}")
        lengths = [len(cert) for _, cert in results]
        print(n, modulus, r, sum(rows for rows, _ in results), max(lengths), flush=True)
        if args.show == n:
            for j, (_, cert) in enumerate(results):
                print("pivot", j, "certificate", cert)
