#include <stdio.h>
#include <stdlib.h>

#include <gmp.h>

int main(void) {
    const char *limit_text = "424462145606577000";
    mpz_t cap, root, n, sigma, prime, power, local;
    mpz_inits(cap, root, n, sigma, prime, power, local, NULL);
    if (mpz_set_str(cap, limit_text, 10) != 0) {
        return EXIT_FAILURE;
    }

    mpz_root(root, cap, 3);
    unsigned bound = mpz_get_ui(root);
    unsigned *spf = calloc((size_t)bound + 1, sizeof(*spf));
    if (spf == NULL) {
        return EXIT_FAILURE;
    }
    for (unsigned p = 2; p <= bound; ++p) {
        if (spf[p] != 0) {
            continue;
        }
        for (unsigned j = p; j <= bound; j += p) {
            if (spf[j] == 0) {
                spf[j] = p;
            }
        }
    }

    unsigned result_mask = 0;
    /* An exponent gcd > 2 is divisible by 4 or by an odd prime. */
    for (unsigned e = 3; e < mpz_sizeinbase(cap, 2); ++e) {
        if (e != 4 && (e % 2 == 0 || spf[e] != e)) {
            continue;
        }
        mpz_root(root, cap, e);
        unsigned largest_base = mpz_get_ui(root);
        for (unsigned b = 2; b <= largest_base; ++b) {
            mpz_set_ui(n, b);
            mpz_pow_ui(n, n, e);
            mpz_set_ui(sigma, 1);
            unsigned remaining = b;
            while (remaining > 1) {
                unsigned p = spf[remaining];
                unsigned multiplicity = 0;
                do {
                    remaining /= p;
                    ++multiplicity;
                } while (remaining % p == 0);

                mpz_set_ui(prime, p);
                mpz_pow_ui(power, prime, e * multiplicity + 1);
                mpz_sub_ui(power, power, 1);
                mpz_divexact_ui(local, power, p - 1);
                mpz_mul(sigma, sigma, local);
            }
            if (mpz_perfect_power_p(sigma) != 0) {
                unsigned bit = 0;
                if (e == 3 && b == 7 && mpz_cmp_ui(sigma, 400) == 0) {
                    bit = 1;
                }
                if (e == 3 && b == 751530 && mpz_cmp(n, cap) == 0) {
                    mpz_set_str(local, "1669404572559360000", 10);
                    if (mpz_cmp(sigma, local) == 0) {
                        bit = 2;
                    }
                }
                if (e == 4 && b == 3 && mpz_cmp_ui(sigma, 121) == 0) {
                    bit = 4;
                }
                if (bit == 0 || (result_mask & bit) != 0) {
                    gmp_fprintf(stderr, "Unexpected result: n=%Zd sigma=%Zd\n", n, sigma);
                    return EXIT_FAILURE;
                }
                result_mask |= bit;
                gmp_printf("n=%Zd sigma=%Zd base=%u exponent=%u\n", n, sigma, b, e);
            }
        }
    }

    free(spf);
    mpz_clears(cap, root, n, sigma, prime, power, local, NULL);
    return result_mask == 7 ? EXIT_SUCCESS : EXIT_FAILURE;
}
