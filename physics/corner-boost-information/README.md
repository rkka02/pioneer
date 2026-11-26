# Information encoded in relative boosts at a gravitational corner

[Read the paper (PDF)](main.pdf) · [LaTeX source](main.tex) · [Numerical verifier](verify.py)

A relative boost across a causal-diamond corner changes the phases of area eigenstates. In a time-reflected pair of boundaries, both individual density matrices are identical for every encoded message. Comparing measurements on the two boundaries can nevertheless identify the message from one successfully prepared pair.

The analysis assumes the area-generated boost, the doubled boundary state, and the clock-bounded Schwarzschild area distribution proposed by Chandrasekaran. The paper gives analytical proofs under these inputs. The value $p=257/90$ uses the source's one-loop calculation. [Gravitational input, Eqs. (5.22), (5.63), (5.68), (5.74) and Appendix D.2](https://arxiv.org/abs/2611.34924v1)

## Results

- **Sharp boost threshold.** Let $s_*$ be the clock-imposed area bound in units of $4G_N\hbar$. For fixed $M\ge 2$ and fixed $\eta s_*$, an area filter with nonvanishing limiting success can produce $M$ exactly orthogonal messages in every sufficiently large finite diamond if and only if $\eta s_*>4\pi^2(1-1/M)$.
- **Optimal probability for one bit.** Put $\eta_c=2\pi^2/s_*$ and $\epsilon=1-\eta_c/\eta$. Taking the large-area limit first gives $P_{\rm opt}\sim 2[(p+1)/p]^p\epsilon^p$ as $\epsilon\downarrow0$. The optimal coherent filter accepts a low-area interval of width proportional to $\epsilon$ and a high-area interval of width proportional to $\epsilon^p$ in rescaled area.
- **Four messages.** At step $\eta=8\pi^2/s_*$ a simple filter succeeds with limiting probability $p/2^p=0.39453246\ldots$. The left boundary measures in a Fourier basis and sends the outcome to the right boundary, which can then distinguish the four codewords. The construction assumes coherent access across area sectors.

The paper also derives a lower bound on the area mixing required by the readout, the Rényi crossover of the unfiltered ensemble, and a binary filter obtained from a complex zero of the gluing amplitude. An appendix describes a separate smooth-corner test of uniformly spaced area levels.

## Reproduction

Run the following commands in this directory, using a Python 3.13 environment and Tectonic.

```sh
python -m pip install -r requirements.txt
python -B verify.py
tectonic main.tex
```

The script prints the success probabilities and Gram-matrix residuals, checks the binary optimization against an independent linear program, certifies a complex zero by rational Taylor bounds, and writes the two vector figures used by LaTeX. The discrete spectra used in the numerical checks are constructed examples of the limiting distribution. The finite-dimensional calibration and optimality statements are proved in the paper.

The published calculations were run with Python 3.13.11 and Tectonic 0.17.0. The supplied figure PDFs also allow the manuscript to be compiled directly from the checkout.
