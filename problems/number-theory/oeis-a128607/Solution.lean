import OMAStatements.S_oeis_a128607
import Mathlib.Tactic.NormNum

open ArithmeticFunction OMA.S_oeis_a128607
open scoped ArithmeticFunction.sigma

private theorem sigmaPrimePower (p e n s : ℕ) (hp : p.Prime) (hn : p ^ e = n)
    (hs : (∑ i ∈ Finset.range (e + 1), p ^ i) = s) : σ 1 n = s :=
  (congrArg (fun v : ℕ => σ 1 v) hn.symm).trans
    ((sigma_one_apply_prime_pow hp).trans hs)

private theorem sigmaProduct (a b n c d s : ℕ) (hn : a * b = n) (hab : a.Coprime b)
    (ha : σ 1 a = c) (hb : σ 1 b = d) (hs : c * d = s) : σ 1 n = s :=
  (congrArg (fun v : ℕ => σ 1 v) hn.symm).trans
    ((isMultiplicative_sigma.map_mul_of_coprime hab).trans
      ((congrArg₂ (· * ·) ha hb).trans hs))

private theorem inputCertificate : σ 1 (424462145606577000 : ℕ) = 1669404572559360000 := by
  have h2 : σ 1 (8 : ℕ) = 15 :=
    sigmaPrimePower 2 3 8 15 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h3 : σ 1 (27 : ℕ) = 40 :=
    sigmaPrimePower 3 3 27 40 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h5 : σ 1 (125 : ℕ) = 156 :=
    sigmaPrimePower 5 3 125 156 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h13 : σ 1 (2197 : ℕ) = 2380 :=
    sigmaPrimePower 13 3 2197 2380 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h41 : σ 1 (68921 : ℕ) = 70644 :=
    sigmaPrimePower 41 3 68921 70644 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h47 : σ 1 (103823 : ℕ) = 106080 :=
    sigmaPrimePower 47 3 103823 106080 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have tail4 : σ 1 (7155584983 : ℕ) = 7493915520 :=
    sigmaProduct 68921 103823 7155584983 70644 106080
      7493915520 (by decide +kernel) (by decide +kernel) h41 h47 (by decide +kernel)
  have tail3 : σ 1 (15720820207651 : ℕ) = 17835518937600 :=
    sigmaProduct 2197 7155584983 15720820207651 2380 7493915520
      17835518937600 (by decide +kernel) (by decide +kernel) h13 tail4 (by decide +kernel)
  have tail2 : σ 1 (1965102525956375 : ℕ) = 2782340954265600 :=
    sigmaProduct 125 15720820207651 1965102525956375 156 17835518937600
      2782340954265600 (by decide +kernel) (by decide +kernel) h5 tail3 (by decide +kernel)
  have tail1 : σ 1 (53057768200822125 : ℕ) = 111293638170624000 :=
    sigmaProduct 27 1965102525956375 53057768200822125 40 2782340954265600
      111293638170624000 (by decide +kernel) (by decide +kernel) h3 tail2 (by decide +kernel)
  exact
    sigmaProduct 8 53057768200822125 424462145606577000 15 111293638170624000
      1669404572559360000 (by decide +kernel) (by decide +kernel) h2 tail1 (by decide +kernel)

private theorem outputCertificate : σ 1 (463608005840717056900 : ℕ) = 1250426685924493640199 := by
  have h2 : σ 1 (4 : ℕ) = 7 :=
    sigmaPrimePower 2 2 4 7 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h5 : σ 1 (25 : ℕ) = 31 :=
    sigmaPrimePower 5 2 25 31 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h7 : σ 1 (49 : ℕ) = 57 :=
    sigmaPrimePower 7 2 49 57 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h29 : σ 1 (841 : ℕ) = 871 :=
    sigmaPrimePower 29 2 841 871 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h37 : σ 1 (1369 : ℕ) = 1407 :=
    sigmaPrimePower 37 2 1369 1407 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h439 : σ 1 (192721 : ℕ) = 193161 :=
    sigmaPrimePower 439 2 192721 193161 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have h653 : σ 1 (426409 : ℕ) = 427063 :=
    sigmaPrimePower 653 2 426409 427063 (by decide +kernel) (by decide +kernel)
      (by norm_num [Finset.sum_range_succ])
  have tail5 : σ 1 (82177968889 : ℕ) = 82491916143 :=
    sigmaProduct 192721 426409 82177968889 193161 427063
      82491916143 (by decide +kernel) (by decide +kernel) h439 h653 (by decide +kernel)
  have tail4 : σ 1 (112501639409041 : ℕ) = 116066126013201 :=
    sigmaProduct 1369 82177968889 112501639409041 1407 82491916143
      116066126013201 (by decide +kernel) (by decide +kernel) h37 tail5 (by decide +kernel)
  have tail3 : σ 1 (94613878743003481 : ℕ) = 101093595757498071 :=
    sigmaProduct 841 112501639409041 94613878743003481 871 116066126013201
      101093595757498071 (by decide +kernel) (by decide +kernel) h29 tail4 (by decide +kernel)
  have tail2 : σ 1 (4636080058407170569 : ℕ) = 5762334958177390047 :=
    sigmaProduct 49 94613878743003481 4636080058407170569 57 101093595757498071
      5762334958177390047 (by decide +kernel) (by decide +kernel) h7 tail3 (by decide +kernel)
  have tail1 : σ 1 (115902001460179264225 : ℕ) = 178632383703499091457 :=
    sigmaProduct 25 4636080058407170569 115902001460179264225 31 5762334958177390047
      178632383703499091457 (by decide +kernel) (by decide +kernel) h5 tail2 (by decide +kernel)
  exact
    sigmaProduct 4 115902001460179264225 463608005840717056900 7 178632383703499091457
      1250426685924493640199 (by decide +kernel) (by decide +kernel) h2 tail1 (by decide +kernel)

theorem OMA.solution : type_of% @OMA.S_oeis_a128607.main := by
  have hi : σ 1 (424462145606577000 : ℕ) = 1292054400 ^ 2 :=
    inputCertificate.trans (by decide +kernel)
  have ho : σ 1 (463608005840717056900 : ℕ) = 10773399 ^ 3 :=
    outputCertificate.trans (by decide +kernel)
  constructor
  · exact ⟨424462145606577000, by decide +kernel, by decide +kernel,
      ⟨751530, 3, by decide +kernel, by decide +kernel, by decide +kernel⟩,
      ⟨1292054400, 2, by decide +kernel, by decide +kernel, hi.symm⟩⟩
  · exact ⟨463608005840717056900, by decide +kernel,
      ⟨21531558370, 2, by decide +kernel, by decide +kernel, by decide +kernel⟩,
      ⟨10773399, 3, by decide +kernel, by decide +kernel, ho.symm⟩⟩
