import Birch.WeylAnalyticCount
import Birch.WeylFrequency
import Birch.WeylKernel

/-!
# The fixed-height Weyl estimate from the uniform prime-direction bound

The analytic reciprocal-distance bound, all-block shrinking, and the
auxiliary-prime kernel estimate are combined in the normalization of
Browning–Prendiville, Lemma 3.3. The same uniform direction bound suffices for
both this estimate and completion.
-/

open Filter Finset MvPolynomial
open scoped BigOperators ContDiff

namespace Birch

noncomputable section

private theorem forall₂_replicate_weylBounds {n : ℕ} (hs : List (Fin n → ℤ)) {U : ℝ}
    (hU : 0 ≤ U) (hh : ∀ h ∈ hs, ∀ i, |(h i : ℝ)| ≤ U) :
    List.Forall₂ (fun h R => 0 ≤ R ∧ ∀ i, |(h i : ℝ)| ≤ R) hs (List.replicate hs.length U) := by
  induction hs with
  | nil => exact .nil
  | cons h hs ih =>
    exact .cons ⟨hU, hh h List.mem_cons_self⟩ (ih (fun u hu => hh u (List.mem_cons_of_mem h hu)))

private theorem weylNearTensorBox_eq_kernel_shrunken {n k q : ℕ} (hk : 0 < k) (hq : 0 < q)
    (F : IntForm n) (hF : F.IsHomogeneous (k+1)) {P H α : ℝ} (hP : 0 < P) (hH : 0 < H)
    (a : ℤ) (hcop : a.natAbs.Coprime q)
    (hfreq : ∀ (hs : List (Fin n → ℤ)) (R : List ℝ), hs.length = k →
      List.Forall₂ (fun h U => 0 ≤ U ∧ ∀ i, |(h i : ℝ)| ≤ U) hs R →
      ∀ i, |(weylFrequency hs F i : ℝ)| ≤ H * R.prod) :
    weylNearTensorBox (k := k) F α (fun _ => weylShrunkenHeight k P H |(q : ℝ)*α-a| q)
      (weylShrunkenTolerance k P H |(q : ℝ)*α-a| q) =
      weylKernelBox F k (weylShrunkenHeight k P H |(q : ℝ)*α-a| q) := by
  let U := weylShrunkenHeight k P H |(q : ℝ)*α-a| q
  let δ := weylShrunkenTolerance k P H |(q : ℝ)*α-a| q
  have hU : 0 < U := (weylShrunkenHeight_pos_le k hP hH (abs_nonneg _) (Nat.cast_pos.mpr hq)).1
  have hδ : 0 ≤ δ := by
    dsimp [δ, weylShrunkenTolerance]
    exact le_of_lt (one_div_pos.mpr (mul_pos hP
      (weylShrinkDenominator_pos k hP hH (abs_nonneg _) (Nat.cast_pos.mpr hq))))
  ext t
  rw [mem_weylNearTensorBox, mem_weylKernelBox]
  apply and_congr_right
  intro ht
  have htbox (u : Fin n → ℤ) (hu : u ∈ List.ofFn t) (j : Fin n) : |(u j : ℝ)| ≤ U := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
    exact mem_latticeBox_iff_abs.mp (ht i) j
  constructor
  · intro hnear
    apply (weylFrequency_zero_iff (List.ofFn t) hF (by simp)).mp
    intro j
    obtain ⟨b,hb⟩ := (nearestIntegerDistance_le_iff _ _).mp (hnear j)
    have hh := hfreq (List.ofFn t) (List.replicate (List.ofFn t).length U) (by simp)
      (forall₂_replicate_weylBounds _ hU.le htbox) j
    apply weyl_linear_frequency_zero_of_shrink hk hq hP hH a _ b hcop
    · simpa only [List.prod_replicate, List.length_ofFn] using hh
    · simpa only [mul_comm α] using hb
  · intro hkernel j
    have hz := (weylFrequency_zero_iff (List.ofFn t) hF (by simp)).mpr hkernel j
    simpa [hz, nearestIntegerDistance] using hδ

private theorem weyl_inverse_height_bound {k n q : ℕ} (hk : 0 < k) (hq : 0 < q)
    {P H E : ℝ} (hP : 0 < P) (hH : 0 < H) (hE : 0 ≤ E) :
    ((weylShrunkenHeight k (2*P) H E q)⁻¹)^n ≤
      (2+2*H)^((n:ℝ)/(k:ℝ)) *
        ((P⁻¹)^k + E + (q:ℝ)/P^(k+1) + 1/(q:ℝ))^((n:ℝ)/(k:ℝ)) := by
  let U := weylShrunkenHeight k (2*P) H E q
  let S : ℝ := (P⁻¹)^k + E + (q:ℝ)/P^(k+1) + 1/(q:ℝ)
  let M : ℝ := 2+2*H
  have h2P : 0 < 2*P := by positivity
  have hqR : 0 < (q:ℝ) := Nat.cast_pos.mpr hq
  have hU := (weylShrunkenHeight_pos_le k h2P hH hE hqR).1
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hinv : (2*P)⁻¹ ≤ P⁻¹ := inv_anti₀ hP (by linarith)
  have hpow : (P⁻¹)^k ≤ M*(P⁻¹)^k :=
    le_mul_of_one_le_left (by positivity) (by dsimp [M]; linarith)
  have hE' : 2*H*E ≤ M*E := mul_le_mul_of_nonneg_right (by dsimp [M]; linarith) hE
  have hQbase : (q:ℝ)/(2*P)^(k+1) ≤ (q:ℝ)/P^(k+1) :=
    div_le_div_of_nonneg_left hqR.le (by positivity)
      (pow_le_pow_left₀ hP.le (by linarith) _)
  have hQ : 2*((q:ℝ)/(2*P)^(k+1)) ≤ M*((q:ℝ)/P^(k+1)) :=
    mul_le_mul (by dsimp [M]; linarith) hQbase (by positivity) hM
  have hLast : H/(q:ℝ) ≤ M*(1/(q:ℝ)) := by
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (by dsimp [M]; linarith) hqR.le
  have hb : (U⁻¹)^k ≤ M*S := by
    change ((weylShrunkenHeight k (2*P) H E q)⁻¹)^k ≤ _
    rw [weylShrunkenHeight_inv_pow_eq hk h2P hH hE hqR]
    have hPP := (pow_le_pow_left₀ (by positivity) hinv k).trans hpow
    rw [← mul_div_assoc] at hQ
    calc
      _ ≤ M*(P⁻¹)^k + M*E + M*((q:ℝ)/P^(k+1)) + M*(1/(q:ℝ)) :=
        add_le_add (add_le_add (add_le_add hPP hE') hQ) hLast
      _ = M*S := by dsimp [S]; ring
  have hpowEq : (U⁻¹)^n = ((U⁻¹)^k)^((n:ℝ)/(k:ℝ)) := by
    have he : (k:ℝ)*((n:ℝ)/(k:ℝ)) = n := by field_simp
    rw [← Real.rpow_natCast_mul (inv_nonneg.mpr hU.le), he, Real.rpow_natCast]
  rw [hpowEq, ← Real.mul_rpow hM hS]
  exact Real.rpow_le_rpow (by positivity) hb (by positivity)

/-- Browning–Prendiville's fixed-height Weyl estimate in the form used by the
minor-arc argument, given the uniform prime-direction count. -/
theorem weylEstimate_of_kernelBound {n d σ : ℕ} (hd : 2 ≤ d) (hσ : σ ≤ n)
    (F : IntForm n) (hF : F.IsHomogeneous d)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hkernel : ∃ K > 0, ∀ U : ℝ, 0 ≤ U →
      ((weylKernelBox F (d-1) U).card : ℝ) ≤ K * (1+U)^(n*(d-2)+σ)) :
    WeylEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖) := by
  obtain ⟨l,rfl⟩ : ∃ l, d = l+2 := ⟨d-2, by omega⟩
  let k := l+1
  have hk : 0 < k := Nat.succ_pos l
  have hkd : l+2-1 = k := rfl
  intro ε hε
  obtain ⟨C,hC,hcount⟩ := norm_normalizedSum_pow_le_weylNearTensor hε F hF w hw hwbox
  obtain ⟨K,hK,hkernel⟩ := hkernel
  obtain ⟨H,hH,hcoeff⟩ := abs_weylFrequency_le F k
  let A : ℝ := ((8*n+1 : ℕ) : ℝ)^(2*n) * 10^n
  let M : ℝ := 2+2*H
  let B : ℝ := C * A^k * 2^(n*k) * K
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨B*M^(((n - σ : ℕ):ℝ)/(k:ℝ)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ)] with P hP
  intro α a q hq hcop _
  have hP₀ : 0 < P := by linarith
  have hP₁ : 1 ≤ P := by linarith
  have hqR : 0 < (q:ℝ) := Nat.cast_pos.mpr hq
  let E := |(q:ℝ)*α-a|
  have hE : 0 ≤ E := abs_nonneg _
  let R := 2*P
  let U := weylShrunkenHeight k R H E q
  let θ := U/R
  let δ := weylShrunkenTolerance k R H E q
  have hR : 4 ≤ R := by dsimp [R]; linarith
  have hR₀ : 0 < R := by linarith
  have hU := (weylShrunkenHeight_pos_le k hR₀ hH hE hqR)
  have hθ : 0 < θ := div_pos hU.1 hR₀
  have hθ₁ : θ ≤ 1 := (div_le_one hR₀).mpr hU.2
  have hUeq : θ*R = U := div_mul_cancel₀ _ hR₀.ne'
  have hδeq : θ^k/R = δ :=
    (weylShrunkenTolerance_eq hk hR₀ hH hE hqR).symm
  have hshrink := card_weylNearTensorBox_le_shrink_all (k := k) F α hR hθ hθ₁
  rw [hUeq, hδeq] at hshrink
  have hclose : weylNearTensorBox (k := k) F α (fun _ => U) δ = weylKernelBox F k U := by
    exact weylNearTensorBox_eq_kernel_shrunken hk hq F hF hR₀ hH a hcop hcoeff
  rw [hclose] at hshrink
  have hker := hkernel U hU.1.le
  rw [hkd] at hker
  have hcombine := hshrink.trans
    (mul_le_mul_of_nonneg_left hker (by positivity : 0 ≤ (A/(R⁻¹+θ)^n)^k))
  have hden : 0 < R⁻¹+θ := add_pos (inv_pos.mpr hR₀) hθ
  have hAlign : (R⁻¹+θ)*P = (1+U)/2 := by
    dsimp only [R, θ]
    field_simp
  have hScale : ((A/(R⁻¹+θ)^n)^k) / P^(n*k) = A^k * 2^(n*k)/(1+U)^(n*k) := by
    rw [div_pow, ← pow_mul, div_div, ← mul_pow, hAlign, div_pow, div_div_eq_mul_div]
  have hExpo : n*k = (n*l+σ)+(n-σ) := by
    change n*(l+1)=_
    rw [Nat.mul_succ, Nat.add_assoc, Nat.add_sub_of_le hσ]
  have hb : ‖normalizedSum F w P α‖^(2^k : ℕ) ≤ B * P^ε * (U⁻¹)^(n-σ) := by
    calc
      _ ≤ C*P^ε*((weylNearTensorBox (k := k) F α (fun _ => R) (1/R)).card : ℝ)/P^(n*k) :=
        hcount P hP₁ α
      _ ≤ C*P^ε*(((A/(R⁻¹+θ)^n)^k)*(K*(1+U)^(n*l+σ)))/P^(n*k) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (by simpa [A] using hcombine) (by positivity)) (by positivity)
      _ = C*P^ε*(K*(1+U)^(n*l+σ))*(((A/(R⁻¹+θ)^n)^k)/P^(n*k)) := by ring
      _ = B * P^ε / (1+U)^(n-σ) := by
        rw [hScale]
        dsimp only [B]
        have hsplit : (1+U)^(n*k) = (1+U)^(n*l+σ)*(1+U)^(n-σ) := by
          rw [hExpo, pow_add]
        rw [hsplit]
        have hp : 1+U ≠ 0 := by linarith [hU.1]
        field_simp
      _ ≤ _ := by
        rw [div_eq_mul_inv, ← inv_pow]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (inv_nonneg.mpr (by linarith [hU.1]))
          (inv_anti₀ hU.1 (by linarith)) _
  have hc := weyl_inverse_height_bound (n := n - σ) hk hq hP₀ hH (abs_nonneg ((q:ℝ)*α-a))
  have ht : (P⁻¹)^k = P^(1-((l+2:ℕ):ℝ)) := by
    have h : (1:ℝ)-((l+2:ℕ):ℝ) = -(k:ℝ) := by dsimp [k]; push_cast; ring
    rw [h, Real.rpow_neg hP₀.le, Real.rpow_natCast, inv_pow]
  have hqterm : (q:ℝ)/P^(k+1) = (q:ℝ)*P^(-((l+2:ℕ):ℝ)) := by
    rw [show k+1=l+2 by rfl, Real.rpow_neg hP₀.le, Real.rpow_natCast, div_eq_mul_inv]
  rw [ht, hqterm] at hc
  have hexp : (k:ℝ) = ((l+2:ℕ):ℝ)-1 := by dsimp [k]; push_cast; ring
  rw [hkd]
  have h := hb.trans (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ B*P^ε))
  rw [← hexp]
  exact h.trans_eq (by ring)

/-- The Weyl estimate at a form with bounded reduced gradient dimension. -/
theorem weylEstimate_of_gradientDim {n d σ : ℕ} (hd : 2 ≤ d) (hσ : σ ≤ n)
    (F : IntForm n) (hF : F.IsHomogeneous d) (hgrad : EventualPrimeGradientDimensionLE F σ)
    (w : (Fin n → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (hdir : PrimeDirectionBound n d) :
    WeylEstimate d (n - σ) (fun P α => ‖normalizedSum F w P α‖) :=
  weylEstimate_of_kernelBound hd hσ F hF w hw hwbox
    (exists_card_weylKernelBox_le_of_gradientDim hd hF hσ hgrad hdir)

/-- The Weyl estimate for smooth forms at the full ambient dimension. -/
theorem weylEstimate_of_primeDirectionBound {n d : ℕ} (hd : 2 ≤ d)
    (F : IntForm n) (hF : F.IsHomogeneous d) (hs : ProjectivelySmooth F)
    (w : (Fin n → ℝ) → ℝ) (hw : TransverseWeight F w) (hdir : PrimeDirectionBound n d) :
    WeylEstimate d n (fun P α => ‖normalizedSum F w P α‖) :=
  weylEstimate_of_kernelBound (σ := 0) hd (Nat.zero_le n) F hF w hw.smooth hw.cubeSupported
    (by simpa only [Nat.add_zero] using exists_card_weylKernelBox_le hd hF hs hdir)

end

end Birch
