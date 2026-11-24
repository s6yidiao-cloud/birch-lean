import Birch.AffineFrame
import Birch.QuadraticCompleteSums
import Birch.SectionFrame
import Birch.SectionPolynomial
import Birch.TerminalAmplitude
import Birch.TerminalSlice

/-! # Completion of the actual terminal chain sum -/

open Matrix MvPolynomial
open scoped ContDiff Matrix BigOperators

namespace Birch

noncomputable section

/-- Deligne's normalized finite-field estimate with arbitrary lower terms
and a linear Fourier twist. -/
def DeligneTwistedDegree (r : ℕ) : Prop :=
  ∀ (l p : ℕ) [Fact p.Prime] [NeZero p], r < p →
    ∀ (g : IntForm l), g.totalDegree ≤ r →
    (∀ x : Fin l → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i (homogeneousComponent r g)) x = 0) → x = 0) →
    ∀ (a : ℤ), (a : ZMod p) ≠ 0 → ∀ z : Fin l → ℤ,
      ‖twistedCompleteSum g p a z‖ ≤ ((r : ℝ)-1)^l * (p : ℝ)^(-(l : ℝ)/2)

/-- A uniform square-root estimate on a terminal slice. Smooth reduction is
measured in characteristic `p`, and the sum is taken modulo `modulus p`. -/
def UniformTwistedResidueBound (modulus : ℕ → ℕ) (r l : ℕ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ (p : ℕ) [Fact p.Prime] [NeZero (modulus p)], r < p →
    ∀ (g : IntForm l), g.totalDegree ≤ r →
    (∀ x : Fin l → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i (homogeneousComponent r g)) x = 0) → x = 0) →
    ∀ (a : ℤ), (a : ZMod p) ≠ 0 → ∀ z : Fin l → ℤ,
      ‖twistedCompleteSum g (modulus p) a z‖ ≤ D * (modulus p : ℝ)^(-(l : ℝ)/2)

/-- The terminal square-root estimate when the sum is taken modulo the prime. -/
def UniformTwistedPrimeBound (r l : ℕ) : Prop := UniformTwistedResidueBound (fun p => p) r l

/-- The sharp Deligne estimate supplies a uniform square-root constant. -/
theorem uniformTwistedPrimeBound_of_deligneTwistedDegree {r : ℕ} (hr : 2 ≤ r)
    (hDeligne : DeligneTwistedDegree r) (l : ℕ) : UniformTwistedPrimeBound r l := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  exact ⟨((r : ℝ)-1)^l, pow_pos (by linarith) _, hDeligne l⟩

/-- The twisted estimate for quadratics is elementary in this normalization. -/
theorem deligneTwistedDegree_two : DeligneTwistedDegree 2 := by
  intro l p _ _ _ g hg hgrad a ha z
  rw [norm_twistedCompleteSum_quadratic g hg hgrad a ha z]
  norm_num

/-- The degree-specific twisted estimate also supplies the conductor-one input. -/
theorem deligneConductorOne_of_twisted {n d : ℕ} {F : IntForm n} (hF : F.IsHomogeneous d)
    (h : DeligneTwistedDegree d) : DeligneConductorOne d F := by
  intro p hp _ hdp hgrad a ha
  letI : Fact p.Prime := hp
  let a₀ : ℤ := a.val
  have ha₀ : (a₀ : ZMod p) = a := by simp [a₀]
  have htop : ∀ x : Fin n → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i (homogeneousComponent d F)) x = 0) → x = 0 := by
    simpa only [homogeneousComponent_eq_self hF] using fun x => (hgrad x).mp
  have hs := h n p hdp F hF.totalDegree_le htop a₀ (ha₀ ▸ ha) 0
  simpa only [twistedCompleteSum_zero, ha₀] using hs

/-- For a fixed finite family of frames, a smooth section of the top form
gives the full terminal saving. The bound is uniform in the prime, the chain,
the frame, and the frozen lattice coordinates. -/
theorem terminal_chain_bound_of_good_frames_of_uniform_residue_bound {l s d r : ℕ}
    {F : IntForm (l+s)} {w : (Fin (l+s) → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (frames : Finset (Matrix (Fin (l+s)) (Fin (l+s)) ℤ))
    {modulus : ℕ → ℕ} {L : ℝ} (hModulus : 0 < L)
    (hTwisted : UniformTwistedResidueBound modulus r l) :
    ∃ T > 0, ∀ {P Q : ℝ}, 1 ≤ P → 1 ≤ Q → Q ≤ Real.sqrt P →
      ∀ (p : ℕ) [Fact p.Prime] [NeZero (modulus p)], r < p →
      (P/Q)^2 ≤ (modulus p : ℝ) → (modulus p : ℝ) ≤ L*(P/Q)^2 →
      ∀ (m : ℕ → ℤ), (∀ i < d-r, 0 < m i ∧ (m i : ℝ)*differencingHeight (d-r) Q i ≤ P) →
      ∀ (α : ℝ) (a : ℤ), (a : ZMod p) ≠ 0 →
        ∀ (t : ℕ → PolynomialDifferencingState (l+s)) (u : ℕ → Fin (l+s) → ℤ),
          IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
          |(t (d-r)).frequency - (a : ℝ)/(modulus p : ℝ)| ≤ completionRadius d r P Q →
          (∃ A ∈ frames, (A.det : ZMod p) ≠ 0 ∧
            ∀ x : Fin l → AlgebraicClosure (ZMod p),
              (∀ i, evalForm (pderiv i (linearSection (sectionFreeColumns A)
                (homogeneousComponent r (t (d-r)).form))) x = 0) → x = 0) →
          (t (d-r)).magnitude P ≤ T * Q^(-(l : ℝ)) := by
  classical
  obtain ⟨R,hR,hframes⟩ := uniform_affineFrame_bounds frames
  obtain ⟨E,hE,hdecay⟩ := uniform_terminalSliceAmplitude_decay (l := l) hF hrd hw hwbox (2*l) R hR
  obtain ⟨C,hC,hCframes⟩ := uniform_latticeBox_bound_of_slices frames
  obtain ⟨D,hD,htwisted⟩ := hTwisted
  refine ⟨C*(D*E*(4*Real.sqrt L)^l), by positivity, ?_⟩
  intro P Q hP hQ hQmax p _ _ hpr hpL hpU m hm α a ha t u ht hclose hgood
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  let k := d-r
  let g := t k
  let β := g.frequency - (a : ℝ)/(modulus p : ℝ)
  let f (x : Fin (l+s) → ℤ) := (g.weight (scaledPoint P x) : ℂ) *
    phase (g.frequency * ((evalForm g.form x : ℤ) : ℝ))
  have hG : g.form.totalDegree ≤ r := by
    have h := ht.totalDegree_le hF.totalDegree_le (i := k) le_rfl
    exact h.trans (by dsimp [k]; omega)
  have hwG : CubeSupported g.weight := ht.cubeSupported_weight hwbox le_rfl
  have hf (x : Fin (l+s) → ℤ) (hx : x ∉ latticeBox (l+s) P) : f x = 0 := by
    have hwx : g.weight (scaledPoint P x) = 0 := by
      by_contra h
      apply hx
      apply mem_latticeBox_iff_abs.mpr
      intro i
      have hi := (hwG _ h i).le
      change |(x i : ℝ)/P| ≤ 1 at hi
      rw [abs_div, abs_of_pos hPpos, div_le_iff₀ hPpos, one_mul] at hi
      exact hi
    simp [f, hwx]
  obtain ⟨A,hA,hdA,hsmooth⟩ := hgood
  have hd : A.det ≠ 0 := fun hd => hdA (by simp [hd])
  obtain ⟨hL,hAffine⟩ := hframes A hA hd
  obtain ⟨rep,hrep,hsum⟩ := hCframes A hA hd
  change ‖∑ x ∈ latticeBox (l+s) P, f x‖ / P^(l+s) ≤ _
  apply hsum hP hQpos (by positivity) f hf
  intro c v hv
  let L := freeFrameMap A
  let b := frozenFrameOffset A c.val v P
  let U := sectionFreeColumns A
  let offset := sectionFrozenOffset A c.val v
  let weight (x : Fin l → ZMod (modulus p)) :=
    ZMod.stdAddChar ((a : ZMod (modulus p)) *
      residueEval (affineSection U offset g.form) (modulus p) x)
  let amp := terminalSliceAmplitude g P β L b
  obtain ⟨hb,hsupp⟩ := hAffine hP c.val (hrep c) v hv
  obtain ⟨hcont,hcomp,hfourier⟩ := hdecay P Q hPpos hQpos m hm α t u ht β hclose
    L b hL hb (hsupp g.weight hwG)
  have hChar (z : Fin l → ℤ) : ‖((modulus p : ℂ)^l)⁻¹ * ∑ x : Fin l → ZMod (modulus p),
      weight x * phase (∑ i, (z i : ℝ)*((x i).val : ℝ)/(modulus p : ℝ))‖ ≤ D * (modulus p : ℝ)^(-(l : ℝ)/2) := by
    unfold weight
    rw [section_twistedCompleteSum]
    apply htwisted p hpr _ (affineSection_totalDegree_le _ _ _ |>.trans hG) _ a ha z
    simpa only [homogeneousComponent_affineSection U offset g.form hG] using hsmooth
  have hterm (x : Fin l → ℤ) : f (c.val + A *ᵥ Fin.append x v) =
      weight (fun i => (x i : ZMod (modulus p))) * amp (P⁻¹ • latticeVector x) := by
    let y := c.val + A *ᵥ Fin.append x v
    have hscale : scaledPoint P y = P⁻¹ • latticeVector y := by
      ext i
      simp [scaledPoint, latticeVector, div_eq_mul_inv, mul_comm]
    have hmap : b + L (P⁻¹ • latticeVector x) = P⁻¹ • latticeVector y :=
      frozenFrameOffset_add_freeFrameMap A c.val v P x
    have hreal : evalForm g.form (latticeVector y) = ((evalForm g.form y : ℤ) : ℝ) :=
      (evalForm_map (Int.castRingHom ℝ) g.form y).symm
    have hphase : g.frequency * ((evalForm g.form y : ℤ) : ℝ) =
        (a : ℝ)/(modulus p : ℝ) * ((evalForm g.form y : ℤ) : ℝ) +
          β * ((evalForm g.form y : ℤ) : ℝ) := by dsimp [β]; ring
    change f y = _
    unfold f amp terminalSliceAmplitude
    rw [hscale, hmap, smul_smul, mul_inv_cancel₀ hPpos.ne', one_smul, hreal, hphase, phase_add]
    rw [show phase ((a : ℝ)/(modulus p : ℝ) * ((evalForm g.form y : ℤ) : ℝ)) =
      weight (fun i => (x i : ZMod (modulus p))) from phase_evalForm_affineSection_frozen A c.val v g.form a x]
    ring
  simp_rw [hterm]
  exact terminal_slice_bound_of_modulus_range hcont.continuous hcomp hModulus.le hPpos hQpos hQmax
    (modulus p) hpL hpU weight hD.le hE.le le_rfl hChar hfourier

theorem terminal_chain_bound_of_good_frames_of_uniform_twisted {l s d r : ℕ}
    {F : IntForm (l+s)} {w : (Fin (l+s) → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (frames : Finset (Matrix (Fin (l+s)) (Fin (l+s)) ℤ))
    (hTwisted : UniformTwistedPrimeBound r l) :
    ∃ T > 0, ∀ {P Q : ℝ}, 1 ≤ P → 1 ≤ Q → Q ≤ Real.sqrt P →
      ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
      (P/Q)^2 ≤ (p : ℝ) → (p : ℝ) ≤ 2*(P/Q)^2 →
      ∀ (m : ℕ → ℤ), (∀ i < d-r, 0 < m i ∧ (m i : ℝ)*differencingHeight (d-r) Q i ≤ P) →
      ∀ (α : ℝ) (a : ℤ), (a : ZMod p) ≠ 0 →
        ∀ (t : ℕ → PolynomialDifferencingState (l+s)) (u : ℕ → Fin (l+s) → ℤ),
          IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
          |(t (d-r)).frequency - (a : ℝ)/(p : ℝ)| ≤ completionRadius d r P Q →
          (∃ A ∈ frames, (A.det : ZMod p) ≠ 0 ∧
            ∀ x : Fin l → AlgebraicClosure (ZMod p),
              (∀ i, evalForm (pderiv i (linearSection (sectionFreeColumns A)
                (homogeneousComponent r (t (d-r)).form))) x = 0) → x = 0) →
          (t (d-r)).magnitude P ≤ T * Q^(-(l : ℝ)) :=
  terminal_chain_bound_of_good_frames_of_uniform_residue_bound
    hF hrd hw hwbox frames (modulus := fun p => p) (L := 2) (by norm_num) hTwisted

/-- The terminal estimate for a fixed family of frames, using Deligne's bound. -/
theorem terminal_chain_bound_of_good_frames {l s d r : ℕ} {F : IntForm (l+s)}
    {w : (Fin (l+s) → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hr : 2 ≤ r) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    (frames : Finset (Matrix (Fin (l+s)) (Fin (l+s)) ℤ)) (hDeligne : DeligneTwistedDegree r) :
    type_of% (terminal_chain_bound_of_good_frames_of_uniform_twisted hF hrd hw hwbox frames
      (uniformTwistedPrimeBound_of_deligneTwistedDegree hr hDeligne l)) :=
  terminal_chain_bound_of_good_frames_of_uniform_twisted hF hrd hw hwbox frames
    (uniformTwistedPrimeBound_of_deligneTwistedDegree hr hDeligne l)

/-- A bounded smooth linear section of the leading form. Here `l` is the
number of free coordinates. -/
def BoundedSmoothSection {n : ℕ} (p l B : ℕ) [Fact p.Prime] (G : IntForm n) : Prop :=
  ∃ U : Matrix (Fin n) (Fin l) ℤ, (∀ i j, |U i j| ≤ (B : ℤ)) ∧
    ∀ x : Fin l → AlgebraicClosure (ZMod p),
      (∀ i, evalForm (pderiv i (linearSection U G)) x = 0) → x = 0

/-- The empty section has no free variables. -/
theorem boundedSmoothSection_zero {n p B : ℕ} [Fact p.Prime] (G : IntForm n) :
    BoundedSmoothSection p 0 B G := by
  exact ⟨0, fun _ j => j.elim0, fun x _ => Subsingleton.elim x 0⟩

/-- The uniform terminal estimate given the bounded section asserted in the
manuscript. Its bound depends on the entry bound, across all chain and prime choices. -/
theorem terminal_chain_bound_of_bounded_sections_of_uniform_residue_bound {n l d r B : ℕ}
    (hl : l ≤ n) (hB : 1 ≤ B)
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hr : 2 ≤ r) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w)
    {modulus : ℕ → ℕ} {L : ℝ} (hL : 0 < L)
    (hTwisted : UniformTwistedResidueBound modulus r l) :
    ∃ T > 0, ∀ {P Q : ℝ}, 1 ≤ P → 1 ≤ Q → Q ≤ Real.sqrt P →
      ∀ (p : ℕ) [Fact p.Prime] [NeZero (modulus p)], r < p →
      (P/Q)^2 ≤ (modulus p : ℝ) → (modulus p : ℝ) ≤ L*(P/Q)^2 →
      ∀ (m : ℕ → ℤ), (∀ i < d-r, 0 < m i ∧ (m i : ℝ)*differencingHeight (d-r) Q i ≤ P) →
      ∀ (α : ℝ) (a : ℤ), (a : ZMod p) ≠ 0 →
        ∀ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
          IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
          |(t (d-r)).frequency - (a : ℝ)/(modulus p : ℝ)| ≤ completionRadius d r P Q →
          BoundedSmoothSection p l B (homogeneousComponent r (t (d-r)).form) →
          (t (d-r)).magnitude P ≤ T * Q^(-(l : ℝ)) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hl
  let frames := boundedSectionFrames (l+s) B
  obtain ⟨T,hT,hterm⟩ := terminal_chain_bound_of_good_frames_of_uniform_residue_bound (s := s)
    hF hrd hw hwbox frames hL hTwisted
  refine ⟨T,hT,?_⟩
  intro P Q hP hQ hQmax p _ _ hpr hpL hpU m hm α a ha t u ht hclose hsec
  apply hterm hP hQ hQmax p hpr hpL hpU m hm α a ha t u ht hclose
  obtain ⟨U,hU,hs⟩ := hsec
  have hind := linearSection_cols_linearIndependent U _ hr (homogeneousComponent_isHomogeneous _ _) hs
  obtain ⟨A,hA,hcols,hdet⟩ := exists_bounded_integral_section_frame hB U hU hind
  exact ⟨A,hA,hdet,by simpa only [sectionFreeColumns_eq_of_cols A U hcols] using hs⟩

theorem terminal_chain_bound_of_bounded_sections_of_uniform_twisted {n l d r B : ℕ}
    (hl : l ≤ n) (hB : 1 ≤ B)
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hr : 2 ≤ r) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) (hTwisted : UniformTwistedPrimeBound r l) :
    ∃ T > 0, ∀ {P Q : ℝ}, 1 ≤ P → 1 ≤ Q → Q ≤ Real.sqrt P →
      ∀ (p : ℕ) [Fact p.Prime] [NeZero p], r < p →
      (P/Q)^2 ≤ (p : ℝ) → (p : ℝ) ≤ 2*(P/Q)^2 →
      ∀ (m : ℕ → ℤ), (∀ i < d-r, 0 < m i ∧ (m i : ℝ)*differencingHeight (d-r) Q i ≤ P) →
      ∀ (α : ℝ) (a : ℤ), (a : ZMod p) ≠ 0 →
        ∀ (t : ℕ → PolynomialDifferencingState n) (u : ℕ → Fin n → ℤ),
          IsPolynomialDifferencingChain (k := d-r) P Q m F w α t u →
          |(t (d-r)).frequency - (a : ℝ)/(p : ℝ)| ≤ completionRadius d r P Q →
          BoundedSmoothSection p l B (homogeneousComponent r (t (d-r)).form) →
          (t (d-r)).magnitude P ≤ T * Q^(-(l : ℝ)) :=
  terminal_chain_bound_of_bounded_sections_of_uniform_residue_bound
    hl hB hF hr hrd hw hwbox (modulus := fun p => p) (L := 2) (by norm_num) hTwisted

/-- The terminal estimate for bounded smooth sections, using Deligne's bound. -/
theorem terminal_chain_bound_of_bounded_sections {n l d r B : ℕ} (hl : l ≤ n) (hB : 1 ≤ B)
    {F : IntForm n} {w : (Fin n → ℝ) → ℝ} (hF : F.IsHomogeneous d) (hr : 2 ≤ r) (hrd : r ≤ d)
    (hw : ContDiff ℝ ∞ w) (hwbox : CubeSupported w) (hDeligne : DeligneTwistedDegree r) :
    type_of% (terminal_chain_bound_of_bounded_sections_of_uniform_twisted hl hB hF hr hrd hw hwbox
      (uniformTwistedPrimeBound_of_deligneTwistedDegree hr hDeligne l)) :=
  terminal_chain_bound_of_bounded_sections_of_uniform_twisted hl hB hF hr hrd hw hwbox
    (uniformTwistedPrimeBound_of_deligneTwistedDegree hr hDeligne l)

end
end Birch
