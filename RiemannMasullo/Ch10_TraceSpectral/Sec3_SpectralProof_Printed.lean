module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # Further assertions in the proofs of §10.3 that are false as printed -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "orderAt(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "lineZeros(" χ ", " a ")" => {t : ℝ | 0 < orderAt(χ, shift(a, t))}
local notation "floorCut(" s ")" => Nat.floor ((s - 1) / 2 + 1)

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
As printed: the smallest interval containing the selected ordinates in each active character
can be enlarged at both ends by a common positive amount while still containing exactly
those zeros on the line. The finite selections are stated one character at a time.
See `spectralConvolutionFiniteSum` and ERRATA F178. -/
def Printed.spectralLineSelection_exists_isolatingInterval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty),
      (K : Set ℝ) ⊆ lineZeros(χ ω, a) →
      ∃ ε : ℝ, 0 < ε ∧
        Icc (K.min' hK - ε) (K.max' hK + ε) ∩ lineZeros(χ ω, a) = (K : Set ℝ)

/-- Three ordered critical-line zeros of the ordinary Riemann zeta function suffice
for the interval counterexample. This is a finite consequence of Hardy's theorem. -/
private theorem spectralLineSelection_three_zeta_zeros :
    ∃ u v w : ℝ, u < v ∧ v < w ∧ riemannZeta (shift(1 / 2, u)) = 0 ∧
      riemannZeta (shift(1 / 2, v)) = 0 ∧ riemannZeta (shift(1 / 2, w)) = 0 := by
  sorry

/-- A critical-line zero of ordinary zeta has positive order for the completed
L-function of the trivial rational character. -/
private theorem spectralLineSelection_mem_lineZeros (t : ℝ)
    (ht : riemannZeta (shift(1 / 2, t)) = 0) :
    t ∈ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
  let z : ℂ := shift(1 / 2, t)
  have hre : z.re = 1 / 2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  change 0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z
  rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
  change riemannZeta z = 0 at ht
  rw [← ht]
  exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
Use F = ℚ, the trivial base character and a = 1/2. Let K consist of the first and third
distinct positive critical-line zeta ordinates. The omitted second ordinate lies inside
the closed interval for every ε > 0. -/
theorem Printed.spectralLineSelection_exists_isolatingInterval_false :
    ¬ Printed.spectralLineSelection_exists_isolatingInterval := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(ℚ))
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases h : ω = 1
    · subst ω
      rw [show χ' 1 = 1 from Function.update_self ..]
      rfl
    · simpa [χ', Function.update_of_ne h] using hχ ω
  obtain ⟨u, v, w, huv, hvw, hu, hv, hw⟩ := spectralLineSelection_three_zeta_zeros
  let K : Finset ℝ := {u, w}
  have huK : u ∈ K := by simp [K]
  have hwK : w ∈ K := by simp [K]
  have hzeros : (K : Set ℝ) ⊆ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
    intro t ht
    rcases (show t = u ∨ t = w by simpa [K] using ht) with rfl | rfl
    · exact spectralLineSelection_mem_lineZeros _ hu
    · exact spectralLineSelection_mem_lineZeros _ hw
  have htriv : χ' 1 = 1 := Function.update_self ..
  obtain ⟨ε, hε, hK⟩ := hall ℚ χ' hχ' (1 / 2) 1 K ⟨u, huK⟩ (by simpa only [htriv] using hzeros)
  rw [htriv] at hK
  have hvK : v ∈ (K : Set ℝ) := by
    rw [← hK]
    refine ⟨⟨?_, ?_⟩, spectralLineSelection_mem_lineZeros _ hv⟩
    · exact (sub_le_self _ hε.le).trans ((K.min'_le u huK).trans huv.le)
    · exact hvw.le.trans ((K.le_max' w hwK).trans (le_add_of_nonneg_right hε.le))
  simp [K, huv.ne', hvw.ne] at hvK

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
As printed: in each such interval the number of jets is at most the floor cutoff times the
logarithm of the greater of the absolute values of the endpoints. The count includes all
the orders below the truncated multiplicity of each zero in the interval.
See `spectralConvolutionFiniteSum` and ERRATA F180. -/
def Printed.spectralLineBand_jetCount_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty)
      (ε : ℝ), 0 < ε →
      let l := K.min' hK - ε
      let r := K.max' hK + ε
      Icc l r ∩ lineZeros(χ ω, a) = (K : Set ℝ) →
      ((∑ t ∈ K, min ((orderAt(χ ω, shift(a, t))).untop₀.toNat) floorCut(s) : ℕ) : ℝ) ≤
        (floorCut(s) : ℝ) * Real.log (max |l| |r|)

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
Use F = ℚ, the trivial base character, a = 1/2 and s = 2. Select every distinct positive
critical-line zeta ordinate at most T, for large T, and enlarge by an isolating ε < 1.
The floor cutoff is one. Riemann–von Mangoldt and the positive proportion of simple
critical-line zeros (Bui–Conrey–Young, Theorem 1.1) give ≫ T log T jets from the simple
zeros alone. The printed upper bound is O(log T). -/
theorem Printed.spectralLineBand_jetCount_le_false :
    ¬ Printed.spectralLineBand_jetCount_le := by sorry

section Plancherel

local instance instNormOneLocallyCompactSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C₁(F) := by
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽(F)) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  exact hc.isClosed.locallyCompactSpace

local instance instNormOneHaarSec3SpectralProofPrinted (F : Type) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1

local instance instIdeleClassDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

local instance instNormOneDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C₁(F)) := borel _

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
As printed: in the coordinates induced by the norm section τ, the full Plancherel measure
is the product of ordinary Lebesgue measure in x and the Plancherel measure of the norm-one subgroup.
This is the radial normalization used in the proof of `spectralLineConvolution_trace`
and `spectralStripConvolution_trace` in the paper. See ERRATA F182. -/
def Printed.spectralPlancherelMeasure_eq_radialVolume_prod : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F)),
      (∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ))) →
      ∀ (ν₁ : Measure (PontryaginDual C₁(F))) (ν : Measure (PontryaginDual C𝔽(F))),
        IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁ →
        IsLCAPlancherelMeasure (ideleClassTamagawaMeasure F) ν →
        (volume.prod ν₁).map (fun p : ℝ × PontryaginDual C₁(F) ↦
          e (Multiplicative.ofAdd p.1, p.2)) = ν

/-- The norm section splits the dual of the idele class group into a real line and the dual
of the norm-one classes, with the kernel `exp(ixy)` in `y = log |g|`. -/
private theorem spectralPlancherel_exists_dualEquiv (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)) (hτ : Function.RightInverse τ (ideleClassNorm F)) :
    ∃ e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F),
      ∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ)) := by
  obtain ⟨eR, heR⟩ := exists_realPontryaginDualEquiv
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hκmem (g : C𝔽(F)) : (τ (ideleClassNorm F g))⁻¹ * g ∈ (ideleClassNorm F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ]
    exact inv_mul_cancel _
  let κ : C𝔽(F) →ₜ* C₁(F) :=
    { toFun := fun g ↦ ⟨(τ (ideleClassNorm F g))⁻¹ * g, hκmem g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by
        simp only [Subgroup.coe_mul, map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _)
      continuous_toFun :=
        ((τ.continuous.comp hN).inv.mul continuous_id).subtype_mk _ }
  have hκ (g : C𝔽(F)) : (κ g : C𝔽(F)) = (τ (ideleClassNorm F g))⁻¹ * g := rfl
  let ι : C₁(F) →ₜ* C𝔽(F) := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
  have hpos (g : C𝔽(F)) : (0 : ℝ) < ((ideleClassNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  let Lhom : C𝔽(F) →ₜ* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))
      map_one' := by simp
      map_mul' := fun g h ↦ by
        change Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
        rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos g).ne' (hpos h).ne']
        rfl
      continuous_toFun := continuous_ofAdd.comp
        ((NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦ (hpos g).ne') }
  let expU : Multiplicative ℝ →ₜ* ℝ≥0ˣ :=
    { toFun := fun y ↦ Units.mk0 ⟨Real.exp y.toAdd, (Real.exp_pos _).le⟩
        (fun h ↦ (Real.exp_pos y.toAdd).ne' (congrArg Subtype.val h))
      map_one' := Units.ext (NNReal.eq (by
        change Real.exp 0 = (1 : ℝ)
        exact Real.exp_zero))
      map_mul' := fun y z ↦ Units.ext (NNReal.eq (by
        change Real.exp (y.toAdd + z.toAdd) = Real.exp y.toAdd * Real.exp z.toAdd
        exact Real.exp_add _ _))
      continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
        ((Real.continuous_exp.comp continuous_toAdd).subtype_mk _) }
  have hexpU (y : ℝ) : (((expU (Multiplicative.ofAdd y) : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp y := rfl
  have hexpU_log (t : ℝ≥0ˣ) : expU (Multiplicative.ofAdd (Real.log ((t : ℝ≥0) : ℝ))) = t :=
    Units.ext (NNReal.eq (by
      rw [hexpU]
      exact Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))))
  let Tex : Multiplicative ℝ →ₜ* C𝔽(F) := τ.comp expU
  let sc : Multiplicative ℝ →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (x.toAdd / (2 * Real.pi))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd ((x.toAdd + y.toAdd) / _) = Multiplicative.ofAdd (_ + _)
        rw [add_div]
        rfl
      continuous_toFun := continuous_ofAdd.comp (continuous_toAdd.div_const _) }
  let sc' : Multiplicative ℝ →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (x.toAdd * (2 * Real.pi))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        change Multiplicative.ofAdd ((x.toAdd + y.toAdd) * _) = Multiplicative.ofAdd (_ + _)
        rw [add_mul]
        rfl
      continuous_toFun := continuous_ofAdd.comp (continuous_toAdd.mul continuous_const) }
  have hsc (x : Multiplicative ℝ) : sc (sc' x) = x := by
    change Multiplicative.ofAdd (x.toAdd * (2 * Real.pi) / (2 * Real.pi)) = x
    rw [mul_div_cancel_right₀ _ hπ]; rfl
  have hsc' (x : Multiplicative ℝ) : sc' (sc x) = x := by
    change Multiplicative.ofAdd (x.toAdd / (2 * Real.pi) * (2 * Real.pi)) = x
    rw [div_mul_cancel₀ _ hπ]; rfl
  let P : Multiplicative ℝ →ₜ* PontryaginDual C𝔽(F) :=
    (PontryaginDual.map Lhom).comp ((ContinuousMonoidHom.toContinuousMonoidHom eR).comp sc)
  have hP (x : ℝ) (g : C𝔽(F)) :
      P (Multiplicative.ofAdd x) g =
        Circle.exp (x * Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) := by
    change eR (Multiplicative.ofAdd (x / (2 * Real.pi)))
      (Multiplicative.ofAdd (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))) = _
    rw [heR]
    congr 1
    field_simp
  let fwd : Multiplicative ℝ × PontryaginDual C₁(F) →ₜ* PontryaginDual C𝔽(F) :=
    P.comp (ContinuousMonoidHom.fst _ _) *
      (PontryaginDual.map κ).comp (ContinuousMonoidHom.snd _ _)
  have hfwd (x : ℝ) (ω : PontryaginDual C₁(F)) (g : C𝔽(F)) :
      fwd (Multiplicative.ofAdd x, ω) g =
        Circle.exp (x * Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) * ω (κ g) := by
    change P (Multiplicative.ofAdd x) g * ω (κ g) = _
    rw [hP]
  let bwd : PontryaginDual C𝔽(F) →ₜ* Multiplicative ℝ × PontryaginDual C₁(F) :=
    ContinuousMonoidHom.prod
      (sc'.comp ((ContinuousMonoidHom.toContinuousMonoidHom eR.symm).comp
        (PontryaginDual.map Tex)))
      (PontryaginDual.map ι)
  have hleft : Function.LeftInverse bwd fwd := by
    rintro ⟨x, ω⟩
    obtain ⟨x, rfl⟩ : ∃ x' : ℝ, Multiplicative.ofAdd x' = x := ⟨x.toAdd, rfl⟩
    refine Prod.ext ?_ ?_
    · change sc' (eR.symm (PontryaginDual.map Tex (fwd (Multiplicative.ofAdd x, ω)))) = _
      have hmap : PontryaginDual.map Tex (fwd (Multiplicative.ofAdd x, ω)) =
          eR (sc (Multiplicative.ofAdd x)) := by
        ext1 y
        obtain ⟨y, rfl⟩ : ∃ y' : ℝ, Multiplicative.ofAdd y' = y := ⟨y.toAdd, rfl⟩
        rw [PontryaginDual.map_apply, hfwd]
        change _ = eR (Multiplicative.ofAdd (x / (2 * Real.pi))) (Multiplicative.ofAdd y)
        rw [heR]
        have hNT : ideleClassNorm F (Tex (Multiplicative.ofAdd y)) =
            expU (Multiplicative.ofAdd y) := hτ _
        have hκT : κ (Tex (Multiplicative.ofAdd y)) = 1 := Subtype.ext (by
          rw [hκ, hNT]
          exact inv_mul_cancel _)
        rw [hκT, map_one, mul_one, hNT, hexpU, Real.log_exp]
        congr 1
        field_simp
      rw [hmap, ContinuousMulEquiv.symm_apply_apply, hsc']
    · ext1 k
      change fwd (Multiplicative.ofAdd x, ω) (ι k) = ω k
      have hNk : ideleClassNorm F (ι k) = 1 := k.property
      have hκk : κ (ι k) = k := Subtype.ext (by
        rw [hκ, hNk, map_one, inv_one, one_mul]
        rfl)
      rw [hfwd, hNk, hκk]
      simp
  have hright : Function.RightInverse bwd fwd := by
    intro χ
    ext1 g
    set z := eR.symm (PontryaginDual.map Tex χ) with hz
    have hz' : eR z = PontryaginDual.map Tex χ := by
      rw [hz, ContinuousMulEquiv.apply_symm_apply]
    change P (sc' z) g * (PontryaginDual.map ι χ) (κ g) = χ g
    have hPz : P (sc' z) g = χ (τ (ideleClassNorm F g)) := by
      change eR (sc (sc' z)) (Lhom g) = _
      rw [hsc, hz', PontryaginDual.map_apply]
      change χ (τ (expU (Multiplicative.ofAdd (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))))) = _
      rw [hexpU_log]
    rw [hPz, PontryaginDual.map_apply, ← map_mul]
    congr 1
    change τ (ideleClassNorm F g) * ((τ (ideleClassNorm F g))⁻¹ * g) = g
    exact mul_inv_cancel_left _ _
  let e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F) :=
    { toFun := fwd
      invFun := bwd
      left_inv := hleft
      right_inv := hright
      map_mul' := map_mul fwd
      continuous_toFun := fwd.continuous
      continuous_invFun := bwd.continuous }
  refine ⟨e, fun x ω r k ↦ ?_⟩
  change fwd (Multiplicative.ofAdd x, ω) (τ r * k.val) = _
  have hNr : ideleClassNorm F (τ r * k.val) = r := by
    rw [map_mul, hτ, MonoidHom.mem_ker.mp k.property, mul_one]
  have hκr : κ (τ r * k.val) = k := Subtype.ext (by
    rw [hκ, hNr]
    exact inv_mul_cancel_left _ _)
  rw [hfwd, hNr, hκr, mul_comm]

/-- In logarithmic norm coordinates the idele class measure is the mass of the norm-one
classes times Lebesgue measure: Haar uniqueness on ℝ, normalized by Weil's formula. -/
private theorem spectralPlancherel_map_logNorm (F : Type) [Field F] [NumberField F] :
    (ideleClassTamagawaMeasure F).map (fun g ↦ Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)) =
      normOneIdeleClassTamagawaMeasure F univ • volume := by
  let μ := ideleClassTamagawaMeasure F
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let L : C𝔽(F) → ℝ := fun g ↦ Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hpos (g : C𝔽(F)) : (0 : ℝ) < ((ideleClassNorm F g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦ (hpos g).ne'
  have hLmul (g h : C𝔽(F)) : L (g * h) = L g + L h := by
    change Real.log _ = Real.log _ + Real.log _
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos g).ne' (hpos h).ne']
  obtain ⟨τ, hτc, hτ⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.2.1
  let expU : ℝ → ℝ≥0ˣ := fun y ↦ Units.mk0 ⟨Real.exp y, (Real.exp_pos y).le⟩
    (fun h ↦ (Real.exp_pos y).ne' (congrArg Subtype.val h))
  have hexpU : Continuous expU := Units.isEmbedding_val₀.continuous_iff.mpr
    (Real.continuous_exp.subtype_mk _)
  have hLτ (y : ℝ) : L (τ (expU y)) = y := by
    change Real.log (((ideleClassNorm F (τ (expU y)) : ℝ≥0ˣ) : ℝ≥0) : ℝ) = y
    rw [hτ]
    exact Real.log_exp y
  have hexpL (g : C𝔽(F)) : expU (L g) = ideleClassNorm F g :=
    Units.ext (NNReal.eq (Real.exp_log (hpos g)))
  -- Preimages of compact sets under the log norm are compact.
  have hLcpt {K : Set ℝ} (hK : IsCompact K) : IsCompact (L ⁻¹' K) := by
    refine ((isProperMap_ideleClassNorm F).isCompact_preimage (hK.image hexpU)).of_isClosed_subset
      (hK.isClosed.preimage hL) fun g hg ↦ ⟨L g, hg, hexpL g⟩
  -- The pushforward is translation invariant and finite on compacts.
  let μ' := μ.map L
  have hinv : μ'.IsAddLeftInvariant := ⟨fun a ↦ by
    change (μ.map L).map (a + ·) = μ.map L
    rw [Measure.map_map (measurable_const_add a) hL.measurable]
    have hcomp : (a + ·) ∘ L = L ∘ (τ (expU a) * ·) := funext fun g ↦ by
      change a + L g = L (τ (expU a) * g)
      rw [hLmul, hLτ]
    rw [hcomp, ← Measure.map_map hL.measurable (measurable_const_mul _), map_mul_left_eq_self]⟩
  have hfin : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK ↦ by
    rw [Measure.map_apply hL.measurable hK.measurableSet]
    exact (hLcpt hK).measure_lt_top⟩
  have hscale : μ' = Measure.addHaarScalarFactor μ' volume • volume :=
    Measure.isAddLeftInvariant_eq_smul μ' volume
  set c := Measure.addHaarScalarFactor μ' volume with hc
  -- A positive bump in log norm coordinates fixes the constant.
  let G : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hGc : Continuous G := G.continuous
  have hGs : HasCompactSupport G := G.hasCompactSupport
  have hGpos : 0 < ∫ y, G y := G.integral_pos
  let : μ₁.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  let : CompactSpace C₁(F) := (ideleClassGroup_finiteness F).2.1
  have hLker (k : C₁(F)) : L k.val = 0 := by
    change Real.log (((ideleClassNorm F k.val : ℝ≥0ˣ) : ℝ≥0) : ℝ) = 0
    rw [MonoidHom.mem_ker.mp k.property]
    simp
  let f : C(C𝔽(F), ℂ) := ⟨fun g ↦ ((G (L g) : ℝ) : ℂ), Complex.continuous_ofReal.comp (hGc.comp hL)⟩
  have hfs : HasCompactSupport f := by
    refine IsCompact.of_isClosed_subset (hLcpt hGs.isCompact) (isClosed_tsupport _) ?_
    refine closure_minimal (fun g hg ↦ subset_tsupport _ fun h ↦ hg ?_)
      ((isClosed_tsupport _).preimage hL)
    change ((G (L g) : ℝ) : ℂ) = 0
    rw [h, Complex.ofReal_zero]
  have hWeil := (normOneIdeleClassTamagawaMeasure_isWeil F).2.2 f hfs
  have hcoset (x : C𝔽(F)) : lcaCosetIntegral C₁(F) μ₁ f (x : C𝔽(F) ⧸ C₁(F)) =
      (μ₁.real univ : ℂ) * ((G (L x) : ℝ) : ℂ) := by
    have hconst : (fun k : C₁(F) ↦ f (x * k.val)) = fun _ ↦ ((G (L x) : ℝ) : ℂ) := by
      funext k
      change ((G (L (x * k.val)) : ℝ) : ℂ) = _
      rw [hLmul, hLker, add_zero]
    rw [lcaCosetIntegral_mk _ _ _ x (by rw [hconst]; exact integrable_const _), hconst,
      integral_const, Complex.real_smul]
  let φ : (C𝔽(F) ⧸ C₁(F)) ≃* ℝ≥0ˣ :=
    QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) τ hτ
  let E : (C𝔽(F) ⧸ C₁(F)) ≃ₜ ℝ≥0ˣ :=
    { φ.toEquiv with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hN
      continuous_invFun := QuotientGroup.continuous_mk.comp hτc }
  let : MeasurableSpace (C𝔽(F) ⧸ C₁(F)) := borel _
  let : BorelSpace (C𝔽(F) ⧸ C₁(F)) := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let Em := E.toMeasurableEquiv
  have hdt : Measure.comap (QuotientGroup.kerLift (ideleClassNorm F)) positiveRealHaar =
      positiveRealHaar.map Em.symm := Em.map_symm.symm
  let H : ℝ≥0ˣ → ℂ := fun t ↦ (μ₁.real univ : ℂ) * ((G (Real.log ((t : ℝ≥0) : ℝ)) : ℝ) : ℂ)
  have hcosetH (q : C𝔽(F) ⧸ C₁(F)) :
      lcaCosetIntegral C₁(F) μ₁ f q = H (QuotientGroup.kerLift (ideleClassNorm F) q) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hcoset, QuotientGroup.kerLift_mk]
  have hexpm : Measurable (fun x : ℝ ↦ Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  have hRHS : (∫ q, lcaCosetIntegral C₁(F) μ₁ f q ∂(Measure.comap
      (QuotientGroup.kerLift (ideleClassNorm F)) positiveRealHaar)) =
      (μ₁.real univ : ℂ) * ((∫ y, G y : ℝ) : ℂ) := by
    simp_rw [hcosetH]
    rw [hdt, integral_map_equiv]
    have hEm (t : ℝ≥0ˣ) : QuotientGroup.kerLift (ideleClassNorm F) (Em.symm t) = t :=
      φ.apply_symm_apply t
    simp_rw [hEm]
    rw [positiveRealHaar, integral_map hexpm.aemeasurable]
    · simp only [H]
      rw [integral_const_mul, integral_complex_ofReal]
      congr 2
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      change G (Real.log (Real.exp y).toNNReal) = G y
      rw [Real.coe_toNNReal _ (Real.exp_pos y).le, Real.log_exp]
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp (hGc.comp
        ((NNReal.continuous_coe.comp Units.continuous_val).log fun t ↦
          (NNReal.coe_pos.mpr (Units.zero_lt t)).ne')))).aestronglyMeasurable
  have hLHS : (∫ g, f g ∂μ) = ((c : ℝ) * ∫ y, G y : ℝ) := by
    change (∫ g, ((G (L g) : ℝ) : ℂ) ∂μ) = _
    rw [integral_complex_ofReal, ← integral_map hL.aemeasurable hGc.aestronglyMeasurable]
    change (((∫ y, G y ∂μ') : ℝ) : ℂ) = _
    rw [hscale, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hcr : (c : ℝ) = μ₁.real univ := by
    have h := hLHS.symm.trans (hWeil.trans hRHS)
    rw [← Complex.ofReal_mul, Complex.ofReal_inj] at h
    exact mul_right_cancel₀ hGpos.ne' h
  have hcE : (c : ENNReal) = μ₁ univ := by
    rw [← ENNReal.ofReal_coe_nnreal, hcr, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change μ' = _
  rw [hscale, ← hcE]
  rfl

/-- At a character that only sees the log norm with frequency `x`, the transform of the
Gaussian `exp(−y²/2)` in `y = log |g|` has squared norm `m² · 2π · exp(−x²)`, where `m` is
the mass of the norm-one classes. -/
private theorem spectralPlancherel_gaussian_fourier (F : Type) [Field F] [NumberField F]
    (x : ℝ) (χ : PontryaginDual C𝔽(F))
    (hχ : ∀ g, χ g = Circle.exp (x * Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ))) :
    ‖lcaFourier (ideleClassTamagawaMeasure F) (fun g ↦ Complex.exp (-(1 / 2 : ℂ) *
        (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ 2)) χ‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal ((normOneIdeleClassTamagawaMeasure F).real univ ^ 2 * (2 * Real.pi) *
        Real.exp (-x ^ 2)) := by
  set r := (normOneIdeleClassTamagawaMeasure F).real univ with hr
  have hr0 : 0 ≤ r := measureReal_nonneg
  let L : C𝔽(F) → ℝ := fun g ↦ Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ)
  have hN : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  let φ : ℝ → ℂ := fun y ↦ Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) *
    star ((Circle.exp (x * y) : Circle) : ℂ)
  have hφ : Continuous φ := by
    refine (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.pow 2))).mul (continuous_star.comp ?_)
    exact continuous_subtype_val.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id))
  have hpt (y : ℝ) : φ y = Complex.exp (Complex.I * (-(x : ℂ)) * y) *
      Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2) := by
    simp only [φ, Circle.coe_exp, Complex.star_def, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hF : lcaFourier (ideleClassTamagawaMeasure F) (fun g ↦ Complex.exp (-(1 / 2 : ℂ) *
        (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ 2)) χ =
      (r : ℂ) * (((Real.pi : ℂ) / (1 / 2)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(-(x : ℂ)) ^ 2 / (4 * (1 / 2)))) := by
    have h1 : lcaFourier (ideleClassTamagawaMeasure F) (fun g ↦ Complex.exp (-(1 / 2 : ℂ) *
        (Real.log ((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ 2)) χ =
        ∫ g, φ (L g) ∂ideleClassTamagawaMeasure F := by
      simp only [lcaFourier, φ, L, hχ]
    rw [h1, ← integral_map hL.aemeasurable hφ.aestronglyMeasurable,
      spectralPlancherel_map_logNorm, integral_smul_measure]
    simp_rw [hpt]
    rw [fourierIntegral_gaussian (by norm_num), Complex.real_smul, ← measureReal_def]
  rw [hF, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two]
  congr 1
  have h2π : ((Real.pi : ℂ) / (1 / 2)) = ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  have hexp : Complex.exp (-(-(x : ℂ)) ^ 2 / (4 * (1 / 2))) = ((Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h2π, hexp, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Real.norm_of_nonneg hr0,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  norm_num
  rw [mul_pow, mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), sq (Real.exp _),
    ← Real.exp_add]
  ring_nf

/-- The Plancherel measure of the compact norm-one classes gives the trivial character the
reciprocal of their mass: the transform of the constant one is that mass at the trivial
character and vanishes elsewhere by orthogonality. -/
private theorem spectralPlancherel_normOneDual_one (F : Type) [Field F] [NumberField F]
    (ν₁ : Measure (PontryaginDual C₁(F)))
    (hν₁ : IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁) :
    ν₁ {1} * normOneIdeleClassTamagawaMeasure F univ = 1 := by
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  let : CompactSpace C₁(F) := (ideleClassGroup_finiteness F).2.1
  let : BorelSpace (PontryaginDual C₁(F)) := ⟨rfl⟩
  have hm0 : μ₁ univ ≠ 0 := (isOpen_univ.measure_pos μ₁ univ_nonempty).ne'
  have hmtop : μ₁ univ ≠ ⊤ := measure_ne_top _ _
  have hF : lcaFourier μ₁ (fun _ ↦ (1 : ℂ)) =
      ({1} : Set (PontryaginDual C₁(F))).indicator fun _ ↦ (μ₁.real univ : ℂ) := by
    funext ω
    simp only [lcaFourier, one_mul]
    by_cases hω : ω = 1
    · subst hω
      simp [PontryaginDual.one_apply, Complex.real_smul]
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      obtain ⟨h₀, hh₀⟩ : ∃ h₀, ω h₀ ≠ 1 := not_forall.mp fun hc ↦
        hω (PontryaginDual.ext fun k ↦ (hc k).trans (PontryaginDual.one_apply k).symm)
      have hinv := integral_mul_left_eq_self (μ := μ₁) (fun k ↦ star (ω k : ℂ)) h₀
      simp only [map_mul, Circle.coe_mul, star_mul'] at hinv
      rw [integral_const_mul] at hinv
      have hne : star (ω h₀ : ℂ) ≠ 1 := by
        intro h
        apply hh₀
        apply Subtype.ext
        simpa using congrArg star h
      have : (star (ω h₀ : ℂ) - 1) * ∫ k, star (ω k : ℂ) ∂μ₁ = 0 := by
        rw [sub_mul, hinv, one_mul, sub_self]
      exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)
  have hP := (hν₁.2.2 (fun _ ↦ (1 : ℂ)) (integrable_const _) (memLp_const _)).2
  rw [hF, eLpNorm_indicator_const (measurableSet_singleton _).nullMeasurableSet two_ne_zero
    ENNReal.ofNat_ne_top, eLpNorm_const _ two_ne_zero (Measure.measure_univ_ne_zero.mp hm0)] at hP
  have hnorm : ‖(μ₁.real univ : ℂ)‖ₑ = μ₁ univ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
      measureReal_def, ENNReal.ofReal_toReal hmtop]
  rw [hnorm, eNorm_one, one_mul] at hP
  have h2 := congrArg (· ^ (2 : ℝ)) hP
  simp only [ENNReal.toReal_ofNat] at h2
  rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
  norm_num at h2
  have h3 : μ₁ univ * (μ₁ univ * ν₁ {1}) = μ₁ univ * 1 := by
    rw [mul_one, ← mul_assoc, ← pow_two]
    exact h2
  rw [mul_comm]
  exact (ENNReal.mul_right_inj hm0 hmtop).mp h3

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
Take F = ℚ with its norm section and induced dual isomorphism. Use the Gaussian exp(−y²/2)
in y = log |g|, constant on the norm-one subgroup. With the kernel exp(ixy) its radial
transform is √(2π) exp(−x²/2). The printed measure makes its squared norm 2π times the
original squared norm, since the fixed norm-one Plancherel measure already accounts for
the compact factor. The radial Plancherel measure is dx/(2π). -/
theorem Printed.spectralPlancherelMeasure_eq_radialVolume_prod_false :
    ¬ Printed.spectralPlancherelMeasure_eq_radialVolume_prod := by
  intro hall
  obtain ⟨τ₀, hτc, hτ⟩ := (ideleGroup_quotient.{0, 0} ℚ).2.2.2.2.2.2.2.2.2.2.1
  let τ : ℝ≥0ˣ →ₜ* C𝔽(ℚ) := ⟨τ₀, hτc⟩
  obtain ⟨e, he⟩ := spectralPlancherel_exists_dualEquiv ℚ τ hτ
  let μ := ideleClassTamagawaMeasure ℚ
  let μ₁ := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace C₁(ℚ) := (ideleClassGroup_finiteness ℚ).2.1
  let : μ.Regular := (ideleClassTamagawaMeasure_isWeil ℚ).2.1
  let : μ₁.Regular :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.2.1
  obtain ⟨ν₁, hν₁⟩ := (lcaPlancherelMeasure_existsUnique μ₁).exists
  obtain ⟨ν, hν⟩ := (lcaPlancherelMeasure_existsUnique μ).exists
  have hmap := hall ℚ τ hτ e he ν₁ ν hν₁ hν
  let : BorelSpace (PontryaginDual C𝔽(ℚ)) := ⟨rfl⟩
  let : BorelSpace (PontryaginDual C₁(ℚ)) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let Φ := fun p : ℝ × PontryaginDual C₁(ℚ) ↦ e (Multiplicative.ofAdd p.1, p.2)
  -- The pushforward is neither zero nor a point mass, since ν is a Haar measure.
  have hν0 : ν ≠ 0 := fun h ↦ isOpen_univ.measure_ne_zero ν univ_nonempty (by rw [h]; rfl)
  have hreg : SFinite ν₁ ∧ AEMeasurable Φ (volume.prod ν₁) := by
    by_contra hdeg
    have hprod : volume.prod ν₁ ≠ 0 := fun h ↦ hν0 (by
      rw [← hmap]
      change Measure.map Φ (volume.prod ν₁) = 0
      rw [h, Measure.map_zero])
    have hsf : SFinite ν₁ := by
      by_contra hs
      exact hprod (Measure.prod_eq_zero_of_not_sfinite hs)
    have hΦ : ¬ AEMeasurable Φ (volume.prod ν₁) := fun h ↦ hdeg ⟨hsf, h⟩
    obtain ⟨χ₀, hχ₀⟩ : ∃ χ₀, ν = Measure.dirac χ₀ :=
      ⟨_, hmap.symm.trans (Measure.map_of_not_aemeasurable_of_ne_zero hΦ hprod)⟩
    let χ₁ := e (Multiplicative.ofAdd 1, 1)
    have hinv := map_mul_left_eq_self ν χ₁
    rw [hχ₀, Measure.map_dirac' (show Continuous fun x : PontryaginDual C𝔽(ℚ) ↦ χ₁ * x from
      continuous_const.mul continuous_id).measurable] at hinv
    have h1 := congrArg (fun m : Measure (PontryaginDual C𝔽(ℚ)) ↦ m {χ₀}) hinv
    simp only [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator,
      Set.mem_singleton_iff, mul_eq_right, Pi.one_apply] at h1
    have hχ₁ : χ₁ = 1 := by
      by_contra hne
      simp [hne] at h1
    have := congrArg Prod.fst (e.injective (hχ₁.trans (map_one e).symm))
    exact one_ne_zero (congrArg Multiplicative.toAdd this)
  obtain ⟨hsf, hΦ⟩ := hreg
  -- Constants.
  set m := μ₁ univ with hm
  set r := μ₁.real univ with hrdef
  have hm0 : m ≠ 0 := (isOpen_univ.measure_pos μ₁ univ_nonempty).ne'
  have hmtop : m ≠ ⊤ := measure_ne_top _ _
  have hmr : m = ENNReal.ofReal r := (ENNReal.ofReal_toReal hmtop).symm
  have hr : 0 < r := ENNReal.toReal_pos hm0 hmtop
  have hone : ν₁ {1} * m = 1 := spectralPlancherel_normOneDual_one ℚ ν₁ hν₁
  -- The Gaussian in log norm coordinates.
  let L : C𝔽(ℚ) → ℝ := fun g ↦ Real.log ((ideleClassNorm ℚ g : ℝ≥0) : ℝ)
  have hN : Continuous (ideleClassNorm ℚ) := (isProperMap_ideleClassNorm ℚ).continuous
  have hL : Continuous L :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp hN)).log fun g ↦
      (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  let G : ℝ → ℂ := fun y ↦ Complex.exp (-(1 / 2 : ℂ) * (y : ℂ) ^ 2)
  have hG : Continuous G :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  let f : C𝔽(ℚ) → ℂ := fun g ↦ G (L g)
  have hmapL : μ.map L = m • volume := spectralPlancherel_map_logNorm ℚ
  have hGnorm (y : ℝ) : ‖G y‖ = Real.exp (-1 / 2 * y ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [← Complex.ofReal_pow]
    ring
  have hGsq (y : ℝ) : ‖G y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Real.exp (-1 * y ^ 2)) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two, hGnorm,
      Real.rpow_two, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hGint : Integrable G volume := integrable_cexp_neg_mul_sq (by norm_num)
  have hGL2 : MemLp G 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mpr ?_
    refine (integrable_exp_neg_mul_sq one_pos).congr (Filter.Eventually.of_forall fun y ↦ ?_)
    change Real.exp (-1 * y ^ 2) = ‖G y‖ ^ 2
    rw [hGnorm, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfi : Integrable f μ :=
    (integrable_map_measure hG.aestronglyMeasurable hL.aemeasurable).mp
      (by rw [hmapL]; exact hGint.smul_measure hmtop)
  have hfm : MemLp f 2 μ :=
    (memLp_map_measure_iff hG.aestronglyMeasurable hL.aemeasurable).mp
      (by rw [hmapL]; exact hGL2.smul_measure hmtop)
  obtain ⟨hFm, hP⟩ := hν.2.2 f hfi hfm
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hFm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hfi.aestronglyMeasurable] at hP
  simp only [ENNReal.toReal_ofNat] at hP
  have hAB := ENNReal.rpow_left_injective (by norm_num : (1 / 2 : ℝ) ≠ 0) hP
  -- The squared norm of the test.
  have hgauss : ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-1 * y ^ 2)) =
      ENNReal.ofReal (Real.sqrt Real.pi) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq one_pos)
      (Filter.Eventually.of_forall fun y ↦ (Real.exp_pos _).le), integral_gaussian, div_one]
  have hB : ∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ) ∂μ = m * ENNReal.ofReal (Real.sqrt Real.pi) := by
    have hmeas : Measurable fun y : ℝ ↦ ‖G y‖ₑ ^ (2 : ℝ) :=
      (ENNReal.continuous_rpow_const.comp hG.eNorm).measurable
    rw [show (∫⁻ g, ‖f g‖ₑ ^ (2 : ℝ) ∂μ) = ∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂(μ.map L) from
      (lintegral_map hmeas hL.measurable).symm, hmapL, lintegral_smul_measure, smul_eq_mul]
    simp_rw [hGsq]
    rw [hgauss]
  -- A lower bound for the squared norm of the transform from the trivial norm-one character.
  let h : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (r ^ 2 * (2 * Real.pi) * Real.exp (-x ^ 2))
  have hh : Continuous h := ENNReal.continuous_ofReal.comp
    (continuous_const.mul (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2))))
  let R : Set (PontryaginDual C𝔽(ℚ)) := {χ | (e.symm χ).2 = 1}
  have hRm : MeasurableSet R :=
    (continuous_snd.comp e.symm.continuous).measurable (measurableSet_singleton _)
  let ψ : PontryaginDual C𝔽(ℚ) → ENNReal := R.indicator fun χ ↦ h (e.symm χ).1.toAdd
  have hψm : Measurable ψ :=
    (hh.comp (continuous_toAdd.comp (continuous_fst.comp e.symm.continuous))).measurable.indicator
      hRm
  have hψle (χ : PontryaginDual C𝔽(ℚ)) : ψ χ ≤ ‖lcaFourier μ f χ‖ₑ ^ (2 : ℝ) := by
    change R.indicator (fun χ ↦ h (e.symm χ).1.toAdd) χ ≤ _
    by_cases hχR : χ ∈ R
    · rw [Set.indicator_of_mem hχR]
      set x := (e.symm χ).1.toAdd
      have hχe : χ = e (Multiplicative.ofAdd x, 1) := by
        rw [← e.apply_symm_apply χ]
        congr 1
        exact Prod.ext rfl hχR
      refine (spectralPlancherel_gaussian_fourier ℚ x χ fun g ↦ ?_).symm.le
      have hk : (τ (ideleClassNorm ℚ g))⁻¹ * g ∈ (ideleClassNorm ℚ).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        exact (congrArg (·⁻¹ * _) (hτ _)).trans (inv_mul_cancel _)
      have := he x 1 (ideleClassNorm ℚ g) ⟨_, hk⟩
      rw [mul_inv_cancel_left, PontryaginDual.one_apply, one_mul] at this
      rw [hχe]
      exact this
    · rw [Set.indicator_of_notMem hχR]
      exact zero_le
  have hψΦ (p : ℝ × PontryaginDual C₁(ℚ)) :
      ψ (Φ p) = h p.1 * ({1} : Set (PontryaginDual C₁(ℚ))).indicator 1 p.2 := by
    have hs : e.symm (Φ p) = (Multiplicative.ofAdd p.1, p.2) := e.symm_apply_apply _
    change R.indicator (fun χ ↦ h (e.symm χ).1.toAdd) (Φ p) = _
    by_cases hp : p.2 = 1
    · rw [Set.indicator_of_mem (show Φ p ∈ R by simp [R, hs, hp]),
        Set.indicator_of_mem (show p.2 ∈ ({1} : Set _) from hp), hs]
      simp
    · rw [Set.indicator_of_notMem (show Φ p ∉ R by simp [R, hs, hp]),
        Set.indicator_of_notMem (show p.2 ∉ ({1} : Set _) from hp), mul_zero]
  have hlow : ENNReal.ofReal (r ^ 2 * (2 * Real.pi) * Real.sqrt Real.pi) * ν₁ {1} ≤
      ∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ (2 : ℝ) ∂ν := by
    refine le_trans (le_of_eq ?_) (lintegral_mono hψle)
    rw [← hmap, lintegral_map' hψm.aemeasurable hΦ]
    simp_rw [hψΦ]
    rw [lintegral_prod_mul hh.aemeasurable
      ((measurable_one.indicator (measurableSet_singleton _)).aemeasurable),
      lintegral_indicator_one (measurableSet_singleton _)]
    congr 1
    have hint : Integrable fun x : ℝ ↦ r ^ 2 * (2 * Real.pi) * Real.exp (-x ^ 2) := by
      simpa [neg_one_mul] using (integrable_exp_neg_mul_sq one_pos).const_mul (r ^ 2 * (2 * Real.pi))
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x ↦ by positivity), integral_const_mul]
    congr 2
    simpa [neg_one_mul] using (integral_gaussian 1).symm
  -- Compare: the transform has 2π times the squared norm of the test.
  rw [hAB, hB] at hlow
  have hle := mul_le_mul_left hlow m
  rw [mul_assoc, hone, mul_one, hmr, ← ENNReal.ofReal_mul hr.le,
    ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.sqrt_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hpos : 0 < r ^ 2 * Real.sqrt Real.pi := by positivity
  nlinarith [Real.pi_gt_three]

end Plancherel

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
As printed: for each norm-one character and any numbering of its line-zero ordinates by
the natural numbers, the Fourier–Mellin samples of every test decay rapidly. This is the
claim for an infinite zero set. See `spectralLineConvolution_trace` and ERRATA F183. -/
def Printed.spectralLineSamples_rapid_for_any_numbering : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (φ : BruhatCompactSupport C𝔽(F)) (ω : PontryaginDual C₁(F))
      (e : ℕ ≃ lineZeros(χ ω, a)) (k : ℕ),
      Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * ∫ g,
        φ.val g * ideleClassNormTwist (χ ω) (shift(0, (e n).val)) g
          ∂ideleClassTamagawaMeasure F) atTop (𝓝 0)

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
Take F = ℚ, the trivial base character and a = 1/2. Modulate a nonzero smooth radial
bump in y = log |g| by exp(icy). Its entire transform has discrete real zeros. Avoid the
countably many frequencies c for which a sample is zero. Place infinitely many samples
vⱼ at increasing nonadjacent indices nⱼ ≥ 1/|vⱼ|, leaving infinitely many ordinates for
the other indices. Then nⱼ|vⱼ| ≥ 1, which violates decay at k = 1. -/
theorem Printed.spectralLineSamples_rapid_for_any_numbering_false :
    ¬ Printed.spectralLineSamples_rapid_for_any_numbering := by sorry

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
As printed: for each integration-by-parts order N > 1, one constant bounds all admitted
Mellin derivatives at nonreal strip zeros by the displayed falling factorial over |z|^N.
The order range on p. 455 includes the low orders in (10.3.2.7). The radial Mellin transform
uses the compact character coefficient for the selected component, as on p. 450 after
(10.3.1.17). See `spectralStripConvolution_traceCauchy` and ERRATA F185. -/
def Printed.spectralStripMellinJet_norm_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s → ∀ (φ : BruhatCompactSupport C𝔽(F)) (N : ℕ), 1 < N →
      let M (ω : PontryaginDual C₁(F)) (z : ℂ) :=
        ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
          (∫ k : C₁(F), (ω k : ℂ) * φ.val (τ r * k.val) ∂normOneIdeleClassTamagawaMeasure F)
          ∂positiveRealHaar
      ∃ C : ℝ, 0 < C ∧ ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ),
        b ∈ Icc (-α) α → t ≠ 0 → 0 < orderAt(χ ω, shift(a + b, t)) →
        let mult := (orderAt(χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min mult floorCut(s) else mult
        ∀ i : ℕ, i < count →
          ‖iteratedDeriv i (M ω) (shift(b, t))‖ ≤
            C * (∏ n ∈ Finset.range N, ((i : ℝ) - (n : ℝ))) / ‖shift(b, t)‖ ^ N

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Take F = ℚ, the trivial base character, a = 1/2, α = 1, s = 2 and N = 2. Let z = iγ
for the first positive critical-line zeta ordinate γ. The interior multiplicity admits
i = 0. For φ(g) = h(log |g|) exp(−iγ log |g|), with h a nonnegative smooth bump of
positive integral, M(φ)(iγ) has positive norm. The n = 0 factor forces the right-hand
side to vanish for every constant C. -/
theorem Printed.spectralStripMellinJet_norm_le_false :
    ¬ Printed.spectralStripMellinJet_norm_le := by sorry

end RiemannMasullo
