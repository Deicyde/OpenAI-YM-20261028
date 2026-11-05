import YM.Next.FOUNDATIONS.Readout
import YM.Push.CUTOFF_PROJECTORS.Bank

/-!
# Exact part of Bill at a locally initialized top stencil

There is a useful smaller premise to apply the Bank when the top
regular support data for the equation cylinders are truly initialized at
N on finite stencils. For the moment treat the case of only finitely many
nonzero **regular** terms there, on nonwrapping supports. Then
`TopTest` follows from the chain receipts, despite masks and forced terms
being present. Prove this; don't assume simply equating densities
in general equates their x coordinates. No continuity across mask
boundaries used. No treating threshold directions as unscaled reads.
Numerical accuracy part of Bill remains a separate finite estimate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.CutoffProjectors.Packet
open Function Filter Next.Foundations Labels Lattice Source RG Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {C : Family G} {d p N : ℕ} {E : Packet C d N p} {S : Finset Cover}

section Test
variable {n : Side}

private theorem tends_one (H : Hol G) (o : Site n) (j : Jet G) (d : ℕ) :
    Tendsto (H.testLinks d o j) (𝓝 0) (𝓝 1) := by
  let L := testLog H d o j
  have hl : Tendsto L (𝓝 0) (𝓝 0) := by
    rw [← testLog_zero H d o j]; exact (testLog_diff H d o j).continuousAt.tendsto
  have hk : Continuous (increment (1: Config G n)) := by unfold increment; fun_prop
  have he : increment (1:Config G n) 0 = 1 := Work.G07.at_zero_increment _
  rw [← he]
  exact (hk.continuousAt.tendsto.comp hl).congr' (increment_testLog H d o j).symm

private theorem never_flag (θ : ℝ) (hθ : 0 < θ) (H : Hol G) (o : Site n) (j : Jet G) (d : ℕ) :
    ∀ᶠ r : ℝ in 𝓝 0, flags θ (H.testLinks d o j r) = ∅ := by
  let Z := H.testLinks d o j
  have hp (p : Face (Per n)) : ∀ᶠ r in 𝓝 0, G.chord (faceValue (Z r) p) ≤ θ := by
    have he : Continuous fun U : Config G n => G.chord (faceValue U p) := by unfold faceValue; fun_prop
    have ht : G.chord (faceValue (1 : Config G n) p) = 0 := by simp [faceValue, square, travel]
    exact (he.continuousAt.tendsto.comp (tends_one H o j d)).eventually (ge_mem_nhds (ht.trans_lt hθ))
  filter_upwards [eventually_all.mpr hp] with r hr
  ext i
  simp only [flags_spec, Finset.notMem_empty, iff_false, not_exists, not_and, not_lt]
  exact fun p _ => hr p

private lemma unmarked {F : Labels.Frame G d} (P : Coefficient F n) (R : Rep G n) {U : Config G n}
    (h : flags R.p.threshold U = ∅) : ∀ b, P.marked R b U = 0 := by
  intro b; unfold Coefficient.marked; split
  · rename_i hh
    suffices b = ∅ by rw [this]; simp
    by_contra hx
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hx
    obtain ⟨v,hv⟩ := (R.activities.forced i).inventory_ne
    have he : v ∈ flags R.p.threshold U := by rw [← hh.2]; exact Finset.mem_biUnion.mpr ⟨i,hi,hv⟩
    simp only [h, Finset.notMem_empty] at he
  rfl

private lemma restored {F : Labels.Frame G d} {s : SectionData F} {H : Hol G} (h : s.Sound H)
    (v : F.Coeff) (o : Site n) (t : ℝ) (U : Config G n) :
    v 0 + s.places (F.scaled t (F.core v)) o U = s.places (F.scaled t v) o U := by
  have he : v = F.core v + v 0 • F.e0 := by
    funext i; by_cases hi : i = 0 <;> simp [Labels.Frame.core, Labels.Frame.e0, Function.update,hi]
  have hs : F.scaled t v = F.scaled t (F.core v) + v 0 • F.e0 := by
    nth_rw 1 [he]
    rw [map_add,map_smul,Labels.Frame.scaled_unit]
  rw [hs]
  simp only [SectionData.places, s.eval_linear.map_add,s.eval_linear.map_smul,h.unit]
  simp [add_comm]
end Test

/-- Finite-initialization lemma: the regular *chains* might require infinitely
many supports; this one asks for finite appearance at N, and nonwrapping for
the selected addresses (not merely local smoothness). Uses all coefficient
components, including constants in the equation presentation. -/
theorem top_of_finite (h : E.ComesFrom S) (hc : C.Makes) (v : equationSpace (C.labels.level d))
    (I : Finset ℕ) (hf : ∀ i ∉ I, (E.chain N v).regular i = 0)
    (hi : ∀ i ∈ I, Nonwrapping ((E.chain N v).support i) 0) : E.TopTest v := by
  classical
  let R := C.path.rep N p N
  let P := E.chain N v
  let B := C.localSection d
  let H := C.params
  let F := C.labels.level d
  let θ := R.p.threshold
  let q := F.scaled θ⁻¹ P.x
  have hq : C.path.levels.clock.threshold N = θ := by
    unfold θ R; rw [(hc.wilson.represents _ _ _ le_rfl).vac]; rfl
  unfold TopTest
  change JetTest H (0 : Site (C.side N p)) (_ ) _
  rw [hq]
  intro J
  let Z := H.testLinks d (0 : Site (C.side N p)) J
  let T := fun t => B.places q 0 (Z t)
  let L := fun (i : ℕ) (t : ℝ) => P.regular i (Z t)
  let Y := fun t => T t + ∑ i ∈ I, L i t
  have he : (fun t => ((C.S.a N:ℂ)^d) * E.Jorigin v (Z t)) =ᶠ[𝓝 0] Y := by
    filter_upwards [never_flag _ R.p.threshold_pos H (0 : Site (C.side N p)) J d] with t ht
    change flags _ (Z t) = _ at ht
    have hU : (R.eval (Z t) : ℂ) ≠ 0 := by
      unfold Rep.eval; rw [Activities.gas_one _ _ ht]; exact Complex.ofReal_ne_zero.mpr (mul_pos (Real.exp_pos _) one_pos).ne'
    have hM : ∀ b, P.marked R b (Z t) = 0 := unmarked _ _ ht
    have hC (s) : Healthy θ s (Z t) := by unfold Healthy θ; rw [ht]; simp
    have hm (i) : P.maskedTerm R i (Z t) = L i t := masked_eq _ _ _ (Z t) (hC _)
    have hh : P.exponentialEntry 0 B R (Z t) = Y t := by
      unfold Coefficient.exponentialEntry Y T
      simp_rw [hm, tsum_eq_sum (s:=I) (fun i hx => show L i t = 0 from (by unfold L P; rw [hf i hx]; rfl))]
      rw [masked_eq _ _ _ _ (hC _)]
      rw [restored (hc.sections d)]
    have hh' := h.encode v (Z t)
    change (_ : ℂ) * P.exponentialEntry 0 B R (Z t) + _ * ∑' b, P.marked R b (Z t) =
      _ * (R.eval (Z t):ℂ) * E.Jorigin v (Z t) at hh'
    simp_rw [hM,hh] at hh'
    apply mul_left_cancel₀ hU
    rw [tsum_zero, mul_zero, add_zero, mul_comm ((C.S.a N:ℂ)^d), mul_assoc] at hh'
    exact hh'.symm
  have hu : ∀ i ∈ I, H.PiVanish d 0 (P.regular i) :=
    fun i hz => (h.format N h.fit le_rfl v).projects i (hi i hz)
  have hk := Next.Foundations.placed_reads B (0 : Site (C.side N p)) (hc.places _ _ _ h.fit) (hc.sections d) q
  rw [Reads, if_pos (Next.Foundations.nonwrapping_placement B _ (hc.places _ _ _ h.fit))] at hk
  have hx := hk J
  have hT : ContDiffAt ℝ (d:WithTop ℕ∞) T 0 := hx.1
  have hcL i (hi : i ∈ I) : ContDiffAt ℝ (d:WithTop ℕ∞) (L i) 0 := (hu i hi J).1
  have hI : ContDiffAt ℝ (d:WithTop ℕ∞) (fun t => ∑ i ∈ I, L i t) 0 := ContDiffAt.sum hcL
  refine ⟨(hT.add hI).congr_of_eventuallyEq he,hx.2.1,fun k hkd => ?_⟩
  have hd : (k : WithTop ℕ∞) ≤ (d : WithTop ℕ∞) := Nat.cast_le.mpr hkd
  apply (he.iteratedDeriv_eq k).trans; unfold Y
  rw [iteratedDeriv_fun_add (hT.of_le hd) (hI.of_le hd), iteratedDeriv_fun_sum (fun i hi => (hcL i hi).of_le hd),
    Finset.sum_eq_zero (fun i hi => show iteratedDeriv k (L i) 0 = 0 from (hu i hi J).2 k hkd),add_zero]
  exact hx.2.2 _ hkd
end YM.Push.CutoffProjectors.Packet
