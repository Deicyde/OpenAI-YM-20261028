import YM.Next.FOUNDATIONS.TestBounds


set_option warningAsError false

/-!
# From literal left bounds at any healthy point to mixed Fréchet

Cf `TestBounds` private tools at identity, derive in scaled
form here (allow any per-link weight as specified dirBound multiplier, even
ca. ≤0 handles zero rays). No dependence on link count, L, threshold etc.
Using at every test position, constants only arity (not buying current
sections). Does not yet test log charts at nonzero input. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Lyre
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open  Next.Foundations
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ}

section

local notation "F" k => Fin k → ℝ

/-- `finite pullbacks`: test on only same direction, lose constant JUST
of tensor order. -/
private theorem concert (k : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ T : Tensor.T (F k) ℂ k,Sym T → ∀ c : ℝ,0 ≤ c →
    (∀ v,(∑ i,‖v i‖) ≤ 1 → ‖Tensor.diagonal T v‖ ≤ c) → ‖T (fun i => Pi.single i 1)‖ ≤ C*c := by
  by_contra! hu
  let B (i : ℕ) := (i:ℝ)+1
  choose f hf c hc he H using fun i => hu (B i) (by unfold B; linarith only [Nat.cast_nonneg (α:=ℝ) i])
  have hn i : 0 < B i := by unfold B; positivity
  let w : Fin k → F k := fun i => Pi.single i 1
  let M := ∏ i, ‖w i‖
  have hm : 0 ≤ M := prod_nonneg fun _ _ => norm_nonneg _
  have hp i : B i*c i < ‖f i‖ * M := (H i).trans_le ((f i).le_opNorm w)
  have hh i : 0 < ‖f i‖ := by nlinarith only [mul_nonneg (hn i).le (hc i),hp i,norm_nonneg (f i),hm]
  let Y (i : ℕ) := ‖f i‖⁻¹ • f i
  have ht i : Y i∈Metric.sphere (0:Tensor.T (F k) ℂ k) 1 := by simp [Y, norm_smul, (hh i).ne']
  letI : ProperSpace (Tensor.T (F k) ℂ k) := FiniteDimensional.proper ℝ _
  obtain ⟨p,hz,s,hS,hp'⟩:= (isCompact_sphere (0:Tensor.T (F k) ℂ k) 1).isSeqCompact ht
  suffices p=(0:Tensor.T (F k) ℂ k) by simp [this] at hz
  let J x := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => F k) ℂ x
  have hx w : Tendsto (fun i : ℕ => Y (s i) w) atTop (𝓝 (p w)) := (J w).continuous.continuousAt.tendsto.comp hp'
  apply ext_diag _ _ ?_ (fun _ _ => rfl)
  · funext v
    let r := 1+∑ i, ‖v i‖
    have hr : 0 < r := add_pos_of_pos_of_nonneg zero_lt_one (sum_nonneg fun _ _ => norm_nonneg _)
    have hR : (∑ i, ‖(r⁻¹ • v) i‖) ≤ 1 := by
      simp_rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hr).le,← Finset.mul_sum]
      unfold r; rw [inv_mul_le_iff₀ hr,mul_one]; linarith
    let x : F k := r⁻¹ • v
    have he i : ‖Tensor.diagonal (Y i) x‖ ≤ M/B i := by
      change ‖(‖f i‖⁻¹:ℝ) • Tensor.diagonal (f i) x‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr (hh i)).le]
      refine le_trans (mul_le_mul_of_nonneg_left (he i x hR) (inv_pos.mpr (hh i)).le) ?_
      rw [inv_mul_le_iff₀ (hh i),← mul_div_assoc,le_div_iff₀ (hn i),mul_comm (c i)]; exact (hp i).le
    have hZ : Tendsto (fun i => ‖Tensor.diagonal (Y i) x‖) atTop (𝓝 (0:ℝ)) := by
      refine squeeze_zero (fun i => norm_nonneg _) he (tendsto_const_nhds.div_atTop ?_)
      exact tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
    have hv : Tensor.diagonal p x=0 := norm_eq_zero.mp (tendsto_nhds_unique (hx (fun _ => x)).norm (hZ.comp hS.tendsto_atTop))
    rw [show v=r • x from (smul_inv_smul₀ hr.ne' v).symm,Tensor.homogeneous,hv,smul_zero]; rfl
  intro i a; apply tendsto_nhds_unique (hx _)
  simp only [Y,smul_apply,hf _ i a]; exact hx i
end

/-! explicit weight for each link. -/
def width (P : BudgetPoint) (o : Site n) (i : Edge (Site n)) := P.threshold*(1+(separation i.1 o:ℝ))^P.power

lemma width_pos (P : BudgetPoint) (o : Site n) (i : Edge (Site n)) : 0 < width P o i := by unfold width; have ht := P.threshold_pos; positivity

/-- Calendar-free polarization. -/
theorem entry (k : ℕ) (G : Gauge) : ∃ C : ℝ,1 ≤ C ∧ ∀ (n : Side) (P : BudgetPoint) (Y : Support n) (o : Site n)
    (u : Config G n → ℂ) (V : Config G n) (c : ℝ) (f : Fin k → Directions G n), k ≤ P.order → Healthy P.threshold Y V → P.Regular Y u →
      P.supBounds o Y u c → (∀ i j,‖f i j‖ ≤ width P o j) →
      ‖iteratedFDeriv ℝ k (u ∘ increment V) 0 f‖ ≤ C*c := by
  obtain ⟨C,h,H⟩:=concert k; refine ⟨C,h,fun n P Y o u V c f he hh hp hu hv => ?_⟩
  let g := u ∘ increment V
  let R (x) := f x
  let L : (Fin k → ℝ) →L[ℝ] Directions G n := ∑ i,(ContinuousLinearMap.proj (R:=ℝ) i).smulRight (f i)
  have hs (v : Fin k→ℝ) : L v=∑ i,v i • f i := by simp [L]
  let T := iteratedFDeriv ℝ k g 0
  let A := T.compContinuousLinearMap (fun _ => L)
  have ht : ContDiffAt ℝ k g 0 := (hp.smooth V hh).of_le (Nat.cast_le.mpr he)
  have ha : Sym A := fun v s => Analysis.sym_Jet ht (L ∘ v) s
  have hT v (hy : (∑ i, ‖v i‖) ≤ 1) : ‖Tensor.diagonal A v‖ ≤ c := by
    have hC : P.dirBound o (L v) := by
      intro e
      calc
        _ = ‖∑ i, v i • f i e‖ := by rw [hs,Finset.sum_apply]; rfl
        _ ≤ ∑ i, ‖v i • f i e‖ := norm_sum_le ..
        _ ≤ ∑ i, ‖v i‖*width P o e := sum_le_sum (fun i _ => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hv i e) (norm_nonneg _))
        _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_of_le_one_left (width_pos ..).le hy
    change ‖Tensor.diagonal T (L v)‖ ≤ _
    rw [show Tensor.diagonal T (L v)=iteratedDeriv k (fun t : ℝ => u (increment V (t • L v))) 0 from (iteratedDeriv_on_line ht _).symm,
      ← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]
    refine hu.2 V hh _ (List.length_replicate.trans_le he) fun i hi => (List.mem_replicate.mp hi).2 ▸ hC
  rw [show T f=A (fun i => Pi.single i 1) from congr_arg T (by
    funext i; simp [hs,Pi.single_apply,ite_smul])]
  exact H A ha c hu.1 hT

def Sized (a : ℝ) (w : Directions G n) (P : BudgetPoint) (o : Site n) :=
    0 ≤ a ∧ ∀ i, ‖w i‖ ≤ a*width P o i

/-- Remains uniform for per-leg sizes, even if zero. -/
theorem lyre (k : ℕ) (G : Gauge) : ∃ C : ℝ,1 ≤ C ∧ ∀ (n : Side) (P : BudgetPoint) (Y : Support n) (o : Site n)
    (u : Config G n → ℂ) (V : Config G n) (c : ℝ) (f : Fin k → Directions G n) (a : Fin k→ℝ),
      k ≤ P.order → Healthy P.threshold Y V → P.Regular Y u → P.supBounds o Y u c →
      (∀ i, Sized (a i) (f i) P o) → ‖iteratedFDeriv ℝ k (u ∘ increment V) 0 f‖ ≤ (∏ i,a i)*C*c := by
  obtain ⟨C,hc,he⟩:=entry k G
  refine ⟨C,hc,fun n P Y o u V c f a h hp hi ht hA => ?_⟩
  let A := iteratedFDeriv ℝ k (u ∘ increment V) 0
  let w (i : Fin k) := (a i)⁻¹ • f i
  have hh i : f i=a i • w i := by
    rcases eq_or_lt_of_le (hA i).1 with H|H
    · have ht j : f i j=0 := norm_le_zero_iff.mp (by have hv := (hA i).2 j; simpa [← H] using hv)
      rw [← H,zero_smul]; exact funext ht
    exact (smul_inv_smul₀ H.ne' (f i)).symm
  have hf : ∀ i j, ‖w i j‖ ≤ width P o j := by
    intro i j
    rcases eq_or_lt_of_le (hA i).1 with H|H
    · unfold w; rw [← H,inv_zero,zero_smul,Pi.zero_apply,norm_zero]; exact (width_pos ..).le
    rw [show w i j=(a i)⁻¹ • (f i j) from rfl,norm_smul,Real.norm_of_nonneg (inv_pos.mpr H).le,inv_mul_le_iff₀ H]; exact (hA i).2 j
  have hS : 0 ≤ ∏ i,a i := prod_nonneg fun i _ => (hA i).1
  change ‖A f‖ ≤ _
  rw [funext hh,A.map_smul_univ,norm_smul,Real.norm_of_nonneg hS,mul_assoc]
  exact mul_le_mul_of_nonneg_left (he n P Y o u V c w h hp hi ht hf) hS
end YM.MultiNext.SignedSource.Lyre
