import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Residual



/-!
# Pay the actual normalized directions of 

Ordinary left-exp-*coordinate* convention in E (at 0 for V in that
sentence, here extended and estimated also at B). This is not ordered Lie
differentiation (no variable-frame terms). At a flag boundary it still means
differentiating this one unmasked covariance function. `γ` arbitrary, can take
t'=`temp x`; show here even absorption into t=`fiery` for normalized positive
orders, no change of exponential debt to polynomial in the period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open YM.Push.Uniform (bolt)
open YM.FreeResolvent (Mark Bundle native)
open YM.FreeResolvent.Mark (Bill)
open YM.FreeResolvent.TestD Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S} {x η d v κ γ : ℝ}

section weighted
variable {ι θ : Type} [Fintype ι] [Fintype θ] {C : ℝ} {M : ℕ → ℝ}
    {H : PriceCoords G c → Matrix ι θ ℝ} {Q : PriceCoords G c → Matrix ι ι ℝ}
    {a : ι → Site c} {b : θ → Site c} {B : PriceCoords G c} {n : ℕ}

/-- Field-direction read (a CLM, on the given representation of Color). -/
def reader (G : Gauge) (c : Side) : Directions G c →L[ℝ] PriceCoords G c :=
  gaugeCount.symm.toContinuousLinearMap

/-- Parameter through actual unflattened Lie coordinates. -/
def cart (H : PriceCoords G c → Matrix ι θ ℝ) : Directions G c → Matrix ι θ ℝ := H ∘ reader G c

lemma reader_field (V : Config G c) (y : Directions G c) : field V (reader G c y)=increment V y := by
  change increment V (tape (tape.symm y)) = _; rw [tape.apply_symm_apply]

/-- `RG.BudgetPoint.dirBound` magnitude condition at free parameters. -/
def Afford (γ : ℝ) (p : ℕ) (o : Site c) (l : List (Directions G c)) :=
    ∀ w ∈ l, ∀ i : Bond c, ‖w i‖ ≤ γ*Mark.hill (native c) o p i.1



/-- `Mark.radial` pay on each row is exactly `τ(i)^(-j)`, with j the
order; also on each column through the other endpoint. -/
structure Weighted (a : ι → Site c) (b : θ → Site c) (B : PriceCoords G c)
    (n p : ℕ) (d : ℝ) (C : ℕ → ℝ) (Q : PriceCoords G c → Matrix ι θ ℝ) : Prop where
  smooth : ContDiffAt ℝ n (cart Q) (tape B)
  each (o : Site c) {γ : ℝ} (hg : 0 ≤ γ) (l : List (Directions G c)) :
    l.length ≤ n → Afford γ p o l →
    Bill (Mark.radial (Directions G c) (native c) o p) (native c) a b l d (C l.length * γ^l.length)
      (jet id (cart Q) l (tape B))

def activation (G : Gauge) (n p : ℕ) (d : ℝ) := (paramPrice G (d/2)*Mark.polynomial (d/2) p)^n
lemma activation_one (G : Gauge) (n p : ℕ) (hd : 0 < d) : 1 ≤ activation G n p d := by
  apply one_le_pow₀ (one_le_mul_of_one_le_of_one_le (param_pos ..) (Mark.poly_le p (half_pos hd)))

lemma activates (p : ℕ) (h : ContDiffAt ℝ n H B) (hd : 0 < d) (hM : ∀ i, i ≤ n → 0 ≤ M i)
    (hf : ∀ l : List (Coord G c), l.length ≤ n →
      Bill (marks G c d) (native c) a b l d (M l.length) (jet bolt H l B)) :
    Weighted a b B n p d (fun i => activation G n p d * M i) H := by
  let Z := reader G c
  have he : Z (tape B)=B := gaugeCount.symm_apply_apply _
  refine ⟨(he.symm ▸ h : ContDiffAt ℝ n H (Z (tape B))).comp (tape B) Z.contDiff.contDiffAt,
    fun o γ hγ l hl ha => ?_⟩
  have hy := smooth_of_le h hl
  have hx : jet id (cart H) l (tape B) = jet Z H l B := by
    unfold jet cart
    change iteratedFDeriv ℝ _ (H ∘ Z) _ _ = _
    rw [Push.Uniform.iter_lin_at (he.symm ▸ hy : ContDiffAt ℝ _ H (Z (tape B))),he]
    rfl
  have hL := directional_bill o p (A:=H) (σ:=d) (p:=a) (q:=b) Z l hy (fun w => ?_) (hM _ hl) hd hγ ?_
  rotate_left
  · simpa using hf (List.ofFn w) (by rwa [List.length_ofFn])
  · intro i hi j
    refine le_trans ?_ (ha i hi j.1)
    change |(i j.1) j.2| ≤ _
    rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ (i j.1) j.2]
    simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ j.2) (i j.1)
  rw [hx]; refine hL.mono le_rfl ?_
  let s := Mark.polynomial (d/2) p; let X := paramPrice G (d/2)*s
  have hh : 1 ≤ X := one_le_mul_of_one_le_of_one_le (param_pos ..) (Mark.poly_le _ (half_pos hd))
  calc
    _ = X^l.length*M l.length*γ^l.length := by unfold X s; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hh hl) (hM _ hl))
      (pow_nonneg hγ _)

lemma Polar.weighted (p : ℕ) (h : Polar B a b H n d C) (hd : 0<d) (hc : 0 ≤ C) :
    Weighted a b B n p d (fun _ => activation G n p d * C) H :=
  activates (M:=fun _ => C) p h.smooth hd (fun _ _ => hc) h.bound

lemma ResolventJets.weighted (p : ℕ) {u : ℝ} (hu : 0 ≤ u) (h : ResolventJets a B n d C u Q)
    (hd : 0 < d) (hc : 0 ≤ C) :
    Weighted a a B n p d (fun i => charges i 1 (activation G n p d * C) (drain u)) Q := by
  rw [show (fun i => charges i 1 (activation G n p d * C) (drain u)) =
    (fun i => activation G n p d * charges i 1 C (drain u)) from ?_]
  · exact activates p h.smooth hd (fun i _ => charges_nn i zero_le_one hc (drain_pos hu).le) h.jets
  funext i; unfold charges; split <;> ring


end weighted

variable {A : Stores S} {k : S.Choices} {V : Config G c} {B : PriceCoords G c} {n : ℕ}

lemma Estimate.directions {M : ℝ} (p : ℕ) (h : Estimate n d v η κ M A F T x V k B) (hd : 0<d)
    (hM : 0 ≤ M) :
    let a := Wisps.front A F (G:=G) (x:=x)
    let C := activation G n p d*M
    let fee := Real.exp (-v*radiusB x)
    let Q := profileGram T x V A F k
    Weighted (Wisps.down S) a B n p d (fun _ => C) (profileD T x V A F k) ∧
    Weighted a a B n p d (fun _ => C) Q ∧
    Weighted a a B n p d (fun _ => C) (pickedCov A F T x V k) ∧
    Weighted a a B n p d (fun _ => C*fee) (pickedS A F T x V k) ∧
    Weighted a a B n p d (fun _ => C*fee) (pickedDelta A F T x V k) ∧
    Weighted a a B n p d (fun _ => C*fee) (pickedCov A F T x V k-fun y => (Q y)⁻¹) ∧
    ∀ u : ℝ, 0 ≤ u →
      Weighted a a B n p d (fun i => charges i 1 C (drain u)) (action Q u) ∧
      Weighted a a B n p d (fun i => charges i 1 C (drain u)) (action (pickedCov A F T x V k) u) ∧
      Weighted a a B n p d (fun i => charges i 1 C (drain u)) (pickedPi A F T x V k u) ∧
      Weighted a a B n p d (fun _ => C*fee*drain u) (pickedDeficit A F T x V k u) ∧
      Weighted a a B n p d (fun _ => C*fee*drain u^2) (pickedPi A F T x V k u-action Q u) ∧
      ∀ I : Set (Rows.In x A F (G:=G)),
        Weighted (a ∘ (Subtype.val : I → _)) (a ∘ (Subtype.val : I → _)) B n p d
          (fun i => charges i 1 C (drain u)) (action (limitTo Q (Subtype.val : I → _)) u) := by
  intro a C fee Q
  have hf : 0 ≤ fee := (Real.exp_pos _).le
  have ht := mul_nonneg hM hf
  refine ⟨Polar.weighted p h.moves hd hM, Polar.weighted p h.gramJets hd hM, Polar.weighted p h.cJets hd hM,
    ?_,?_,?_,?_⟩
  · unfold C; rw [mul_assoc]; exact Polar.weighted p h.sJets hd ht
  · unfold C; rw [mul_assoc]; exact Polar.weighted p h.inverseGapJets hd ht
  · unfold C; rw [mul_assoc]; exact Polar.weighted p h.toKernelJets.covarianceJets hd ht
  intro u hu
  refine ⟨(h.globalJets u hu).weighted p hu hd hM, (h.covarianceInverse u hu).weighted p hu hd hM,
    (h.windowJets u hu).weighted p hu hd hM, ?_, ?_, fun I => (h.principalJets I u hu).weighted p hu hd hM⟩
  · rw [show C*fee*drain u=activation G n p d*(M*fee*drain u) by unfold C; ring]
    exact Polar.weighted p (h.deficitJets u hu) hd (mul_nonneg ht (drain_pos hu).le)
  rw [show C*fee*drain u^2=activation G n p d*(M*fee*drain u^2) by unfold C; ring]
  exact Polar.weighted p (h.closenessJets u hu) hd (mul_nonneg ht (sq_nonneg _))

lemma monitors (G : Gauge) (L : Side) : ∀ᶠ x : ℝ in atTop,
    0 < temp x ∧ temp x ≤ 1 ∧ temp x ≤ 2*fiery G x L := by
  have hT : Tendsto temp atTop (𝓝 0) := by simpa using! YM.Work.E09.radiusB_temp 0
  filter_upwards [eventually_gt_atTop 0,hT.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1)),
    Work.E07.temp_coarse_le G L] with x hx ht hh
  exact ⟨Work.E09.temp_pos hx,ht,hh⟩
end YM.AnalyticBridge.SectorAffine
