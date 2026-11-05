import YM.RG08.Loom.Sole
/-!
# One triangular chart with mark tested for Ward, θ-independent

Unmasked finite dimensional periods, estimates auxiliary around flat to
establish identities within same formal convention. Doesn't estimate real
physical masks.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent PertExtension.Chart
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {p c f : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable (M : Matrix (Body 1 f) (Body 1 c) ℝ) (v : ℝ→Link G c) (n h : ℕ) (K B : FreeResolvent.FaceRow) (σ : ChartRatio G)
variable (F : Air G) (V : ℕ→Config G f→ℝ) (W : Site S.ratio.count → ℕ→Config G f→ℝ) {D : ℕ}{R : ℝ} (τ : ℕ) (o : Site c) (U : BoardU D R G)(φ : Exam D) (κ : S.Choices) (i : G.ColorIndex)
local notation "A" => FreeResolvent.Active G T→ℝ
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ
local notation "⌂" => tangent G T.Free
local notation "Ξ" => treeMatrix G S T K
local notation "Σ'" => surge S G F i σ
local notation "E₀" => expEra Σ'
local notation "P_K" => (quad G (YM.RG08.hessian K))
local notation "P_B" => (quad G (YM.RG08.hessian B))
local notation "Ω" => regal S G T M v κ n V P_B
local notation "☉" => nibble S G T M v σ
local notation "Χ" => heated S G T M v
local notation "B'" => valve G U S φ h τ o
local notation "Γ" => chapel G S n W τ h
local notation "Υ" => hatsScale S T σ * Real.exp (-1)
local notation "W_" j => (fun k l=> plug (Scores.Pages.roll (spinner j) (S.ratio.count.val:ℝ)⁻¹ φ) R ∘ U k l)
local notation "z_" j => (S.ratio.assemble (o,j))

lemma charter (ht : ∀ i p,Measurable (W i p))(X : Type) [MeasurableSpace X] {u : X→ℝ} (hu : Measurable u) {w : X→ Config G f}(hw : Measurable w): Measurable fun x=> Γ (u x) (w x) := by unfold chapel; exact Finset.measurable_fun_sum _ (fun i _=> measurable_const.mul (Finset.measurable_fun_sum _ (fun j _=> (hu.pow_const _).mul ((ht i j).comp hw))))

def papyrus (P : Z) := Γ P.2 (input G f (fineL G S.ratio (chic S G T M v P))) * ☉ P
local notation "Υ₁" => papyrus S G T M v n h σ W τ
lemma paper_lamp (ht : ∀ i p, Shell G f (W i p)) (hf: ContDiffAt ℝ ω v 0) (he:LocalRatio σ) : ContDiffAt ℝ ω Υ₁ 0 := by
  unfold papyrus chapel
  apply ContDiffAt.mul _ (nibble_fit S G T M v σ he hf)
  have hh : ContDiffAt ℝ ω (fun p:Z=> fineL G S.ratio (chic S G T M v p)) 0 := (fineL G S.ratio).contDiff.contDiffAt.comp _ (chic_fit S G T M v hf)
  have hx : fineL G S.ratio (chic S G T M v 0)=0 := by rw [chic_zero,map_zero]
  exact ContDiffAt.sum (fun i _=> contDiffAt_const.mul (ContDiffAt.sum fun j _=> (contDiffAt_snd.pow j).mul ((show ContDiffAt ℝ ω (W i j ∘ input G f) (fineL G S.ratio (chic S G T M v 0)) from hx.symm ▸ (ht i j).hol).comp (f:=fun p:Z=> fineL G S.ratio (chic S G T M v p)) _ hh)))
lemma paper_bills (ht : ∀ i p, Shell G f (W i p)) (hv : Measurable v) (hD : LocalRatio σ) : Measurable Υ₁ :=
  (charter S G n _ W _ (fun i p=>(ht i p).measure) _ measurable_snd (input_cont.measurable.comp ((fineL G S.ratio).continuous.measurable.comp (chic_meas S G T M v hv)))).mul (nibble_meas S G T M v σ hD hv)
def beam (t : ℝ) (x : A) := year (fun j t=> billow B' E₀ j (Χ t x)) n t
local notation "β" => beam S G T M v n h σ F τ o U φ i
lemma beam_event (hp : ContDiffAt ℝ ω v 0) : Meadow β := by
  have he j : Meadow (fun (t:ℝ) (x:A)=> valve G U S φ h τ o j (Χ t x)) := by
    refine meadowCompose (dryL o _ _) ?_; intro b
    let m t := (Χ t 0) b; let a (x:A):=(chargeS S T G*ᵥ x) b
    have ha : Grass a := Grass.base (k:=1) (start_hemi ((ContinuousLinearMap.proj (R:=ℝ) b).comp (chargeS S T G).mulVecLin.toContinuousLinearMap|>.analyticAt _) (fun x t=> by simp [a,Matrix.mulVec_smul]))
    have hh : Meadow (fun t:ℝ=>fun _ : A=> m t) := Meadow.work _ (((contDiffAt_pi.mp (heat_lamp S G T M v hp 0)) b).of_le le_top)
    rw [show (fun (t:ℝ)(x:A)=> Χ t x b)=(fun _=>a)+(fun (t:ℝ) (_:A)=>m t) from funext fun t=>funext fun x=>by simp [a,m,Reflect.heated,settler, Matrix.mulVec_zero]; rfl]
    exact (Meadow.single ha).more hh
  have hz (j : ℕ): Meadow (fun (t:ℝ)(x:A)=> billow B' E₀ j (Χ t x)) := by unfold billow; simp only [Finset.sum_apply]; exact Meadow.sums (s:=wheel j) (fun r _=> (he r.1).times (surge_spice S G T M v F i σ hp r.2))
  unfold beam year; exact Meadow.sums (F:=fun i t x=> t^i* billow B' E₀ i (Χ t x)) (fun j _=> (Meadow.work (fun t:ℝ=> t^j) (contDiffAt_id.pow _)).times (hz j))
lemma foot_fit (ha:LocalRatio σ)(he: ContDiffAt ℝ ω v 0) (hp:S.patch.Branches S.kernel G)
    (hg:∀ i',Caper P_K F n i' (V i')) (hF : Gets F)(hA:Halt F)(hk: Whole K) (hB : Whole B)
    (hK : ∀ m,(K.acts m).IsSymm)(hBz : ∀ m,(B.acts m).IsSymm)(hM : Inputs S M (K.acts f) (B.acts c))(hΔ : (Ξ).PosDef)
    (hW : ∀ p j,Cargo (z_ p) τ j (n+τ) (W_ p) (W p j)) (hu : ∀ i j,Pens (U i j)) (hz:1/2≤R) (x : A) :
    Fit (n+1) (fun t=> PertExtension.Series.Radial.projection Υ₁ Ω t (plates G T.Free (maplit G T x)))
        (fun t=> Υ*t^τ * β t x*(crownM hΔ).kern x) := by
  -- distribute papyrus against independent unmarked radial, use exact Fit n+1
  let P:=plates G T.Free (maplit G T x); let E t:=chapel G S n W τ h t (input G f (fineL G S.ratio (t • Χ t x)))
  have hf : (fun t=> PertExtension.Series.Radial.projection Υ₁ Ω t P)=E*(fun t=> PertExtension.Series.Radial.projection ☉ Ω t P) := by
    funext t; unfold papyrus; simp_rw [projection_eq]; dsimp only [E,Pi.mul_apply]; rw [← mul_assoc, show (t•P).2=t from mul_one _,show chic S G T M v (t • P)=_ from chic_ray S G T M v t x]
  have hc:= soaring G S n τ h W hz hu hW (fun t=> Χ t x) ((heat_lamp S G T M v he x).continuousAt)
  have hx:=apertures S G T M v κ n V F K B i σ ha he hp hg hF hA hk hB hK hBz hM x hΔ
  let I j t:= B' j (Χ t x); let p j t:= E₀ j (Χ t x); let H:= Υ * (crownM hΔ).kern x
  let Z' t:=H*year p n t
  have hu' (j): Bill 0 (I j) := life_price ((((dryL o _ _).smooth.continuous.continuousAt).comp ((heat_lamp S G T M v he x).continuousAt)).mono_left nhdsWithin_le_nhds)
  have hy (j) : Bill 0 (p j) := life_price ((surge_spice S G T M v F i σ he j).arc x|>.continuousAt|>.mono_left nhdsWithin_le_nhds)
  have hv : Fit (n+1) (fun t=> PertExtension.Series.Radial.projection ☉ Ω t P) Z' := hx.join (Fit.supply (Eventually.of_forall fun t=> mul_right_comm ..) _) -- may defeq
  let f':=(fun t:ℝ=> t^τ)
  rw [show (fun t => PertExtension.Series.Radial.projection Υ₁ Ω t _) = _ from hf]
  have hR : Fit (n+1) E (f'*year I n) := hc.lower (by omega)
  apply (hR.groups hv (bill_mul (ruler 0 τ (by omega)) (year_bills hu' n)) (bill_mul (bill_const H) (year_bills hy n))).join
  let Y t:=year (Zone.mul I p) n t
  have hL:= (year_mult hu' hy n).scale H ; have h': Fit (n+1) (f'*(H • (year I n*year p n))) (f'*(H • Y)) := by simpa only [zero_add] using hL.right (ruler 0 τ (by omega))
  have he' (j t) : Zone.mul I p j t=billow B' E₀ j (Χ t x) := by unfold billow; rw [Finset.sum_apply]; rfl
  refine Fit.join (Fit.supply ?_ _) (Fit.join h' (Fit.supply ?_ _))
  · apply Eventually.of_forall; intro y; change (_*_) * (H*_) = _*(H*(_*_)); ring
  apply Eventually.of_forall; intro y; change y^τ*(H*Y y)=_; unfold H Y beam year; simp_rw [he']; ring
end YM.RG08.Loom
