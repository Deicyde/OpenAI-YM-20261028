import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Core
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Letters
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.GridCost

/-!
Recenter the true local physical read U(V) at its *own* point; include
noncommutative increments and `replica` velocity. Transfer pre-mask E
receipts without an inverse-temperature loss from repeated left variations.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Push.SectorMeasure Precision
  FiniteMatrix Push.Local Work.G07
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}
private abbrev Test (G : Gauge) := G.Color × G.Color × G.Mat
private def recentered (p : Test G) := G.plog (G.mat (G.lieExp p.2.1) * (1+p.2.2) * star (G.mat (G.lieExp p.1)))

structure Changes (G : Gauge) (k : ℕ) (C : ℝ) : Prop where
  one : 1 ≤ C
  recenter (t : ℝ) (x y : G.Color) : 0 < t → t ≤ 1 → ‖t • x‖ ≤ firstRadius G → ‖t • y‖ ≤ firstRadius G →
    Towers k (dilate recentered t) (dilate recentered t) (x,x,(0:G.Mat)) (y,y,0) (t*C) (t*(C*‖x-y‖))

-- independent of the temperature or L. Compact only in a fixed color test.


-- One relative coarse link; use the Lie prefix estimate (matrix topology costs
-- on one color block only, not on the whole physical space).
def leg (e : Bond c) (V : Config G c) (W : Config G c) := G.mat (W e * (V e)⁻¹)
lemma leg_chart (k : ℕ) (e : Bond c) (V : Config G c) : Chart k (leg e V) V := by
  unfold leg Chart increment Function.comp; simp only [G.mat_mul]
  exact (((G.exp_jet.of_le le_top).comp (contDiff_apply ..)).mul contDiff_const |>.mul contDiff_const).contDiffAt
lemma leg_at (e : Bond c) (V : Config G c) l : leftDerivs (leg e V) l V = linkPrefix e l := by
  let L := ContinuousLinearMap.mul ℝ G.Mat |>.flip (G.mat ((V e)⁻¹))
  have hh : leg e V = L ∘ (fun W : Config G c => G.mat (W e)) := by ext1; exact G.mat_mul ..
  have ht : Chart l.length (fun W : Config G c => G.mat (W e)) V := by
    unfold Chart increment Function.comp; simp only [G.mat_mul]; exact (((G.exp_jet.of_le le_top).comp (contDiff_apply ..)).mul contDiff_const).contDiffAt
  rw [hh, left_linear L l ht le_rfl,left_link]; change _ * _ * G.mat _ = _
  rw [Matrix.mul_assoc, ← G.mat_mul, mul_inv_cancel, G.mat_one, Matrix.mul_one]
lemma link_prefix {e : Bond c} {t B : ℝ} (l : List (Directions G c)) (ht : 0 ≤ t) (hb : 0 ≤ B) (he : ∀ A∈l, ‖A e‖ ≤ t*B) :
    ‖linkPrefix e l‖ ≤ ‖(1:G.Mat)‖ * (t*(G.colorScale*B))^l.length := by
  have hG := G.colorScale_pos
  induction l with
  | nil => simp [linkPrefix]
  | cons v l ih =>
    rw [linkPrefix_cons,List.length_cons,pow_succ]; apply (norm_mul_le ..).trans
    rw [← mul_assoc]; exact mul_le_mul (ih fun i hi => he i (by simp [hi])) (by rw [G.colorMat_norm,mul_left_comm]; gcongr; exact he _ (by simp)) (norm_nonneg _) (by positivity)

def kinematic (G : Gauge) (B : ℝ) (k : ℕ) := ‖(1:G.Mat)‖*(1+G.colorScale*B)^k
lemma kinematic_nn {B : ℝ} (h : 0 ≤ B) (k : ℕ) : 0 ≤ kinematic G B k := by have := G.colorScale_pos; unfold kinematic; positivity
lemma leg_budget {D : Directions G c → Prop} {t B : ℝ} (k : ℕ) (V : Config G c) (e : Bond c) (ht : 0<t) (hr : t≤1) (hb : 0≤B) (he : ∀ A, D A → ‖A e‖ ≤ t*B) :
    Bound k D V (fun W => t⁻¹ • (leg e V W-1)) (kinematic G B k) 1 := by
  let L := t⁻¹ • ContinuousLinearMap.id ℝ G.Mat
  have hg := leg_chart k e V; have hG := G.colorScale_pos
  have he1 : Chart k (fun W => t⁻¹ • (leg e V W-1)) V := (hg.sub (g:=fun _ => (1:G.Mat)) contDiffAt_const).const_smul t⁻¹
  refine ⟨he1,kinematic_nn hb k,zero_le_one,fun l hl hh => ?_⟩
  rw [one_pow,mul_one]; change ‖leftDerivs (L ∘ (fun W => (leg e V W - 1))) l V‖ ≤ _
  have hQ : Chart k (fun W : Config G c => leg e V W - (1:G.Mat)) V := hg.sub contDiffAt_const
  have hS : (fun W : Config G c => leg e V W - (1:G.Mat)) = leg e V + (fun _ => -(1:G.Mat)) := funext fun W => sub_eq_add_neg _ _
  erw [left_linear L l hQ hl, hS, Push.Local.left_add l hg contDiffAt_const hl, Work.G07.left_const]
  split
  next hn => subst l; simpa [leg,L,leftDerivs] using (kinematic_nn (G:=G) hb k)
  next hn =>
    have hr' : t^l.length ≤ t := pow_le_of_le_one ht.le hr (List.length_pos_iff_ne_nil.mpr hn).ne'
    rw [add_zero, leg_at]; change ‖t⁻¹ • linkPrefix e l‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le,inv_mul_le_iff₀ ht]
    apply (link_prefix l ht.le hb (fun A h => he A (hh _ h))).trans
    have ha : 1 ≤ 1+G.colorScale*B := by nlinarith
    have hz := (pow_le_pow_left₀ (mul_nonneg hG.le hb) (le_add_of_nonneg_left (show (0:ℝ)≤1 by norm_num)) l.length).trans (pow_le_pow_right₀ ha hl)
    rw [mul_pow,kinematic,mul_left_comm t]; gcongr

namespace Kernel
variable {I J ρ : Type} [Fintype I] [Fintype J] [Fintype ρ] (h h' : Kernel G c I J ρ)
    (S : StepData c f) (P : Location f I J) (V : Config G c) (t g : ℝ)

def wheel (i : I) (W : Config G c) := let e := P.address (.inl i)
  (t⁻¹ : ℝ) • (G.mat (replica S.ratio W e * (replica S.ratio V e)⁻¹)-1)

def probes (i : I) (W : Config G c) :=
  ((t⁻¹ : ℝ) • h.stage g V i,(t⁻¹ : ℝ) • h.stage g W i, wheel S P V t i W)

def pivot (W : Config G c) : Directions G f := fun e =>
  (t⁻¹ : ℝ) • G.plog (G.mat (h.atLinks S P g W e * (h.atLinks S P g V e)⁻¹))
lemma pivot_read {t : ℝ} (i : I) (W : Config G c) (ht : 0 < t) :
    h.pivot S P V t g W (P.address (.inl i)) = (t⁻¹ : ℝ) • dilate recentered t (h.probes S P V t g i W) := by
  unfold pivot; rw [west_link,west_link]; unfold probes wheel recentered dilate; simp only [Prod.smul_fst, Prod.smul_snd,
    smul_inv_smul₀ ht.ne', add_sub_cancel]; simp [mul_inv_rev, G.mat_mul,G.mat_inv,Matrix.mul_assoc]
lemma pivot_fixed {e : Bond f} (W : Config G c) (he : ¬∃ i, P.address (.inl i)=e) :
    h.pivot S P V t g W e=0 := by
  unfold pivot atLinks; rw [dif_neg he,dif_neg he]; split <;> simp
lemma pivot_zero : h.pivot S P V t g V=0 := by ext; simp [pivot]

variable {h h' g V} {k : ℕ} {C B a b t : ℝ} {D : Directions G c → Prop}

structure Exposure (h h' : Kernel G c I J ρ) (g t : ℝ) (k : ℕ) (D : Directions G c → Prop) (V : Config G c) (B a b : ℝ) : Prop where
  step_pos : 0 ≤ B
  size : 0 ≤ a
  err : 0 ≤ b
  parent (A : Directions G c) : D A → ∀ i : I, let e := P.address (.inl i)
      ‖A (S.ratio.parent e.1,e.2)‖ ≤ t * B
  stage (i : I) : Compare k D V ((t⁻¹:ℝ) • (h.stage g · i)) ((t⁻¹:ℝ) • (h'.stage g · i)) a b 1
  west (i : I) : ‖h.stage g V i‖ ≤ firstRadius G
  east (i : I) : ‖h'.stage g V i‖ ≤ firstRadius G

def pivotCost (G : Gauge) (k : ℕ) (B a C : ℝ) := compositionCost k (a+kinematic G B k)*C
lemma pivot_bill (ht : 0<t) (ht' : t≤1) (H : Exposure S P h h' g t k D V B a b) (hC : Changes G k C) :
    Compare k D V (h.pivot S P V t g) (h'.pivot S P V t g) (pivotCost G k B a C) (pivotCost G k B a C * ((1+k)*b)) 1 := by
  let X := a + kinematic G B k
  have hk := kinematic_nn (G:=G) H.step_pos k
  have hx : 0 ≤ X := add_nonneg H.size hk
  have hl : 0 ≤ pivotCost G k B a C := mul_nonneg (zero_le_one.trans (compositionCost_one k hx)) (zero_le_one.trans hC.one)
  have hδ := H.err
  have hD : 0 ≤ pivotCost G k B a C * ((1+k)*b) := by positivity
  refine Compare.pi (fun i => ?_) hl hD zero_le_one
  by_cases hi : ∃ j : I, P.address (.inl j)=i
  · obtain ⟨j,rfl⟩ := hi; set e := P.address (.inl j)
    have he (u : Kernel G c I J ρ) : t • ((t⁻¹:ℝ) • u.stage g V j) = u.stage g V j := smul_inv_smul₀ ht.ne' _
    have Hx (u : Kernel G c I J ρ) : u.probes S P V t g j V = ((t⁻¹:ℝ) • u.stage g V j,(t⁻¹:ℝ) • u.stage g V j,0) := by simp [probes,wheel]
    have hw : Bound k D V (wheel S P V t j) (kinematic G B k) 1 := by
      unfold wheel replica; dsimp only; split
      next hh => simpa using Bound.const (k:=k) (D:=D) (V:=V) (0:G.Mat) (norm_zero.trans_le hk) zero_le_one
      exact leg_budget _ _ _ ht ht' H.step_pos (fun A h => H.parent A h j)
    have hs := (H.stage j).weaker (le_add_of_nonneg_right hk) le_rfl le_rfl
    have hc (u : Kernel G c I J ρ) W := u.pivot_read S P V g j W ht
    dsimp only [e]; simp_rw [hc]
    have hd : Compare k D V (h.probes S P V t g j) (h'.probes S P V t g j) X b 1 := (Compare.const _ _ hs.west.value hs.east.value hs.swing.value zero_le_one).prod_mk
      (hs.prod_mk ((Compare.same hw).weaker (le_add_of_nonneg_left H.size) hδ le_rfl))
    have Ht := hC.recenter t _ _ ht ht' ((he h).symm ▸ H.west j) ((he h').symm ▸ H.east j)
    rw [← Hx,← Hx] at Ht
    have hD := (hd.chain Ht).smul_const_left t⁻¹
    refine hD.weaker (le_of_eq (by rw [abs_of_pos (inv_pos.mpr ht)]; unfold pivotCost; change _ = compositionCost k X*C; field_simp)) ?_ le_rfl
    rw [abs_of_pos (inv_pos.mpr ht),pivotCost]; change _ ≤ compositionCost k X*C*_
    have H := (H.stage j).swing.value
    have := hC.one
    have he (x y c k : ℝ) : t⁻¹*(x*(t*(c*y)+k*(t*c)*b))=x*c*(y+k*b) := by field_simp
    rw [he]; simp only [Pi.smul_apply] at H; gcongr
    linarith
  simp_rw [pivot_fixed _ _ _ _ _ _ _ hi]; exact (Compare.const 0 0 (by simpa) (by simpa) (by simpa) zero_le_one)

lemma pivot_germ (ht : 0<t) (he : Chart k (h.stage g) V) : h.atLinks S P g ∘ increment V =ᶠ[𝓝 0]
    fun y => increment (h.atLinks S P g V) (t • h.pivot S P V t g (increment V y)) := by
  suffices ht : ∀ i, ∀ᶠ y in 𝓝 (0:Directions G c), h.atLinks S P g (increment V y) i =
      increment (h.atLinks S P g V) (t • h.pivot S P V t g (increment V y)) i by
    filter_upwards [eventually_all.mpr ht] with y hy using funext hy
  intro i
  have hx : ContinuousAt (fun y => h.atLinks S P g (increment V y) i) (0:Directions G c) := by
    unfold atLinks; split
    · rename_i hx
      have hq : ContinuousAt (fun y => h.stage g (increment V y) hx.choose) 0 := (continuous_apply hx.choose).continuousAt.comp he.continuousAt
      refine (G.lieExp_cont.continuousAt.comp hq).mul ?_
      unfold replica; split
      · exact continuousAt_const
      let j := (S.ratio.parent i.1,i.2)
      exact (show Continuous (fun y : Directions G c => increment V y j) from (G.lieExp_cont.comp (continuous_apply j)).mul (continuous_const (y:=V j))).continuousAt
    · exact continuousAt_const
  let u (y : Directions G c) := h.atLinks S P g (increment V y) i * (h.atLinks S P g V i)⁻¹
  have hu : Tendsto u (𝓝 0) (𝓝 1) := by rw [← show u 0=1 by simp [u]]; exact hx.mul continuousAt_const
  filter_upwards [hu.eventually G.plog_right] with y hy
  simp only [increment,pivot, Pi.smul_apply,smul_inv_smul₀ ht.ne']; rw [hy]; unfold u; group

lemma Exposure.stage_chart (H : Exposure S P h h' g t k D V B a b) (ht : 0 < t) : Chart k (h.stage g) V ∧ Chart k (h'.stage g) V := by
  have he (u : Kernel G c I J ρ) (j:I) (hu : Chart k ((t⁻¹:ℝ) • (u.stage g · j)) V) : Chart k (u.stage g · j) V := by
    simpa [Chart,Function.comp_def,smul_inv_smul₀ ht.ne'] using hu.const_smul t
  exact ⟨contDiffAt_pi.mpr (fun j => he h j (H.stage j).west.smooth),contDiffAt_pi.mpr fun j => he h' j (H.stage j).east.smooth⟩

def fieldCost (G : Gauge) (k : ℕ) (B a C M : ℝ) := compositionCost k (pivotCost G k B a C)*M

lemma through {p : BudgetPoint} (H : Exposure S P h h' g p.threshold k D V B a b) (hC : Changes G k C) {M u v : ℝ} (hP : Polar k M)
    {o : Site f} {F F' : Config G f → ℝ}
    (hH : Diagonals k p o (h.atLinks S P g V) (h'.atLinks S P g V) F F' u v) :
    Compare k D V (F ∘ h.atLinks S P g) (F' ∘ h'.atLinks S P g) (fieldCost G k B a C M*u)
      (fieldCost G k B a C M*(v + k*u*pivotCost G k B a C*((1+k)*b))) 1 := by
  have ⟨hW,hE⟩ := H.stage_chart S P p.threshold_pos
  have hf := pivot_bill S P p.threshold_pos p.threshold_le H hC
  have ht := hH.transfer hP
  nth_rw 1 [← h.pivot_zero S P V p.threshold g] at ht
  nth_rw 1 [← h'.pivot_zero S P V p.threshold g] at ht
  have hu := (hf.chain ht).congr (g:= F ∘ h.atLinks S P g) (g':= F' ∘ h'.atLinks S P g) ((pivot_germ S P p.threshold_pos hW).fun_comp F) ((pivot_germ S P p.threshold_pos hE).fun_comp F')
  exact hu.weaker (le_of_eq (by rw [fieldCost,mul_assoc])) (le_of_eq (by unfold fieldCost; ring)) le_rfl
end Kernel
end YM.AnalyticBridge.MarginalMultiplier3b1d
