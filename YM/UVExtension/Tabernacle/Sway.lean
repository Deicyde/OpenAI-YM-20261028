import YM.UVExtension.Oriel.Dial
import YM.UVExtension.Tabernacle.Friends

/-! # Normalized currency & closure. Compatible legal input permutation at fixed N; membership 
    of general complex curves is not assumed. Floor readings are in the same fixed chimes for
    all cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tabernacle
open Function Set Filter Metric Lattice RG Precision Wilson Ovens
open Progress.DirectedRecipe Whirl Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Lamppost Concert BoundedContinuousFunction
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators Classical

section M
variable {X Y: Type}
variable (M:Meter.{0,0,0} X Y)
instance fingers: TopologicalSpace (Meter.Finger M):= ⊥
instance : DiscreteTopology (Meter.Finger M):= discreteTopology_bot _

abbrev Chime := M.Finger→ᵇℂ
open Complex
def vibe (a:M.Slot): Chime M := if h:∃ b:ℝ,M.MeasureP a b then
    ofNormedAddCommGroupDiscrete (fun i=>↑(Meter.Finger.effect M i a)) h.choose (fun i=> (norm_real _).trans_le (M.fare h.choose_spec i))
    else 0

lemma puts {a:M.Slot}(ha:∃ b:ℝ,M.MeasureP a b)(t:M.Finger): vibe M a t=↑(Meter.Finger.effect M t a):=by unfold vibe; rw [dif_pos ha]; rfl
lemma ticks {a:M.Slot}{k:ℝ}(h: M.MeasureP a k)(hk:0≤ k) : ‖vibe M a‖ ≤ k:= by
    apply BoundedContinuousFunction.norm_le hk|>.2; intro i; rw [puts M ⟨k,h⟩,norm_real]; exact M.fare h _
lemma paper {a:M.Slot}{x:ℝ}(h:∃ b,M.MeasureP a b)(he:‖vibe M a‖≤x): M.MeasureP a x:= by
    apply M.clips_real; intro i; have hp:= (norm_coe_le_norm (vibe M a) i).trans he; rwa [puts M h,norm_real] at hp

-- Coordinate-level linearity steps (can't assume arbitrary raw arrays are bounded)
lemma subPrint (a b c:M.Slot)(he:∀ i k,a i k=b i k-c i k)(ha:∃ d,M.MeasureP a d)(hb:∃ d,M.MeasureP b d)(hc:∃ d,M.MeasureP c d): vibe M a=vibe M b-vibe M c:=by
  apply DFunLike.ext; intro i; rw [puts _ ha, BoundedContinuousFunction.sub_apply, puts _ hb,puts _ hc,← Complex.ofReal_sub]; apply congr_arg; unfold Meter.Finger.effect; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; rw [← mul_sub]; unfold Meter.padding; cases i.engage j <;> simp [he]
lemma scalePrint (a b:M.Slot)(c:ℝ)(he:∀ i k,a i k=c*b i k)(ha:∃ d,M.MeasureP a d)(hb:∃ d,M.MeasureP b d): vibe M a=c • vibe M b:=by
  apply DFunLike.ext; intro i; rw [puts _ ha, BoundedContinuousFunction.smul_apply,puts _ hb,← Oriel.rsmul ℂ,smul_eq_mul,← Complex.ofReal_mul]; apply congr_arg; unfold Meter.Finger.effect; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j h=>?_ ; unfold Meter.padding; cases i.engage j <;> simp [he]; ring
end M
variable {G : Gauge} {n : Side}
variable (p : BudgetPoint)

abbrev ChimeE (G:Gauge)(p:BudgetPoint)(n:Side):= fork p G (drawer G n).reg p.supportExponent
abbrev ChimeK (G:Gauge)(p:BudgetPoint)(n:Side):= bell (Pipes.addr (folio G n) p) p.B p.supportExponent
abbrev Readings (G:Gauge)(p:BudgetPoint)(n:Side):= Chime (ChimeE G p n) × Chime (ChimeK G p n)
abbrev sheetE (u:Field G n):= trill p G (drawer G n).reg p.supportExponent u.1
abbrev sheetK (u:Field G n): (ChimeK G p n).Slot:= u.2
def tuningE (u:Field G n):= vibe (ChimeE G p n) (sheetE p u)
def tuningK (u:Field G n):= vibe (ChimeK G p n) (sheetK p u)
def tuning (σ τ:ℝ) (u:Field G n): Readings G p n:= (σ⁻¹ • tuningE p u, τ⁻¹ • tuningK p u)
lemma tickP (σ τ:ℝ) (h:0<σ)(hp:0<τ){u:Field G n}(hR:rake p u){a:ℝ}: ‖tuning p σ τ u‖≤ a ↔ (floor p u).Valid p (a*σ) (a*τ):= by
    obtain ⟨c,C,hK⟩:= hR; let v:= floor p u; have hS:(ChimeE G p n).MeasureP (sheetE p u) c:= (Above.floorE p v).2 hK.boundE; have hT:(ChimeK G p n).MeasureP (sheetK p u) C:= (Above.floorK p v).2 hK.boundK
    unfold tuning; simp only [Prod.norm_def,norm_smul,norm_inv,Real.norm_of_nonneg h.le,Real.norm_of_nonneg hp.le,max_le_iff]
    constructor
    · intro hx
      refine {hK with boundE:= (Above.floorE p v).1 (paper (ChimeE G p n) ⟨c,hS⟩ ?_),boundK:= (Above.floorK p v).1 (paper (ChimeK G p n) ⟨C,hT⟩ ?_)}
      · rw [mul_comm]; exact (inv_mul_le_iff₀ h).mp hx.1
      rw [mul_comm]; exact (inv_mul_le_iff₀ hp).mp hx.2
    intro he
    obtain ⟨f,hf,hQ⟩:=he.boundK; have hy:=budget_nonneg (hQ 0); have ha:0≤a:=nonneg_of_mul_nonneg_left hy hp
    exact ⟨(inv_mul_le_iff₀ h).2 ((ticks (ChimeE G p n) ((Above.floorE ..).2 he.boundE) (by positivity)).trans_eq (mul_comm ..)),(inv_mul_le_iff₀ hp).2 ((ticks _ ((Above.floorK p v).2 he.boundK) hy).trans_eq (mul_comm ..))⟩

namespace Charm
variable (d:Tabernacle.Charm G p n) (σ τ:ℝ)
private lemma earnsE (x:d.Shed p): ∃ b, (ChimeE G p n).MeasureP (sheetE p x.val) b:= by
   obtain ⟨b,c,h⟩:= (d.income p x).1; exact ⟨_,(Above.floorE ..).2 h.boundE⟩ -- '-' may need
private lemma earnsK (x:d.Shed p): ∃ b, (ChimeK G p n).MeasureP (sheetK p x.val) b:= by
   obtain ⟨a,b,h⟩:= (d.income p x).1; exact ⟨_,(Above.floorK ..).2 h.boundK⟩
private lemma washE (x y:d.Shed p): tuningE p (x-y).val= tuningE p x.val- tuningE p y.val:=by
  obtain ⟨a,A,h⟩:= (d.income p x).1; obtain ⟨b,B,h'⟩:= (d.income p y).1; refine subPrint _ _ _ _ (fun i k=>?_) (d.earnsE p _) (d.earnsE p _) (d.earnsE p _)
  let q:= (drawer G n).reg i; let t:Concert.Tap p G q.site q.support:= k
  exact left_sub ((h.regular.smooth i).smooth t.view t.live) ((h'.regular.smooth i).smooth t.view t.live) t.card
private lemma washable (x y:d.Shed p): tuning p σ τ (x-y).val = tuning p σ τ x.val - tuning p σ τ y.val:=by
  have hz : tuningK p (x-y).val= tuningK p x.val-tuningK p y.val:= subPrint _ _ _ _ (fun i k=> rfl) (d.earnsK p _) (d.earnsK p _) (d.earnsK p _)
  unfold tuning; rw [hz,washE,smul_sub,smul_sub]; rfl
private lemma scalar (x:d.Shed p)(c:ℝ): tuning p σ τ (c • x).val=c • tuning p σ τ x.val:=by
  have hz:tuningE p (c • x).val=c • tuningE p x.val:= scalePrint _ _ _ c (fun i k=> by let t :Concert.Tap p G ((drawer G n).reg i).site ((drawer G n).reg i).support:= k; exact WilsonStartup.Start.left_mult c t.poll t.view) (d.earnsE p _) (d.earnsE p _)
  have hp:tuningK p (c • x).val=c • tuningK p x.val:= scalePrint _ _ _ c (fun i k=> rfl) (d.earnsK p _) (d.earnsK p _)
  unfold tuning; rw [hz,hp,smul_comm _ c,smul_comm τ⁻¹ c]; rfl

def hue : d.Shed p →ₗ[ℝ] Readings G p n where
    toFun t:= tuning p σ τ t.val
    map_add' x y:=by rw [← sub_neg_eq_add, d.washable,← neg_one_smul ℝ y,d.scalar]; simp
    map_smul' a x:= d.scalar ..
end Charm
end YM.UVExtension.Tabernacle
