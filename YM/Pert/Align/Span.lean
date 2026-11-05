import YM.Pert.Align.Recoil
import YM.Push.FINITE_DETECTION.Signed
/-!
# Bilinear coordinate calculus for open-leg stencils
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Align
open Maxwell Function Atom Filter Topology RingHom YM.Next.Rank.Radian Tensor
open scoped BigOperators Classical
variable {j k : ℕ} {G : Gauge}
abbrev Pad (G : Gauge) (j : ℕ) := Module.Dual ℝ (YM.Pert.Bare.Response G j)
structure Spot (G : Gauge) (j : ℕ) where
  slash : Axis
  via : Axis
  γ : Fin j→Axis
  color : G.ColorIndex
  deriving DecidableEq, Fintype
namespace Spot
 def atom (v : Spot G j) (s : Signed) : Atom j := ⟨s,v.γ,v.slash,v.via⟩
 def meter (v : Spot G j) : Pad G j := probes (unitColor G v.color) (v.atom 1)
 def impulse (v : Spot G j) (f g : Axis) (p : Fin j→Axis) : G.Color := if v.slash=f ∧ v.via=g ∧ v.γ=p then Maxwell.unitColor G v.color else 0
 def freeze (v : Spot G j) : Extended G j := Maxwell.fromF G (basis ∘ v.γ) v.color v.slash v.via
 lemma meter_atom (v : Spot G j) (s : Signed) : v.meter = probes (unitColor G v.color) (v.atom s) := rfl
 lemma impulse_read (v : Spot G j) (f g : Axis) (p : Fin j→Axis) (c : G.ColorIndex) : v.impulse f g p c = if v=(⟨f,g,p,c⟩:Spot G j) then 1 else 0 := by
   cases v with | mk a b t d => by_cases h : a=f∧b=g∧t=p; · obtain ⟨rfl,rfl,rfl⟩ := h; simp [impulse,unitPaint]; split_ifs <;> simp_all
                                dsimp [impulse]; rw [if_neg h, if_neg (by contrapose! h; simp_all)];rfl
end Spot
lemma meter_full (a : YM.Pert.Bare.Response G j): a = ∑ v : Spot G j, (v.meter a) • v.impulse := by
   classical
   dsimp only [Spot.meter]
   funext i l p; ext c
   rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]
   change _=((∑ v:Spot G j, (probes _ _ a : ℝ) • v.impulse i l p):G.Color) c
   simp [WithLp.ofLp_sum, Spot.impulse_read]
   rw [←to_color (a i l p) c]; change inner ℝ (a i l p) (unitColor G c) = inner ℝ (unitColor G c) (a i l p); exact real_inner_comm ..
   -- was rw simp
lemma pad_full (A : Pad G j) : A = ∑ v : Spot G j, A v.impulse • v.meter := by
  apply LinearMap.ext; intro f
  rw [LinearMap.sum_apply, (congrArg A (meter_full f)), map_sum]
  apply Finset.sum_congr rfl; intro v _; rw [A.map_smul]; exact mul_comm _ _
variable {E F I K : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup I] [AddCommGroup K] [Module ℝ E] [Module ℝ F] [Module ℝ I] [Module ℝ K]
abbrev Biform E F [AddCommGroup E] [AddCommGroup F] [Module ℝ E] [Module ℝ F] := E →ₗ[ℝ] F →ₗ[ℝ] ℝ
def under (B : Biform E F) (t : I →ₗ[ℝ] E) (s:K →ₗ[ℝ] F) : Biform I K := (B.compl₂ s).comp t
@[simp] lemma under_at (B : Biform E F) (t : I→ₗ[ℝ] E) (s:K→ₗ[ℝ] F) (a b) : under B t s a b = B (t a) (s b) := rfl
def covMap (B : Biform E F) (t : I →ₗ[ℝ] E) (s:K→ₗ[ℝ] F) := under B t s
lemma cost_free (B : Biform E F) (a b c d) : B (a-b) (c-d) = B a c - B a d - (B b c - B b d) := by rw [B.map_sub,LinearMap.sub_apply,map_sub,map_sub]
def pickDual (t : E →ₗ[ℝ] I) : Module.Dual ℝ I →ₗ[ℝ] Module.Dual ℝ E where
  toFun a := a.comp t
  map_add' a b := by ext z; rfl
  map_smul' a b := by ext z; rfl
@[simp] lemma pickDual_apply (t : E→ₗ[ℝ] I) (a) : pickDual t a = a.comp t := rfl
lemma upgrade {I K : Type*} [Fintype I] [Fintype K] (p : I→E) (z : I→ℝ) (q : K→F) (r : K → ℝ) (A B : ℕ→Biform E F)
    (H : ∀ i j, Tendsto (fun t=> A t (p i) (q j)-B t (p i) (q j)) atTop (𝓝 (0:ℝ))) : Tendsto (fun t =>
       (A t (∑ i:I,z i • p i) (∑ j:K,r j • q j) - B t (∑ i:I,z i • p i) (∑ j:K,r j • q j))) atTop (𝓝 0) := by
  have e (i) (j) := ((H i j).const_mul (r j)).const_mul (z i)
  -- function rewriting equality under congr
  simp only [map_sum,map_smul, ←Finset.sum_sub_distrib,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul] at *
  have H := tendsto_finsetSum Finset.univ fun i (_:i∈Finset.univ) => tendsto_finsetSum Finset.univ fun j (_:j∈Finset.univ) => e i j
  simp only [mul_zero,Finset.sum_const_zero] at H; apply H.congr; intro t
  simp_rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  -- normalize double sum order
  nth_rw 2 [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
lemma surge (A B : ℕ→Biform (Pad G j) (Pad G k)) (h : ∀ v w, Tendsto (fun i => A i (Spot.meter v) (Spot.meter w) - B i (Spot.meter v) (Spot.meter w)) atTop (𝓝 (0:ℝ))) (Q : Pad G j) (S : Pad G k) :
   Tendsto (fun t=>A t Q S - B t Q S) atTop (𝓝 0)  := by
    have e (B : Pad G j → Pad G k → ℝ) : B Q S = B (∑ v : Spot G j, Q v.impulse • v.meter) (∑ v : Spot G k,S v.impulse • v.meter) := congrArg₂ B (pad_full Q) (pad_full S)
    -- q unused
    simp_rw [show ∀ t, A t Q S = A t (∑ v : Spot G j,Q v.impulse • v.meter) (∑ v : Spot G k,S v.impulse•v.meter) from fun t=>e (fun i j=>A t i j), show ∀ t, B t Q S = _ from fun t=> (e fun i j=> B t i j)]; apply upgrade _ _ _ _ A B h
end YM.Pert.Align
