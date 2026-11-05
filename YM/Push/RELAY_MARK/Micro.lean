import YM.Next.FOUNDATIONS.SU2
import YM.Push.RELAY_MARK.Wilson
import YM.Work.B06

/-!
# Full spectator locality for equation cylinders

Radius and cutoff-side conditions are in **lattice** units; no interpolated
field or phase read. `Micro` is suitable for one section stencil per d
fixed once and for all before building the family. The equation identity
in this API is stronger than the ordered-tail one. It concerns all positions
windings etc. (from the stated side on), all multipliers satisfying the
stencil, and does not require the spectator to be continuous or gauge invariant.
We also record how to *produce* it from Haar identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark

open Lattice Wilson Filter Function MeasureTheory Set
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

variable {G : Gauge} {n : Side}

abbrev Pre (G : Gauge) := CoverConfig G → ℂ

def Outer (r : ℕ) (o : Site n) := {x : Site n | r < separation x o}

def MicroAt (f : Pre G) (r M : ℕ) := ∀ n : Side, M ≤ n.val → ∀ o : Site n,
    ∀ β : ℝ, β ≠ 0 → ∀ S : Config G n → ℂ, LocalOn (Outer r o) S → RG.Envelope S →
    moment β (fun U => f (expandAt o U) * S U)=0

def Micro (f : Pre G) := Continuous f ∧ ∃ r M : ℕ, MicroAt f r M

lemma onStencil (o : Site n) {α : Type*} [TopologicalSpace α] {f : CoverConfig G → α} (h : Continuous f) :
    Continuous (f ∘ expandAt o) := h.comp <| continuous_pi fun _ => continuous_apply _

namespace MicroAt
variable {f g : Pre G} {r M s N : ℕ}

lemma mono (h : MicroAt f r M) (h1 : r ≤ s) (h2 : M ≤ N) : MicroAt f s N := by
  intro n hn o β hb S hS hE
  exact h n (h2.trans hn) o β hb S (fun U V H => hS U V (agrees_mono H fun _ ht => lt_of_le_of_lt h1 ht)) hE

lemma zero (G : Gauge) (r M : ℕ) : MicroAt (0 : Pre G) r M := by
  intro n hn o β hb S hS hE
  simp [moment]

lemma add (hf : MicroAt f r M) (hg : MicroAt g r M) (hF : Continuous f) (hG : Continuous g) : MicroAt (f+g) r M := by
  intro n hn o β hb S hS hE
  have he := hf n hn o β hb S hS hE
  have hl := hg n hn o β hb S hS hE
  unfold moment at *
  simp only [Pi.add_apply,add_mul]
  apply Eq.trans (integral_add (times_integrable (μ:=law G n β) (onStencil o hF) hE)
    (times_integrable (onStencil o hG) hE))
  exact (congr_arg₂ _ he hl).trans (add_zero _)

lemma scale (hf : MicroAt f r M) (c : ℂ) : MicroAt (c • f) r M := by
  intro n hn o β hb S hS hE
  have he := hf n hn o β hb S hS hE
  unfold moment at *
  simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul, he, mul_zero]

lemma conj (hf : MicroAt f r M) : MicroAt (star f) r M := by
  intro n hn o β hb S hS hE
  have hL : LocalOn (Outer r o) (star S) := fun U V H => congr_arg star (hS U V H)
  obtain ⟨hB,K,hK⟩ := hE
  have he := hf n hn o β hb (star S) hL
    ⟨(continuous_star (R:=ℂ)).measurable.comp hB, K, fun U => by simpa using hK U⟩
  unfold moment at *
  rw [← star_zero ℂ, ← he,Complex.star_def,← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards with U
  simp

/-- Pull of a full spectator test; needs no invariance of S. -/
lemma turn_local {K L : Set (Site n)} {F : Config G n → ℂ} (h : LocalOn K F) (s : Signed)
    (b : Site n) (hs : MapsTo (affine s b) K L) : LocalOn L (F ∘ pull s b) := by
  intro U V hh; apply h
  intro p hp he
  let d := (posDir p.2).rotate s
  let x := affine s b p.1
  have hu : x ∈ L := hs hp
  have hv : x + d.vec ∈ L := by
    have H : x + d.vec = affine s b (p.1 + step p.2) := by
      unfold x d; rw [Step.vec_rotate, Step.vec_pos]; simp only [affine, Signed.act_add]; abel
    rw [H]; exact hs he
  change d.read U x = d.read V x
  generalize d = D at *
  rcases D with ⟨i,t|t⟩
  · exact hh (x,i) hu hv
  change (U (x-step i,i))⁻¹ = (V (x-step i,i))⁻¹
  rw [hh]; exacts [by simpa [Step.vec,sub_eq_add_neg] using hv,by simpa [x] using hu]

private lemma pull_cancels (q : Signed) (o : Site n) (U : Config G n) :
    pull q⁻¹ (o-q⁻¹.act o) (pull q (o-q.act o) U) = U := by
  rw [pull_pull,mul_inv_cancel]
  simp [affine]

lemma signed (hf : MicroAt f r M) (hF : Continuous f) (q : Signed) :
    MicroAt (f ∘ pull q (0:Cover)) r M := by
  intro n hn o β hb S hS hE
  let b (q : Signed) := o-q.act o
  have he (q : Signed) : affine q (b q) o=o := by unfold affine b; abel
  let Y := S ∘ pull q⁻¹ (b q⁻¹)
  have hy : RG.Envelope Y := by
    obtain ⟨T,hT⟩ := hE.cost
    exact ⟨hE.meas.comp (continuous_pull ..).measurable,T,fun V => hT _⟩
  have hw : LocalOn (Outer r o) Y := turn_local hS _ _ (fun x hx => by
    change r < separation _ _; nth_rw 1 [← he q⁻¹]
    simp only [affine,separation_translate,separation_signed]; exact hx)
  let Q := fun U => f (expandAt o U) * Y U
  have ht (U : Config G n) : f (pull q (0:Cover) (expandAt o U)) * S U = Q (pull q (b q) U) := by
    unfold Q Y; rw [expandAt_pull, he, comp_apply,pull_cancels]
  change moment β (fun U => f (pull q _ (expandAt o U)) * S U) = _
  simp_rw [ht]
  exact (moment_pull β q _ Q (times_integrable (onStencil o hF) hy)).trans (hf n hn o β hb Y hw hy)
end MicroAt

lemma continuousPull (s : Signed) : Continuous (pull s (K:=G.El) (0:Cover)) := by
  apply continuous_pi; intro i
  unfold pull Step.read; split <;> fun_prop

namespace Micro
variable {f g : Pre G}
lemma add (hf : Micro f) (hg : Micro g) : Micro (f+g) := by
  obtain ⟨r,m,h⟩ := hf.2; obtain ⟨s,M,H⟩ := hg.2
  exact ⟨hf.1.add hg.1, max r s, max m M,
    (h.mono (le_max_left ..) (le_max_left ..)).add (H.mono (le_max_right ..) (le_max_right ..)) hf.1 hg.1⟩

lemma scale (c : ℂ) (hf : Micro f) : Micro (c • f) := by
  obtain ⟨r,M,h⟩ := hf.2
  exact ⟨hf.1.const_smul _,r,M,h.scale c⟩

lemma conj (hf : Micro f) : Micro (star f) := by
  obtain ⟨r,M,h⟩ := hf.2
  exact ⟨hf.1.star,r,M,h.conj⟩

lemma signed (hf : Micro f) (q : Signed) : Micro (f ∘ pull q 0) := by
  obtain ⟨r,M,h⟩ := hf.2
  exact ⟨hf.1.comp (continuousPull _),r,M,h.signed hf.1 q⟩

end Micro

def micros (G : Gauge) : Submodule ℂ (Pre G) where
  carrier := {f| Micro f}
  zero_mem' := ⟨continuous_const,0,0,MicroAt.zero G 0 0⟩
  add_mem' h k := Micro.add h k
  smul_mem' t _ h := Micro.scale t h

end YM.Push.Mark
