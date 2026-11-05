import YM.UVExtension.Lamppost.Meter
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Metric Filter Topology Set BoundedContinuousFunction Complex RG Push.AbsoluteSums
open scoped BigOperators ContDiff Classical
variable {A B : Type*} {M:Meter A B} {Z D : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

structure Opening (D Z:Type*) [NormedAddCommGroup Z] [NormedSpace ℂ Z] where
    call : D → Z
    span : Set Z
    within i : call i∈span
    agrees (f g:Z→ℂ) : Bumps span f → Bumps span g → (∀ i, f (call i)=g (call i))→ EqOn f g span
variable (M : Meter A B) (T : Opening D Z)
-- can quote on smaller domain than on which hol needed. Here relative to survey.
structure Atlas (M:Meter A B) (T:Opening D Z) (r:D → M.Slot) (b:Z→ℝ) where
    f : Z→M.CSlot
    exacts (d i k) : f (T.call d) i k=(r d i k:ℂ)
    pulse i k : Bumps T.span (fun z=>f z i k)
    bounds z : z∈T.span → M.MeasureP (f z) (b z)
namespace Meter
lemma income {w:M.Slot} (k:M.Finger) {f:M.CSlot} (h:∀ i d,(w i d:ℂ)=f i d) : (Finger.effect M k w:ℂ)=Finger.issue M k f:=by
  unfold Finger.effect Finger.issue; push_cast; refine Finset.sum_congr rfl fun x _=>?_ ; unfold padding; cases k.engage x <;> simp [h]
lemma pollen {Z : Set Z} {f : _ → M.CSlot} (p : ∀ i k, Bumps Z (fun z=> f z i k)) (k:M.Finger) : Bumps Z (fun z=>Finger.issue M k (f z)) := by
  unfold Finger.issue; apply bend_finset; intro i _; unfold padding; cases k.engage i
  · simp only [Option.elim']; exact bumps _ _ (differentiableOn_const _)
  rename_i a; exact bends_smul (f:=fun _=> ((M.cost k.root i:ℂ)*(k.cash i:ℂ))) (p i a) (bumps _ _ (differentiableOn_const _))
end Meter

namespace Atlas
variable {T M} {r:D→M.Slot} {b:Z→ℝ} {x C U : ℝ}
variable {A' B':Type*} {N:Meter A' B'} (s:D→N.Slot)
-- actual receipt linear step
lemma apply_to (F:Atlas M T r b) (hp:∀ z∈T.span,0≤b z ∧ b z ≤ U) (hm:0≤U) (hx:0≤x)
    (h:∀ (S:Finset D) (d:D→ℝ) (m:ℝ), 0≤m → M.MeasureP (fun i k=> ∑ j∈S,d j*r j i k) m →
      N.MeasureP (fun i k=> ∑ j∈S,d j*s j i k) (x*m)):Nonempty (Atlas N T s (fun z=>4*x*b z)) := by
  let f z i:= Meter.Finger.issue M i (F.f z)
  let b' i t:=Meter.Finger.effect M t (r i); let c' i t:= Meter.Finger.effect N t (s i)
  have he i k:f (T.call i) k=↑(b' i k):= (M.income k (fun u p=> (F.exacts ..).symm)).symm
  have hg(t:N.Finger) S (w:D→ℝ) m (hn:0≤m) (hx:∀ i,‖∑ k∈S,w k*b' k i‖≤m):‖∑ k∈S,w k*c' k t‖≤x*m:=by
    have hb := Atlas.exacts F
    have hf: M.MeasureP (fun i k=> ∑ j∈S,w j*r j i k) m:= by
      apply M.clips_real; intro i; rw [Meter.combines]; exact hx i
    have hi:= N.fare (h S w m hn hf) t
    rw [Meter.combines] at hi; exact hi
  choose g₀ he' ht hx' using fun t:N.Finger => bloom T.within (fun i : M.Finger=> M.pollen F.pulse i) he (fun d=>c' d t) (hg t) hx (fun z hz=> ⟨(hp z hz).1,⟨(hp z hz).2,hm⟩,fun i=> M.spare (F.bounds z hz) i⟩) hm
  choose h hh using N.awake
  let g (z:Z) (i:A') (k:N.test i):= (↑(N.cost (h i) i):ℂ)⁻¹*g₀ (N.single i k (h i)) z
  have hf d i k : g (T.call d) i k= ↑(s d i k) := by
    unfold g; rw [ht]; unfold c'; rw [Meter.sel,Complex.ofReal_mul, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hh _|>.ne'))]
  have hw i k : Bumps T.span (fun z=> g z i k):= by
    intro Z u ht hh hv; unfold g; apply DifferentiableOn.const_mul; exact he' _ _ _ ht hh hv
  refine ⟨⟨g,hf,hw,fun v hv=>?_⟩⟩; rw [show 4*x*b v=2*x*b v+2*x*b v by ring]; apply N.c_clips
  intro i; specialize hx' i v hv; apply Eq.trans_le (congr_arg norm ?_) hx'; exact T.agrees _ (g₀ i) (N.pollen hw i) (he' _) (fun j => (N.income i (fun _ _=> (hf ..).symm)).symm.trans (ht i j).symm) hv
end Atlas
end YM.UVExtension.Lamppost
