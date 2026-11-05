import YM.WilsonBulk.Tickets.Race

/-!
# Full affine-null order in position moments. Use on ANY two Whispers in same convention.
- Rank 2..∞ at coupling e/e top/sub stencil. No assumptions on Ω differences except same normalized.
- Orbits signed & color true in every output propagated by `whispers_post` etc.
- Top will inject local stencil NORMALIZED at all periods BEFORE horizon lifts.

Quantitative continuation NOT on masks! This licenses `<saturated>` h degree replacement of
potential `tele`,`A0` predictors and arbitrary Color slot rotations under projection by transfer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open Lattice Laurent Function Filter Bloch Equiv Matrix Precision Exterior Wilson Pert.Bulk Sheet Atelier Finset
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {V U : Text (Cloth G) 2} {c : Side} {e r n : ℕ} {σ p : ℝ} {I J : Library G}
-- ALL moments after rescaling
abbrev fitting (n : ℕ) := 4-n -- for (n+1) legs; e.g. n=1 tests through quad
def BodyNull (I : Library G) := ∀ e n, TicketNull (fitting n) (I e (n+1))

lemma Regime.difference {U V : Tape (Pennant G c)} (h : Regime U) (he : Regime V) : Regime (U-V) := ⟨fun s b=> by unfold Spins; rw [map_sub,h.spins s b, he.spins s b],fun i=> by rw [map_sub,map_sub, h.dance i,he.dance i]⟩
lemma Whisper.minus (h : Whisper I) (he : Whisper J) : Whisper (I-J) := ⟨h.style.minus he.style,h.cash.minus he.cash,h.palm.minus he.palm, fun n=> by unfold audienceK; rw [h.palm.issued_minus _ he.palm,tape_minus]; exact (h.guns n).difference (he.guns n)⟩

lemma body_shift (h : Whisper I) (hs : G.Simple) (k : G.ColorIndex) (hz : ∀ e,subdue k (I e 2)=0) : BodyNull I := by
  intro e
  induction e using Nat.strong_induction_on with
  | h e ih=>
  intro i; cases i with
  | zero=> rw [color_null h hs]; exact TicketNull.zero _
  | succ i=>
  cases i with
  | zero=> exact lifted_quadratic h hs k (hz e)
  | succ n=>
     by_cases hC:n+1+1<4; swap; · rw [fitting,Nat.sub_eq_zero_of_le (by omega : 4≤n+1+1)]; exact TicketNull.zeroDegree _
     apply ticket_gain (show fitting _ ≤ _ by unfold fitting; omega) (h.palm _ _) (h.style.coherent _ _)
     rw [submission h]; apply TicketNull.scale; apply TicketNull.snipped _ _ (fun x hx=>?_); rw [mem_range] at hx
     apply TicketNull.proceeding; intros hv hu
     exact TicketNull.fewer (ih (e-(x+1)) (by omega) (n+1+1-(x+1))) (by unfold fitting; omega)
-- consumption: subtract projected action from once-prenormalized *at any momentum order*. pair costs.
lemma BodyNull.fuse (h : Whisper I) (he : Whisper J) (k : G.ColorIndex) (hs : G.Simple)
    (hy : ∀ e,subdue k (I e 2) = subdue k (J e 2)) : BodyNull (I-J) := body_shift (h.minus he) hs k (by intro i; rw [Pi.sub_apply,Pi.sub_apply,subdue_minus (he.palm _ _) (h.palm _ _),hy i,sub_self])
end YM.WilsonBulk.Parapet
