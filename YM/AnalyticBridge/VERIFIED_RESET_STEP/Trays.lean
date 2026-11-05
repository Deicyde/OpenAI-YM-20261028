import YM.AnalyticBridge.VERIFIED_RESET_STEP.Channels
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Isotropy
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quotes


/-!
# Reset tap for the DirectedRecipe gathering algorithm

`Listing` is the *early* negative-log and compulsory-family alphabet of
the represented Gaussian answer, with `Source` the actual coefficient
functions (E *before* normalization/subtraction). Its original forced
addresses and every additional discrepancy address enter H01 at once. No
claim that the Gaussian/local/sector estimates producing such a Listing
on the actual step have been proved. The book and e/k addresses need not
be universal across torus sizes, but are held fixed during a parameter
comparison. Extra apertures are then those of DirectedRecipe.finish.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG Ovens Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Progress.DirectedRecipe Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
namespace Collection
structure Listing (G : Gauge) (n : Side) where
  reg : ℕ → RegularAddress n
  hard : ℕ → ForcedAddress G n

structure Source (G : Gauge) (n : Side) where
  logRead : ℕ → Pot G n -- with NEGATIVE sign in exponent
  hardRead : ℕ → Pot G n

def Listing.read (X : Listing G n) (v : Source G n) : Activities G n := ⟨X.reg, X.hard, v.logRead, v.hardRead⟩

structure Local (X : Listing G n) (p : BudgetPoint) (v : Source G n) (H w : ℝ) : Prop where
  smooth i : p.Regular (X.reg i).support (v.logRead i)
  family : (X.read v).ForcedFamily p
  transforms s b : Nonempty ((X.read v).Moves s b)
  cheap : ∃ u, (∀ i, p.supBounds (X.reg i).site (X.reg i).support (v.logRead i) (u i)) ∧ Quotes.early p X.reg u H
  expensive : ∃ k, (∀ i, 0 ≤ k i ∧ ∀ U, ‖v.hardRead i U‖ ≤ k i) ∧ Ac.Hit (fun i => (X.hard i).support) p.B k (p.supportExponent+1) w

abbrev Faces (n : Side) := Seat n × Low
abbrev Spikes (n : Side) := Seat n × High
abbrev EKey (n : Side) := ℕ ⊕ (Faces n ⊕ Spikes n)
abbrev LKey (n : Side) := ℕ ⊕ Faces n

def incoming (X : Listing G n) (R : PathData G) (p : BudgetPoint) : EKey n → RegularAddress n := Sum.elim (enlarges ∘ X.reg)
    (Sum.elim (lowEntry G R p) (highEntry G R))
def soft (X : Listing G n) (R : PathData G) (p : BudgetPoint) : LKey n → Support n :=
    Sum.elim (expand ∘ X.reg) fun i => (lowEntry G R p i).support
def shelves (X : Listing G n) (R : PathData G) (p : BudgetPoint) : Pipes G n where
  reg := incoming X R p ∘ numbering (EKey n)
  kernel := X.hard
  softer := soft X R p ∘ numbering (LKey n)
  sites i := by
    dsimp only [comp_apply]; rcases numbering (LKey n) i with k|k
    · exact ⟨_,(enlarges (X.reg k)).anchor⟩
    exact ⟨_,(lowEntry G R p k).anchor⟩

def archive (X : Listing G n) (R : PathData G) (c : Clip) (v : Source G n) (α Δ : ℝ) : EKey n → Pot G n := Sum.elim (fun i => rebate (X.reg i) (v.logRead i))
    (Sum.elim (fun i => i.2.fresh R c 0 (factor*Δ) ∘ i.1.view) (fun i => i.2.fresh R 0 (factor*α) (factor*Δ) ∘ i.1.view))
def loses (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (v : Source G n) (α Δ : ℝ) : LKey n → Pot G n :=
    Sum.elim (fun i => fault (X.reg i) (v.logRead i) p.threshold) (fun i => i.2.loan R c 0 p (factor*α) (factor*Δ) ∘ i.1.view)

def fill (X : Listing G n) (R : PathData G) (c : Clip) (p : BudgetPoint) (v : Source G n) (α Δ : ℝ) : Tap G n where
  regular := archive X R c v α Δ ∘ numbering _
  forced := v.hardRead
  logarithm := loses X R c p v α Δ ∘ numbering _

variable {X : Listing G n} {v : Source G n}
lemma Local.unweighted (h : Local X p v H w) : (X.read v).EBound p H := by
  obtain ⟨u,hu,h'⟩ := h.cheap
  exact ⟨u,hu,Quotes.segment _ (fun i => (hu i).1) h'⟩
lemma Local.projects (h : Local X p v H w) : Projects (X.read v) p H := ⟨h.smooth,h.unweighted⟩
lemma Local.H_nonneg (h : Local X p v H w) : 0 ≤ H := by obtain ⟨_,_,he⟩ := h.cheap; exact Cost.nonneg (he 0)


private def spins (n : Side) (π : Equiv.Perm ℕ) (s : Signed) (b : Site n) : Equiv.Perm (EKey n) :=
    Equiv.sumCongr π (Equiv.sumCongr ((Seat.move s b).prodCongr (Equiv.refl _)) ((Seat.move s b).prodCongr (Equiv.refl _)))
private def knots (n : Side) (π : Equiv.Perm ℕ) (s : Signed) (b : Site n) : Equiv.Perm (LKey n) :=
    Equiv.sumCongr π ((Seat.move s b).prodCongr (Equiv.refl _))

namespace Local
variable (g : G.Simple) (h : Local X p v H w) (hx : R.Bounds c σ C Λ) (hc : Decent c p) (hn : 20 < n.val) (α Δ : ℝ)
include g h hx hc hn
lemma regFamily : ((shelves X R p).pours (fill X R c p v α Δ)).RegularFamily p := by
  let F := archive X R c v α Δ; let D := incoming X R p
  have hr (i : EKey n) : p.Regular (D i).support (F i) ∧ F i 1 = 0 := by
    rcases i with i|⟨z,d⟩|⟨z,d⟩
    · exact ⟨rebate_regular _ (h.smooth i),rebate_one ..⟩
    · exact ⟨z.regular (d.fresh_regular R c 0 hc _),show d.fresh R c 0 _ (pull _ _ 1) = 0 by rw [pull_one_field,Low.fresh_one]⟩
    exact ⟨z.regular (d.fresh_regular R 0 hx p _ _), show d.fresh R 0 _ _ (pull _ _ 1) = 0 by rw [pull_one_field,High.fresh_one]⟩
  have hh (i : EKey n) (hi : Nonwrapping (D i).support (D i).site) : ∀ a b, IsAffineDirection (D i).site a → IsAffineDirection (D i).site b →
      logHessian (F i) a b = 0 := by
    rcases i with i|⟨z,d⟩|⟨z,d⟩
    · exact rebate_vanish (X.reg i) g (h.smooth i) hi hn
    · apply affine_zero (hr _).1
      intro u; exact (z.hessian g (d.fresh_regular R c 0 hc _) hi (by omega) u u).trans (d.fresh_vanish R c 0 g hc (z.unwrapped hi) hn _ _ _
          ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩) ((LinearJet.isAffine ..).mpr ⟨_,rfl⟩))
    apply affine_zero (hr _).1
    intro u; exact (z.hessian g (d.fresh_regular R 0 hx p _ _) hi (by omega) u u).trans (d.fresh_vanish R 0 g hx p _ _ _ _)
  exact ⟨fun i => (hr _).1,fun i => (hr _).2,fun i => hh _⟩

omit g hx hc hn in
lemma hardFamily : ((shelves X R p).pours (fill X R c p v α Δ)).ForcedFamily p :=
    ⟨h.family.sym,h.family.symtest,h.family.meas,h.family.meas_test,h.family.reads,h.family.reads_test,h.family.permit⟩
omit g hx hn in
lemma loose (i : LKey n) : let F := loses X R c p v α Δ i; let Z := soft X R p i
    GaugeInvariant F ∧ UsesFinal p.threshold Z F ∧ Measurable F ∧ ∀ U, F U ≠ 0 → ¬Healthy p.threshold Z U := by
  rcases i with i|⟨z,d⟩
  · exact ⟨fault_gauge _ _ (h.smooth i),fault_reads _ _ (h.smooth i),fault_meas _ _ (h.smooth i),fun _ => Residual.visits _ _⟩
  exact ⟨Push.Local.invariant_pull (d.loan_gauge R c 0 p _ _) _ _,Push.Local.uses_pull (d.loan_reads R c 0 hc _ _) _ _,
    (d.loan_meas R c 0 p _ _).comp (continuous_pull ..).measurable,fun U he hh => d.visits R c _ p _ _ _ he ((z.healthy ..).1 hh)⟩

omit hx hc in
private lemma action (s : Signed) (b : Site n) (e : (X.read v).Moves s b) :
    (∀ i : EKey n, let z := incoming X R p; let F := archive X R c v α Δ; let j := spins n e.ep s b i
      (z j).site = affine s b (z i).site ∧ (z j).support = (z i).support.image (affine s b) ∧ F j = F i ∘ pull s b) ∧
    (∀ i : LKey n, let z := soft X R p; let F := loses X R c p v α Δ; let j := knots n e.ep s b i
      z j = (z i).image (affine s b) ∧ F j = F i ∘ pull s b) := by
  have ht (i : ℕ) := label_moves (X.reg i) p.threshold (h.smooth i) (by omega : 4 ≤ n.val) (e.reg_support i) (e.reg_site i) g
    (h.smooth (e.ep i)) (funext (e.valuesE i))
  have he (z : Seat n) (f : Pot G n) : f ∘ (Seat.move s b z).view = (f ∘ z.view) ∘ pull s b := by rw [z.view_move]; rfl
  constructor
  · rintro (i|⟨z,d⟩|⟨z,d⟩)
    · exact ⟨e.reg_site i, expand_moves _ _ s b (e.reg_support i) (e.reg_site i),funext fun U => (ht i U).1⟩
    · exact ⟨rfl, z.spread_move ..,he z (d.fresh R c 0 _)⟩
    exact ⟨rfl, z.spread_move ..,he z (d.fresh R 0 _ _)⟩
  rintro (i|⟨z,d⟩)
  · exact ⟨expand_moves _ _ s b (e.reg_support i) (e.reg_site i),funext fun U => (ht i U).2⟩
  exact ⟨z.spread_move ..,he z (d.loan R c 0 p _ _)⟩

lemma fittings : Payments.Fittings (fill X R c p v α Δ) (shelves X R p) p := by
  have he := h.loose (R:=R) hc α Δ
  refine ⟨h.regFamily g hx hc hn α Δ, h.hardFamily α Δ,fun s b => ?_,fun i => (he _).2.2.2,fun i => (he _).1,fun i => (he _).2.1,
    fun i => (he _).2.2.1,fun s b => ?_⟩
  · obtain ⟨e⟩ := h.transforms s b
    let N := numbering (EKey n); let π := spins n e.ep s b; let u := (N.trans π).trans N.symm
    have hN (i) : N (u i) = π (N i) := N.apply_symm_apply _
    have hj (i) := (h.action (R:=R) (c:=c) g hn α Δ s b e).1 (N i)
    let Y := ((shelves X R p).pours (fill X R c p v α Δ))
    change Nonempty (Y.Moves s b)
    refine ⟨⟨u,e.kp,fun i => ?_,fun i => ?_, e.forced_support, e.forced_inventory, e.forced_tests,fun i U => ?_, e.valuesK⟩⟩
    · change (incoming X R p (N (u i))).site = _; exact hN i ▸ (hj i).1
    · change (incoming X R p (N (u i))).support = _; exact hN i ▸ (hj i).2.1
    change archive X R c v α Δ (N (u i)) U = _; exact hN i ▸ congr_fun (hj i).2.2 U
  obtain ⟨e⟩ := h.transforms s b
  let N := numbering (LKey n); let π := knots n e.ep s b; let u := (N.trans π).trans N.symm
  have hN (i) : N (u i) = π (N i) := N.apply_symm_apply _
  have hj (i) := (h.action (R:=R) (c:=c) g hn α Δ s b e).2 (N i)
  exact ⟨u,fun i => by change soft X R p (N (u i)) = _; exact hN i ▸ (hj i).1,fun U i => by
    change loses X R c p v α Δ (N (u i)) U = _; exact hN i ▸ congr_fun (hj i).2 U⟩
end Local
end Collection
end YM.AnalyticBridge.VerifiedReset
