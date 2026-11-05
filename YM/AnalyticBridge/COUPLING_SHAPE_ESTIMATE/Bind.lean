import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Orders
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Surviving



/-!
# The shape-reset activity dictionary

Retained even indices which will evaluate to zero. Pellet enumeration
also fixed by metadata only, not selected using continuity/convergence.
Here the prior `R` ACTUALLY comes before affine subtraction so isn't
required Valid. After the unmarked reset the recipe could need further
padding and `retain`/`next` supplies for the particular path; not
asserting any sufficiency for Op generation beyond what we prove below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Lattice RG Wilson Next.Scheduling WardBin Ovens
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {n : Side} (P : PathData G) (p : Clip) (b : BudgetPoint) (R : Activities G n)

abbrev Scroll (n : Side) := ℕ ⊕ (Card n ⊕ (Post n ⊕ Post n))

def sorting {X : Type*} (f : ℕ→X) (g : Card n → X) (a c : Post n → X) : Scroll n → X := Sum.elim f (Sum.elim g (Sum.elim a c))

def wheel (n : Side) : ℕ≃ Scroll n :=
  letI:=Classical.choice (nonempty_denumerable (Scroll n))
  (Denumerable.eqv (Scroll n)).symm

def corners := sorting (sprouts ∘ R.reg) (cardSite P b) (Post.park P.cubic) (Post.park P.quartic)

def ward : Pipes G n where
  reg := corners P b R ∘ wheel n
  kernel := R.forced
  softer i := (corners P b R (wheel n i)).support
  sites i := ⟨_,(corners P b R (wheel n i)).anchor⟩

def arrange (α ε : ℝ) := sorting (remain R) (residue P p ε)
    (fun i=> -(α+ε) • Post.fee P.cubic i) (fun i => -(α+ε) • Post.fee P.quartic i) (n:=n)

def hooks (α ε : ℝ) := sorting (requireLog R b) (refund P p b α ε) (fun _=>0) (fun _=>0)

def ink (α ε : ℝ) : Tap G n := ⟨arrange P p R α ε ∘ wheel n, R.K, hooks P p b R α ε ∘ wheel n⟩

def slate (α ε : ℝ) := (ward P b R).pours (ink P p b R α ε)

def pelletKey (X : Pipes G n) : ℕ≃Pipes.Pellet X := Classical.choice (Pipes.encoding X)

def written (α ε : ℝ) := Pipes.fused (pelletKey (ward P b R)) b (ink P p b R α ε)





private def permuted (x : Equiv.Perm ℕ) (s : Signed) (z : Site n) : Equiv.Perm (Scroll n) :=
  Equiv.sumCongr x (Equiv.sumCongr (Around.move _ s z) (Equiv.sumCongr (Around.move _ s z) (Around.move _ s z)))

lemma noted_spin {δ : ℝ} (hn : 10<n.val) (hs : G.Simple) (α ε : ℝ) (h : Profiled R (boost b) δ) (s : Signed) (z : Site n) :
    Nonempty ((slate P p b R α ε).Moves s z) ∧ ∃ v : Equiv.Perm ℕ,
      (∀ i, (ward P b R).softer (v i)=((ward P b R).softer i).image (affine s z)) ∧
       ∀ U i,(ink P p b R α ε).logarithm (v i) U=(ink P p b R α ε).logarithm i (pull s z U) := by
  obtain ⟨M⟩:=h.moves s z
  let w:=wheel n; let t:=permuted M.ep s z; let v := (w.trans t).trans w.symm
  let A:= corners P b R; let B:=arrange P p R α ε; let F:=hooks P p b R α ε
  have hh (j) : (A (t j)).site=affine s z (A j).site ∧ (A (t j)).support=(A j).support.image (affine s z) ∧
      ∀ U, B (t j) U=B j (pull s z U) ∧ F (t j) U=F j (pull s z U) := by
    rcases j with i|(j|i|i)
    · obtain ⟨h₁,h₂,h₃⟩:=shiftSeed R (boost b) s z hs hn h M i
      exact ⟨h₁,h₂,h₃⟩
    · refine ⟨(card_smuggle P p b s z j (1:Config G n) α ε).1,(card_smuggle P p b s z j (1:Config G n) α ε).2.1,?_⟩
      exact fun U => (card_smuggle P p b s z j U α ε).2.2
    · obtain ⟨h₁,h₂,h₃⟩:=Post.sanctuary P.cubic s z i
      exact ⟨h₁,h₂,fun U=> ⟨congr_arg (fun y:ℝ => -(α+ε) • y) (h₃ U),rfl⟩⟩
    obtain ⟨h₁,h₂,h₃⟩:=Post.sanctuary P.quartic s z i
    exact ⟨h₁,h₂,fun U=> ⟨congr_arg (fun y:ℝ => -(α+ε) • y) (h₃ U),rfl⟩⟩
  have hx (j) : w (v j)=t (w j) := w.apply_symm_apply _
  have hl (j) : (A (w (v j))).support=(A (w j)).support.image (affine s z) := by rw [hx]; exact (hh _).2.1
  refine ⟨⟨v,M.kp,fun i=>?_,hl,M.forced_support,M.forced_inventory,M.forced_tests, fun i U=>?_,M.valuesK⟩,v,hl,fun U i=>?_⟩
  · change (A (w (v i))).site=_; rw [hx]; exact (hh _).1
  · change B (w (v i)) U=_; rw [hx]; exact ((hh _).2.2 U).1
  change F (w (v i)) U=_; rw [hx]; exact ((hh _).2.2 U).2
end YM.AnalyticBridge.CouplingShape
