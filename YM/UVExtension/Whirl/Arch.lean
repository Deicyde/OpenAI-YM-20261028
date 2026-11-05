import YM.UVExtension.Guild.Fair
import YM.UVExtension.Whirl.Pitch

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Whirl
open Function Filter Set Lattice Wilson RG Ovens AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Progress.DirectedRecipe Extra.Iteration
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H H' w w' : ℝ}{X:Listing G n}{v v': Collection.Source G n}
private def spins (n : Side) (π : Equiv.Perm ℕ) (s : Signed) (b : Site n) : Equiv.Perm (EKey n) :=
    Equiv.sumCongr π (Equiv.sumCongr ((Seat.move s b).prodCongr (Equiv.refl _)) ((Seat.move s b).prodCongr (Equiv.refl _)))
private def knots (n : Side) (π : Equiv.Perm ℕ) (s : Signed) (b : Site n) : Equiv.Perm (LKey n) :=
    Equiv.sumCongr π ((Seat.move s b).prodCongr (Equiv.refl _))

variable (g:G.Simple) (h: Collection.Local X p v H w)(hn:20<n.val)(α Δ:ℝ)
include g h hn
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

def ember (s:Signed) (b:Site n)(e:(X.read v).Moves s b):
    Takes s b (shelves X R p) (fill X R c p v α Δ) := by
    let X':=shelves X R p; let V:=fill X R c p v α Δ
    let N := numbering (EKey n); let π := spins n e.ep s b; let u := (N.trans π).trans N.symm
    have hN (i) : N (u i) = π (N i) := N.apply_symm_apply _
    have hj (i) := (action (R:=R) (c:=c) g h hn α Δ s b e).1 (N i)
    let Y := ((shelves X R p).pours (fill X R c p v α Δ))
    let K:= numbering (LKey n); let t:=(K.trans (knots n e.ep s b)).trans K.symm
    have ht (i): K (t i)= knots n e.ep s b (K i):= K.apply_symm_apply _
    refine ⟨⟨u,e.kp,fun i => ?_,fun i => ?_, e.forced_support, e.forced_inventory, e.forced_tests,fun i U => ?_, e.valuesK⟩, t,fun i=>?_, fun U i=>?_⟩
    · change (incoming X R p (N (u i))).site = _; exact hN i ▸ (hj i).1
    · change (incoming X R p (N (u i))).support = _; exact hN i ▸ (hj i).2.1
    · change archive X R c v α Δ (N (u i)) U = _; exact hN i ▸ congr_fun (hj i).2.2 U
    · change soft X R p (K (t i))= _; rw [ht]; exact (action g h hn α Δ s b e (R:=R) (c:=c)|>.2 (K i)).1
    change loses X R c p v α Δ (K (t i)) U=_; rw [ht]; exact congr_fun (action g h hn α Δ s b e|>.2 (K i)|>.2) U

lemma moves (h': Collection.Local X p v' H' w') {α' Δ' : ℝ} {s:Signed}{b: Site n}(e:(X.read v).Moves s b)(e':(X.read v').Moves s b) (he: Twins e e'):(ember (R:=R) (c:=c) g h hn α Δ s b e).Joint (ember (c:=c) g h' hn α' Δ' s b e'):=by
  let N:=numbering (EKey n); let K:=numbering (LKey n)
  exact ⟨⟨congr_arg (fun π=> (N.trans (spins n π s b)).trans N.symm) he.1,he.2⟩, congr_arg (fun π=> (K.trans (knots n π s b)).trans K.symm) he.1⟩
end YM.UVExtension.Whirl
