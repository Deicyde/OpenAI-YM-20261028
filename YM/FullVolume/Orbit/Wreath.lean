import YM.FullVolume.Sym.Stage
import YM.FullVolume.Orbit.Rings
/-!
# Wreath: Moves for WHOLE payload family.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Apse
open RG Lattice Wilson Function Ovens Ovens.Pipes
open Progress.DirectedRecipe
open AnalyticBridge VerifiedReset Averaging Residual Collection
open Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {P : BudgetPoint} {X : Pipes G n} {d : Tap G n} {s : Signed} {b: Site n}
structure Emote where
  e:Equiv.Perm ℕ
  k:Equiv.Perm ℕ
  deriving Inhabited

def amid (z:Emote)(u:Activities G n)(s:Signed)(b:Site n):Prop:= ∃ U:u.Moves s b,U.ep=z.e ∧ U.kp=z.k

def duet (z:Emote)(p:Equiv.Perm ℕ)(X:Pipes G n)(d:Tap G n)(s:Signed)(b:Site n):Prop:= amid z (X.pours d) s b ∧
     (∀ i, X.softer (p i) = (X.softer i).image (affine s b)) ∧ ∀ U i, d.logarithm (p i) U=d.logarithm i (pull s b U)
variable {ι : Type*}{W:ι→Tap G n}{z:Emote}{p:Equiv.Perm ℕ}
lemma wreath (F : ℕ≃X.Pellet) (h:∀ i,duet z p X (W i) s b): ∃ u,∀ i,amid u (fused F P (W i)) s b:= by
  cases isEmpty_or_nonempty ι with
  | inl _ => exact ⟨default,isEmptyElim⟩
  | inr i =>
    let i₀:= Classical.choice i; choose t hu hv using fun i=>(h i).1
    let T (i:ι):= Work.H03.After.defines F (t i) p (h i₀|>.2.1) (h i|>.2.2) (P:=P)
    exact ⟨⟨z.e,(T i₀).kp⟩,fun i=> ⟨T i,(Work.H03.After.issued_eq F (t i) p (h i|>.2.1) (h i|>.2.2)).trans (hu i),Work.H03.After.written_eq F (t i) (t i₀) p (h i₀|>.2.1) (h i|>.2.2) (h i₀|>.2.2) ((hv i).trans (hv i₀).symm)⟩⟩
lemma roundish (R : PathData G)(c:Clip)(τ α:ι→ℝ) (h:∀ i,duet z p X (W i) s b):∃ u,∀ i,amid u (finish R c P X (W i) (τ i) (α i)).activities s b:=by
  choose T hu hv using fun i=>(h i).1
  let Y:= destination s b
  let t:= rearrange (softKeys n) (softMap Y) p; let a:= rearrange (regularKeys n) (regMap Y) z.e; let u:= rearrange (hardKeys n) (hardMap Y) z.k
  have hz i:duet ⟨a,u⟩ t (drawer G n) (Rack.widen X (W i)) s b:= ⟨⟨on_shelves (T i), show rearrange ..=(a) from congr_arg _ (hu i),show rearrange ..=u from congr_arg _ (hv i)⟩,carries_log s b p (h i|>.2.1) (h i|>.2.2)⟩ -- .. expected mismatch
  exact wreath (folio G n) hz

-- post Hessian extraction leg. copied perm scripts.
section archive
variable {L:Listing G n}{v:Collection.Source G n}{R:PathData G}{c:Clip}
def spins (n : Side) (π : Equiv.Perm ℕ) (s : Signed) (b : Site n) : Equiv.Perm (EKey n) :=
    Equiv.sumCongr π (Equiv.sumCongr ((Seat.move s b).prodCongr (Equiv.refl _)) ((Seat.move s b).prodCongr (Equiv.refl _)))
def knots (n : Side) (π : Equiv.Perm ℕ) (s : Signed) (b : Site n) : Equiv.Perm (LKey n) :=
    Equiv.sumCongr π ((Seat.move s b).prodCongr (Equiv.refl _))
abbrev twists (s : Signed)(b:Site n) (z:Emote) : Emote:= ⟨Refrain.congo (Extra.Iteration.numbering _) (spins n z.e s b),z.k⟩
abbrev cord (s:Signed)(b:Site n) (z:Emote) := Refrain.congo (Extra.Iteration.numbering _) (knots n z.e s b)
lemma process (s : Signed) (b:Site n) (g:G.Simple) (hn:20<n.val)(h:∀ i,P.Regular (L.reg i).support (v.logRead i)) (hf:amid z (L.read v) s b) (α Δ:ℝ) : duet (twists s b z) (cord s b z) (shelves L R P) (fill L R c P v α Δ) s b:=by
  obtain ⟨e,he,hk⟩:=hf
  have hp (i : ℕ) := label_moves (L.reg i) P.threshold (h i) (by omega : 4 ≤ n.val) (e.reg_support i) (e.reg_site i) g
    (h (e.ep i)) (funext (e.valuesE i))
  have hv (z : Seat n) (f : Pot G n) : f ∘ (Seat.move s b z).view = (f ∘ z.view) ∘ pull s b := by rw [z.view_move]; rfl
  have hT :
    (∀ i : EKey n, let t := incoming L R P; let F := archive L R c v α Δ; let j := spins n e.ep s b i
      (t j).site = affine s b (t i).site ∧ (t j).support = (t i).support.image (affine s b) ∧ F j = F i ∘ pull s b) ∧
    (∀ i : LKey n, let z := soft L R P; let F := loses L R c P v α Δ; let j := knots n e.ep s b i
      z j = (z i).image (affine s b) ∧ F j = F i ∘ pull s b) := by
    constructor
    · rintro (i|⟨z,d⟩|⟨z,d⟩)
      · exact ⟨e.reg_site i, expand_moves _ _ s b (e.reg_support i) (e.reg_site i),funext fun U => (hp i U).1⟩
      · exact ⟨rfl, z.spread_move ..,hv z (d.fresh R c 0 _)⟩
      exact ⟨rfl, z.spread_move ..,hv z (d.fresh R 0 _ _)⟩
    rintro (i|⟨z,d⟩)
    · exact ⟨expand_moves _ _ s b (e.reg_support i) (e.reg_site i),funext fun U => (hp i U).2⟩
    exact ⟨z.spread_move ..,hv z (d.loan R c 0 P _ _)⟩
  let N := Extra.Iteration.numbering (EKey n); let π := spins n e.ep s b; let u := (N.trans π).trans N.symm
  have hN (i) : N (u i) = π (N i) := N.apply_symm_apply _
  have hj (i) := hT.1 (N i)
  let N' := Extra.Iteration.numbering (LKey n); let v':=knots n z.e s b
  let d:= cord s b z; have h' i:N' (d i) = v' (N' i):= N'.apply_symm_apply _
  constructor
  · refine ⟨⟨u,e.kp,fun i => ?_,fun i => ?_, e.forced_support, e.forced_inventory, e.forced_tests,fun i U => ?_, e.valuesK⟩, congr_arg (fun X=> Refrain.congo N (spins n X s b)) he, hk⟩
    · change (incoming L R P (N (u i))).site = _; exact hN i ▸ (hj i).1
    · change (incoming L R P (N (u i))).support = _; exact hN i ▸ (hj i).2.1
    change archive L R c v α Δ (N (u i)) U = _; exact hN i ▸ congr_fun (hj i).2.2 U
  rw [he] at hT
  exact ⟨fun i => by change soft L R P (N' (d i)) = _; rw [h']; exact (hT.2 (N' i)).1,fun U i=> by change loses L R c P v α Δ (N' (d i)) U=_; rw [h']; exact congr_fun ((hT.2 (N' i)).2) U⟩
end archive
end YM.PhysicalNext.Repeat.Apse
