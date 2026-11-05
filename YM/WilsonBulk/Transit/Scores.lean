import YM.WilsonBulk.Transit.Homeland
import YM.WilsonBulk.Grid.Paper
import YM.WilsonBulk.Vacuum.HessRates

/-!
# Instantiate with flat-kernel column accuracy, pre-L. Costs advertised on
*all* p,q inputs with this height. Include G.Simple through consuming API when
extracting kinetic/reset. Here no gauge-Ward asserted, price uses zero-end
jets. E-readiness for length inequality tall.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Lattice Laurent Pert.Bulk Bloch RG
open Precision Exterior
open Work.F08
open scoped Topology ENNReal BigOperators Classical
variable {α β : Type} {L : Side} {σ θ μ R M : ℝ}
variable [Fintype α] [Fintype β] {d n : ℕ}
variable {H : Cross L α β} {P : Text α (n+1)}

omit [Fintype α] [Fintype β] in
lemma walk_install (h : Odd L.val) (H : Cross L α β) (l : List Axis) : Sheet.walk (install H) l = install (advanceC L H l.reverse) := by
  induction l generalizing H with
  | nil => rfl
  | cons i l ih=> rw [walk,install_step h, ih, List.reverse_cons,advance_singleton]

def Heights (H : Cross L α β) (d : ℕ) (σ M : ℝ) :=
  0 ≤ M ∧ ∀ l : List Axis,l.length ≤ d→ (advanceC L H l).strip σ (M/(L.val:ℝ)^(1+l.length))
lemma install_walk (h : Heights H d θ M) (hp : Odd L.val) (hs : 0 ≤ σ) (ht : ((n+1:ℕ):ℝ)*σ≤θ) :
    let a : ℝ := (Fintype.card β:ℝ)*Real.exp (4*σ)*M/(L.val:ℝ)
    let b : ℝ := (Fintype.card α:ℝ) * Real.exp (4*((n+1:ℕ)*σ))*M*(L.val:ℝ)^3
    WalkIn L σ (install H) d a ∧ AuditLine (install H) (spotCost L σ) (n+1) a b := by
  intro a b; have hM:= h.1
  have he (l:List Axis) (hl:l.length≤d) := install_audited (h.2 l hl) (by positivity) hs (le_trans (le_mul_of_one_le_left hs (show (1:ℝ)≤(n+1:ℕ) by norm_cast; omega)) ht) ht
  constructor
  · refine ⟨by unfold a; positivity,fun l hl x=>?_⟩
    rw [walk_install hp]; convert (he l.reverse (by simpa using hl)).row x using 1
    congr 1; rw [List.length_reverse,pow_add]; unfold a; ring
  have hT := he [] (by simp); simp only [List.length_nil,pow_one,Nat.add_zero] at hT; unfold a b; convert hT using 1; · rfl
  · ring
  have hL : (L.val:ℝ) ≠ 0:= by positivity
  field_simp
-- vacuum engineering power nominal 4-r with potential logs of canonical dimension 1.
def receipt (α β : Type) [Fintype α] [Fintype β] (σ θ M : ℝ) (d n : ℕ) :=
 (Fintype.card α:ℝ)*Real.exp (4*((n+1:ℕ)*σ))*M * ((Fintype.card α:ℝ)^n*(momentWeight (θ/2) d*((Fintype.card β:ℝ)*Real.exp (4*σ)*M)^n))
lemma receipt_nonneg (h : 0≤θ) (he : 0 ≤ M) : 0 ≤ receipt α β σ θ M d n := by unfold receipt; have hv := momentWeight_nonneg (by positivity : 0≤θ/2) d; positivity
lemma exit_budget (h : TicketNull d P) (hv : Regular P) (he : Within (lawn α) θ R P)
    (hp : 0 < θ) (hs : 0 ≤ σ) (hw : σ/L.val≤θ/2) (hy : Odd L.val) (hH : Heights H d μ M) (ht : ((n+1:ℕ):ℝ)*σ≤μ) :
    Within (lawn β) σ (receipt α β σ θ M d n * (L.val:ℝ)^3/(L.val:ℝ)^(n+d)*R) (travel (install H) P) := by
  obtain ⟨hh,hT⟩:= install_walk hH hy hs ht; apply (travel_budget h hv he hT hh hs hp hw).mono le_rfl (Eq.le ?_)
  unfold receipt; rw [pow_add, div_pow]; ring
lemma pruned_price (hp : 0 < θ) (h : TicketNull d P) (hv : Regular P) (he : Within (lawn α) θ R P)
    (hs : 0 ≤ σ) (hw : σ/L.val≤θ/2) (hy : Odd L.val) (hH : Heights H d μ M) (ht : ((n+1:ℕ):ℝ)*σ≤μ) (hz : 4≤n+d) :
    Within (lawn β) σ (receipt α β σ θ M d n /(L.val:ℝ) * R) (travel (install H) P) := by
  have hL : 1≤(L.val:ℝ):= by exact_mod_cast L.property
  have hh := receipt_nonneg (α:=α) (β:=β) (n:=n) (σ:=σ) (d:=d) hp.le hH.1; refine (exit_budget h hv he hp hs hw hy hH ht).mono le_rfl (mul_le_mul_of_nonneg_right ?_ he.1)
  apply LE.le.trans (b:=receipt α β σ θ M d n*(L.val:ℝ)^3/(L.val:ℝ)^4) ?_ (Eq.le ?_)
  · gcongr
  have hL : (L.val:ℝ)≠0:= by positivity
  field_simp

variable {G : Gauge} {m k : ℕ} {A : Levels G} {P' : Horizon A} {F : MapPrices}
lemma bond_forwardC {F : Cross L (TypeFace m) (TypeFace k)} (s : Axis) : forwardC L (bondColor G F) s = bondColor G (forwardC L F s) := by
  ext ⟨x,i,c⟩ ⟨i',c'⟩
  by_cases h:c=c' <;> simp [forwardC, bondColor,painted,h]
lemma heaviest {F' : Cross L (TypeFace m) (TypeFace k)} (H : Heights (L:=L) (α:=TypeFace m) (β:=TypeFace k) F' d σ M) : Heights (bondColor G F') d σ M := by -- declare F'
  have hh l : advanceC L (bondColor G F') l = bondColor G (advanceC L F' l) := by induction l with
   | nil=> rfl
   | cons i l ih=> simp only [advanceC]; rw [ih,bond_forwardC]
  refine ⟨H.1,fun l h=>?_⟩; rw [hh]; exact painted_strip _ _ _ _ (H.2 l h) (div_nonneg H.1 (by positivity))
lemma permDeep (h : P'.Suffices F) (hp : m<k) (hd : d+2 ≤ stage A (m+1)) : Heights (bondColor G (P'.towers k m).A0) d (F.α (stage A (m+1))) (F.Ω (stage A (m+1))) := by
  refine heaviest ⟨?_,fun l hl=> ?_⟩
  · exact Pert.Bulk.merit (h.rows k (m+1) hp)
  exact ((h.costs k m hp).2.2.2 l (by change l.length ≤ stage A (m+1)-2; omega)).1
end YM.WilsonBulk.Sheet
