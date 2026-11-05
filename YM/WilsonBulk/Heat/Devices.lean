import YM.WilsonBulk.Web.Holonomy
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# One-line contraction of ordered tensors

`lap` factors are (n+2)(n+1)/2. `bridge` *similarly includes the 1/2*
to drop into Polchinski heat coefficient update with an ordered sum over
pairs. Incoming variables include all LOG coordinates (fine and coarse);
the line G is the full conditional fluctuation covariance on fine only,
extended by zero (adapter later). `pluck` at rank zero only invoked for
finite volume; cover recursion omits it. Estimates consuming nonzero rank
never use summability in total volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Equiv Lattice Bloch Filter Pert.Bulk
variable {X : Type} {n k r : ℕ} {A B C : ℝ} {α : Type}

abbrev bond (n : ℕ) : Fin 2→ Fin (n+2) := hitch 0 (fun _=>Fin.succ (0 : Fin (n+1)))
-- `run_some` already optimizes when `Cases`. Present here baseline symbols exactly.
def dab (n : ℕ) : ℝ := (n+2:ℕ)*(n+1:ℕ)/2
lemma dab_eval (n : ℕ) : dab n = ((n:ℝ)+2) * ((n:ℝ)+1) / (2:ℝ) := by unfold dab; push_cast; rfl
def brush (k n : ℕ) : ℝ := ((k:ℝ)+1)*((n:ℝ)+1)/2
lemma dab_pos (n : ℕ) : 0 < dab n := by rw [dab_eval]; positivity
lemma brush_pos (k n : ℕ) : 0 < brush k n := by unfold brush; positivity

def dabble (G : Page X 2) (u : Page X (n+2)) := pluck (pluck (overlay u G (bond n)))
def lap (G : Page X 2) (u : Page X (n+2)) := polish (dab n • dabble G u)
lemma bond_pay (x y : X) (v : Legs X n) : hitch x (hitch y v) ∘ bond n=two x y := by
  ext1 i; fin_cases i <;> rfl
lemma dabble_read (G : Page X 2) (u : Page X (n+2)) (v : Legs X n) :
    dabble G u v=∑' y,∑' x,u (hitch x (hitch y v))*G (two x y) := by simp only [dabble,pluck,overlay_apply,bond_pay]
lemma Regular.lap (G : Page X 2) (u : Page X (n+2)) : Regular (lap G u) := polish_ready _

-- identity of position substitution for the single connecting edge
def grab (G : Page X 2) (u : Page X (k+1)) := escort (finRotate (k+1)) (pluck (seam u G))
lemma grabbed (v : Legs X k) (y : X) : hitch y v ∘ finRotate (k+1)=Fin.append v (fun (_:Fin 1)=> y) := by
  ext1 i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i
  · rw [Fin.append_left]; exact (congr_arg (hitch y v) (finRotate_of_lt j.isLt)).trans (hitch_succ ..)
  rw [Fin.append_right]; rw [Fin.fin_one_eq_zero j]; exact (congr_arg (hitch y v) finRotate_last).trans (hitch_zero ..)
lemma grab_read (G : Page X 2) (u : Page X (k+1)) (v : Legs X k) (y : X) :
    grab G u (hitch y v) = ∑' x,u (hitch x v)*G (two x y) := by simp only [grab,escort,pluck,grabbed,seam_apply,two]

def bracket (G : Page X 2) (u : Page X (k+1)) (v : Page X (n+1)) := pluck (seam (grab G u) v)
def bridge (G : Page X 2) (u : Page X (k+1)) (v : Page X (n+1)) := polish (brush k n • bracket G u v)
lemma bracket_read (G : Page X 2) (u : Page X (k+1)) (v : Page X (n+1)) (a : Legs X k) (b : Legs X n) :
    bracket G u v (Fin.append a b) = ∑' y,(∑' x,u (hitch x a)*G (two x y))*v (hitch y b) := by
  simp only [bracket,pluck,seam_apply,grab_read]
lemma Regular.bridge (G : Page X 2) (u : Page X (k+1)) (v : Page X (n+1)) : Regular (bridge G u v) := polish_ready _
lemma Regular.rank_cast (h : k=n) (u : Page X k) (hh : Regular u) : Regular (escort (finCongr h) u) := by subst h; exact hh
@[simp] lemma grab_zero (G : Page X 2) : grab G (0:Page X (k+1))=0 := by simp [grab]
@[simp] lemma grab_zero_left (u : Page X (k+1)) : grab 0 u=0 := by simp [grab]
@[simp] lemma lap_zero (G : Page X 2) : lap G (0:Page X (n+2))=0 := by simp [lap,dabble]
@[simp] lemma lap_zero_left (u : Page X (n+2)) : lap 0 u=0 := by simp [lap,dabble]
@[simp] lemma bridge_zero_left (G : Page X 2) (v : Page X (n+1)) : bridge G (0:Page X (k+1)) v=0 := by simp [bridge,bracket]
@[simp] lemma bridge_zero_right (G : Page X 2) (u : Page X (k+1)) : bridge G u (0:Page X (n+1))=0 := by simp [bridge,bracket]
lemma Pervasive.lap {G : Text α 2} {u : Text α (n+2)} (hG : Pervasive G) (h : Pervasive u) : Pervasive (lap G u) := (((h.overlaid hG (bond n)).plucked.plucked).scale (dab n)).polished
lemma Pervasive.grab {G : Text α 2} {u : Text α (k+1)} (hG : Pervasive G) (h : Pervasive u) : Pervasive (grab G u) := ((h.sewn hG).plucked).reindex _
lemma Pervasive.bridge {G : Text α 2} {u : Text α (k+1)} {v : Text α (n+1)} (hG : Pervasive G) (h : Pervasive u) (hv : Pervasive v) : Pervasive (bridge G u v) := ((((hG.grab h).sewn hv).plucked).scale (brush k n)).polished

namespace Proxy
variable {D : ℕ→Side} (hd : Tendsto (fun i=> (D i).val) atTop atTop)
variable {G : Text α 2} {G' : Leaf D α 2} [Fintype α]
include hd
lemma lap {u : Text α (n+2)} {U : Leaf D α (n+2)} (hG : Proxy G' G) (h : Proxy U u) (hn : n ≠ 0) : Proxy (fun i=>lap (G' i) (U i)) (lap G u) :=
    ((((h.overlaid hd hG (by decide) (bond _)).plucked (by omega)).plucked hn).scale _).polished
omit hd
lemma grab {u : Text α (k+1)} {U : Leaf D α (k+1)} (hG : Proxy G' G) (h : Proxy U u) : Proxy (fun i=> grab (G' i) (U i)) (grab G u) :=
    ((h.sewn hG).plucked (by omega)).reindex _
lemma bridge {u : Text α (k+1)} {v : Text α (n+1)} {U : Leaf D α (k+1)} {V : Leaf D α (n+1)}
    (hG : Proxy G' G) (hu : Proxy U u) (hv : Proxy V v) (h : k+n ≠ 0) : Proxy (fun i=> bridge (G' i) (U i) (V i)) (bridge G u v) :=
    (((((hG.grab hu).sewn hv).plucked h).scale _).polished)
end Proxy
end Sheet
end YM.WilsonBulk
