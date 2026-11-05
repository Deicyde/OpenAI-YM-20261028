import YM.WilsonBulk.Broadcast.Court

/-!
# Chapters from homogeneous inputs at grade offset (2 or 0). Full narrative
   power 0 can be retained (top Wilson in kinetic gauge) when n+r shifts ≤2.
   Otherwise caller obtains `volumeTape` only up to scalar. Used for noise,
   Haar vertices. Handles complete path choices (including repeated letters).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open Function Filter Equiv Finset Matrix Bloch Lattice Pert.Bulk
open scoped Topology Classical BigOperators ENNReal ContDiff
open PowerSeries (coeff constantCoeff)
open MvPolynomial (C X homogeneousComponent)
variable {α β ι : Type} [Fintype α] [Fintype β]
def chapters (s : ℕ) (T : α→Market β) (F : Tabletop α→ℝ) : Record (Market β) := fun e n=> if n=e+s then stem T (photo F n) else 0
variable (s : ℕ) (T : α→Market β) (F : Tabletop α→ℝ)
omit [Fintype β] in
lemma chapters_here (hs : s≤2) (he : s%2=0) : Document (chapters s T F) := ⟨fun e n h=> if_neg (by omega),fun e n=> by rw [chapters]; split; exacts [polish_ready _,Regular.zero],fun i n h=> if_neg (by omega)⟩
omit [Fintype β] in
lemma chaptersPublic : Pamphlet (chapters s T F) := fun e n=> by
  rw [chapters]; split
  next h => exact ⟨stem_style _ _,⟨1,mound T (photo F n) 1,one_pos,stem_price ..⟩⟩ -- binder clash
  exact Public.zero
omit [Fintype β] in
lemma chapters_money (e n : ℕ) (σ : ℝ) : Within (lawn β) σ (if n=e+s then mound T (photo F n) σ else 0) (chapters s T F e n) := by
  rw [chapters]; split; exacts [stem_price ..,Within.zero le_rfl]
lemma chapters_read (hs : s≤2) (c : Side) (h : ContDiffAt ℝ ω F 0) (e : ℕ) (he : 0<e+s) : coeff e (volumeTape (issue c (chapters s T F))) = coeff (e+s) (ink (plantSector T F c)) := by
  rw [tape_power,capsule,sum_eq_single (e+s)]
  · rw [issue,chapters,if_pos rfl]; exact reads_plant T F h (by omega) -- check assumptions
  · intro i _ hi; simp [issue,chapters,hi]
  intro ha; simp only [allowed,mem_range] at ha; omega
lemma chapters_decal (c : Side) (h : ContDiffAt ℝ ω F 0) : volumeTape (issue c (chapters 2 T F))=zoom (zoom (ink (plantSector T F c))) := by
  ext1 i; rw [zoom_power,zoom_power,chapters_read 2 T F le_rfl c h i (by omega)]
lemma later_decal (c : Side) (h : ContDiffAt ℝ ω F 0) : volumeTape (issue c (later (chapters 2 T F)))=advanceP _ (zoom (zoom (ink (plantSector T F c)))) := by rw [← chapters_decal T F c h,← advance_board]; exact congr_arg _ (issue_board c _ _).symm
lemma chapters_simple (c : Side) (h : ContDiffAt ℝ ω F 0) : volumeTape (issue c (later (chapters 0 T F)))=advanceP _ (ink (plantSector T F c)) := by
  rw [later,← issue_board,← show advanceP (Formula (Co c β)) (volumeTape (issue c (chapters 0 T F)))=_ from (advance_board ..).symm]
  ext1 i; cases i with
  | zero=> simp only [advance_zero]
  | succ i=> rw [advance_hr, advance_hr]; exact chapters_read 0 T F (by omega) c h _ (by omega)
end YM.WilsonBulk.Sheet
