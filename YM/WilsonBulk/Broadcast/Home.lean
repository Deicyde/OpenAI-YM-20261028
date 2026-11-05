import YM.WilsonBulk.Broadcast.Core

/-!
# Bulk adjacent unreset coefficients (unmarked and rank0 treated mod cash)
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open Work.F08 RG Sheet Pert.Bulk Atelier FreeResolvent Tree Work.F08 Lifted
open PowerSeries (constantCoeff coeff)
variable {c f L : Side} {G : Gauge} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {θ σ p q : ℝ}
variable (J : ChartRatio G) (T : Model P K) (B Q : Bed) (I : Library G)
abbrev cargo := corridor (Cloth G) (fluct G T B)
abbrev pilot := efferos (beams G T B)
abbrev reality (S : StepData c f) (T : Model S.patch S.kernel) := spreadForest T S.sizes

-- all-order BEFORE reset. unmarked interaction log copied heat; compare forceQ leading.
def heating : Printed G P := receive (pair (plain (cargo (G:=G) T B))) (dais J P K I) true
def wreath : Library G := lecture (plain (pilot (G:=G) T B)) (heating J T B I)
def pressureI : Library G := summit G Q - wreath J T B I

abbrev circular (G : Gauge) (c : Side) := Record (Pennant G c)
def flameI (c : Side) : circular G c := lecture (fun x y=> (pilot (G:=G) T B).acts c x y) (receive (pair (fun x y=> (cargo (G:=G) T B).acts c x y)) (Sheet.issue c (dais J P K I)) false)
def torch (c : Side) : circular G c := Sheet.issue c (summit G Q)-flameI J T B I c -- unreset pressure (includes finite scalar)
lemma pressure_style (hd : Document I) : Document (pressureI J T B Q I) := by
  refine (summit_style ..).minus (Document.lectured (Document.receives ?_ _ ?_ true) _); exact podium_style J P K hd; exact podium_free J P K I
lemma pressure_cash : Cashless (pressureI J T B Q I) := (summit_hairless G Q).minus (Cashless.lectured (fun _=> noCash ..) _)
lemma press_free (h : Document I) : Sheet.Free (wreath J T B I) := (((siteLimits _ true (podium_style (I:=I) J P K h).cap (podium_free J P K I) (podium_style J P K h).coherent).2.2).lectured _)
lemma press_lead (h : Document I) (i : ℕ) : pressureI J T B Q I 0 i=summit G Q 0 i:= by simp only [pressureI,Pi.sub_apply,press_free J T B I h i,sub_zero]
lemma flame_free (c : Side) (h : Document I) (p : Pamphlet I) : Sheet.Free (flameI J T B I c) := by
  have he := (podium_hears J P K p).at_issue c (podium_style J P K h); exact ((siteLimits _ false he.cap (issue_free _ _ (podium_free J P K I)) he.coherent).2.2).lectured _
lemma flame_style (c : Side) (h : Document I) (p : Pamphlet I) : Document (flameI J T B I c) := let he:=(podium_hears J P K p).at_issue c (podium_style J P K h); (he.receives _ (issue_free c _ (podium_free J P K I)) false).lectured _
lemma survives {D : ℕ→Side} (hd : Tendsto (fun i:ℕ=>(D i).val) atTop atTop) (hp : Pamphlet I) (he : 0<σ) -- add implicit
    (h : (fluct G T B).strip σ p) (hm : (beams G T B).strip σ q) (hk : 0 ≤ p) : dean D (fun i=> flameI J T B I (D i)) (wreath J T B I) := by
  apply dean.lecture (F:=pilot (G:=G) T B) he (effer_cost _ hm) (zero_le_one.trans (le_max_right ..)) D _
  exact dean.reached (cargo (G:=G) T B) _ D hd _ (fun i n _=> (podium_hears J P K hp i n).forever D) he (corridor_height h hk) hk
lemma arrival {fprice : ℝ} {D : ℕ→ Side} (hd : Tendsto (fun i:ℕ=>(D i).val) atTop atTop) (hp : Pamphlet I) (he : 0<σ) (hg : (actionKernel Q.metric).strip θ fprice) (hθ : 0<θ) -- add fprice
    (h : (fluct G T B).strip σ p) (hm : (beams G T B).strip σ q) (hk : 0≤p) : dean D (fun i=> torch J T B Q I (D i)) (pressureI J T B Q I) := fun i j hn=> ((summit_public G hg hθ i j).forever D).minus (survives J T B I hd hp he h hm hk i j hn)
lemma press_public (p' : Pamphlet I) (h : Pamphlet (summit G Q)) -- wrong type
    (he : 0 < σ) (hp : (fluct G T B).strip σ p) (hq : (beams G T B).strip σ q) (hk : 0 ≤ p) : Pamphlet (pressureI J T B Q I) := by
  apply h.minus; intro i j; cases j; swap
  · let T₀ (i : ℕ) : Side:= ⟨i+1,Nat.zero_lt_succ _⟩; exact (survives J T B I (D:=T₀) (tendsto_atTop_mono (fun i=>(show i≤(i+1) by omega)) tendsto_id) p' he hp hq hk i _ (by omega)).claim _
  change Public (lecture _ (heating J T B I) i 0); rw [Cashless.lectured]; exact Public.zero; intro i; exact noCash ..
-- prove plateau for ANY F with tree field fixed (reindex crucial for changing to use symmetry)
lemma flame_energizes {S : StepData c f} (T : Model S.patch S.kernel) (hs : 0≤σ) (h : Serves G T B σ p) (p : Pamphlet I) (hc : Document I) (he : Steps 1 (audienceK G f I) (grains (matrixK G f B))) (hl : Bid.Larger (G:=G) S)
    (hJ : LocalRatio J) {ι : Type} (t : S.Choices) (F : Coursing ι S) (hf : F.tree= reality S T) : plateau J B t F (audienceK G f I) (volumeTape (flameI J T B I c)) := by
  let U:=dais J S.patch S.kernel I
  have ht := podium_ambience t I B hl.1 p hJ he
  let t' := reality S T
  have hv : Atelier.predictor G F.tree B=installed S.ratio (beams G T B) := by rw [hf]; exact hanging T B hs h S.sizes hl
  have h₁ : Document (Sheet.issue c U):= (podium_hears J S.patch S.kernel p).at_issue c (podium_style J S.patch S.kernel hc)
  have hV : Seen c (splitCo S.ratio _) (splitCo S.ratio _) (fluct G T B) (regionJ G F.tree B) := by rw [hf]; exact h.covers S.sizes hl
  unfold plateau glimmer; erw [hv]; exact podium S.ratio _ _ _ _ (beams G T B) _ h₁ (issue_free c U (podium_free J _ _ I)) hV (haar_empty hJ) (auditorium_start t hl.1 he) ht
end YM.WilsonBulk.Parapet
