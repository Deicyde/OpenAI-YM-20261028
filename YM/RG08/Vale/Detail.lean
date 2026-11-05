import YM.RG08.Vale.Styles
/-!
# Projection realizes the stated proper section weights
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {p m c:Side}{R:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}
variable {F:Labels.Frame G d}(T:SectionData F)(b:Letter F) {V : BoardU D R G}
variable (H:Hol G)(h:T.Sound H)(hP: Bid.pop T)(hz:d≤D)(hR:0≤R)
include h
lemma dappled_crown (k:ℕ): Dappled (crownP T b k):=by
  refine ⟨crown_tidy ..,fun m=> shy_useful (crown_tidy ..) ?_ (crown_pays T b _)⟩
  refine ⟨Complex.continuous_re.measurable.comp (T.continuous_places (Place.copy F b.label) (0:Site m)).measurable,(smooth_sl ..).contDiffAt,fun _ _ _ _ _ _ hp=>?_⟩
  filter_upwards [hp] with i he; dsimp only [Function.comp_apply]; rw [he]; exact congr_arg Complex.re (T.placed_invariant h ..)
-- ordinary Taylor chain first, then engineering power in log substitute. include rank-zero.
omit h in
private lemma ordinary_taylor {E W:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup W][NormedSpace ℝ W](U:E→W) (h:ContDiffAt ℝ ω U 0)(n:ℕ)(hv:k≤n):
    Tensor.coeff U k 0=Tensor.coeff (∑ i∈range (n+1), Tensor.diagonal (Tensor.coeff U i 0)) k 0 := by
  classical
  rw [Tensor.coeff_sum,Finset.sum_eq_single k,coeff_at_diagonal]; rotate_left
  · intro i hi hx; exact coeff_diagonal_else _ (Tensor.coeff_symm (h.of_le le_top)) hx.symm
  · intro hp; simp [hv] at hp
  · exact fun _ _=> (Tensor.diag_smooth ..).contDiffAt
  exact Tensor.coeff_symm (h.of_le le_top)
lemma stoop (v : Fin j→ Snap G d):
    (∑ i∈range (j+1), amount (crownP T b i) d j v)=iteratedFDeriv ℝ j (pillar T b ∘ Film.localLane) 0 v := by
  let f:=pillar T b; let M i:= Tensor.diagonal (Tensor.coeff f i 0)
  let g: Snap G d→ Place.Dev T.stencil G:= Film.localLane
  let x:= ∑ i∈range (j+1), M i; have hp:g 0=0:= Film.local_zero _
  have hg := Film.local_smooth T.stencil (G:=G) (d:=d); have hm i : ContDiffAt ℝ ω (M i) (g 0):= (Tensor.diag_smooth ..).contDiffAt
  have he : ContDiffAt ℝ ω f (g 0):= (Complex.reCLM.contDiff.comp (Place.column_smooth ..)).contDiffAt
  have hx : ContDiffAt ℝ ω x (g 0) := by unfold x; rw [show (∑ i∈range (j+1),M i)=(fun x=>∑ i∈range (j+1),M i x) from funext fun k=> Finset.sum_apply k _ M]; exact ContDiffAt.sum (fun i _=>hm i)
  calc
    _ = ∑ i∈range (j+1), iteratedFDeriv ℝ j (M i∘g) 0 v := sum_congr rfl fun i _=> DFunLike.congr_fun (stock_leads ..) v
    _ = iteratedFDeriv ℝ j (x∘g) 0 v := by rw [show x∘g= ∑ i∈range (j+1), M i∘g from funext fun k=> by simp [x,Finset.sum_apply], iteratedFDeriv_sum_apply (fun i _=> ((hm i).comp (f:=g) (0:Snap G d) hg).of_le le_top), _root_.sum_apply]
    _ = _ := by
      change iteratedFDeriv ℝ j (x∘g) 0 v= iteratedFDeriv ℝ j (f∘g) 0 v
      rw [Cases.compReads hx hg le_top, Cases.compReads he hg le_top]; refine sum_congr rfl fun i _=> ?_
      unfold Cases.caseRead; rw [hp]; apply DFunLike.congr_fun; apply smul_right_injective _ (show ((i.length.factorial:ℝ)⁻¹)≠0 by positivity)
      exact (ordinary_taylor f (hp ▸ he) j i.length_le).symm
set_option maxHeartbeats 400000 in
lemma costuming (c:F.Index): (∑ i∈range ((F.grades c).2+1), F.coords (ladle H (crownP T b i) d (F.grades c).2) c)= if b.label=c then 1 else 0 := by
  let w:=F.grades c; let j:=w.2; let P(i:ℕ):=cook (dappled_crown T b H h i) (stock_lank T.stencil (Tensor.coeff (pillar T b) i 0)) H d j
  let M:=∑ i∈range (j+1),P i
  have hp v: M.val v=iteratedFDeriv ℝ j (pillar T b ∘ Film.localLane) 0 v := by
    unfold M; rw [AddSubmonoidClass.coe_finsetSum,_root_.sum_apply]; exact stoop T b H h v
  let f:= pillar T b ∘ Film.localLane (S:=T.stencil) (d:=d); let g : Snap G d→ℂ:= Place.column T b.label ∘ Film.localLane
  have hh : g = Complex.ofRealCLM ∘ f := funext fun i=> (pillar_real T b H h _).symm
  have hx : Tensor.coeff g j 0=shadeC M := by rw [hh,Tensor.coeff,Complex.ofRealCLM.iteratedFDeriv_comp_left]; exact congr_arg (fun x=> ((j.factorial:ℝ)⁻¹) • Complex.ofRealCLM.compContinuousMultilinearMap x) (ContinuousMultilinearMap.ext hp).symm; exact ((Complex.reCLM.contDiff.comp (column_smooth ..)).contDiffAt.comp _ (Film.local_smooth ..)); exact le_top -- maybe
  have ht : Parts.Safe g := Film.still T h (Place.copy F b.label)
  have hs : gradePart (F.grades c) (basin M)=gradePart (F.grades c) (Parts.archive ht):= by
    apply Subtype.ext; exact ((basin_tile (k:=(F.grades c).2) (i:=(F.grades c).1) M (F.bound c) (Film.second_fits F c)).trans (dif_pos rfl)).trans ((Parts.capture ht (k:= (F.grades c).1) (F.bound c) (Film.second_fits F c)).trans (congr_arg (fun x=>WardBin.tile x (F.grades c).1) hx)|>.symm)
  have hc : F.coords (basin M) c= if b.label=c then 1 else 0 := by rw [Film.costs_only,hs,← Film.costs_only, show Parts.archive ht=_ from Film.corner T h (Place.copy F b.label),LinearEquiv.apply_symm_apply]; simp [Place.copy,Pi.single_apply,eq_comm]
  unfold M at hc; rw [basin_sums,map_sum,Finset.sum_apply] at hc
  exact (Finset.sum_congr rfl (fun i _=> by rw [ladle,dif_pos ⟨dappled_crown T b H h _,stock_lank _ _⟩] )).trans hc
include hz hR hP
set_option maxHeartbeats 300000 in
lemma outfit (p : Letter F)(e:ℕ): auditT H F (startU T b hz hR) e p=if e=0 ∧ p=b then 1 else 0 := by
  let V:= startU T b hz hR
  let f:= F.coords
  by_cases ht: e+slot b<slot p
  · rw [if_neg ?_, audit_cap H (start_cap T b hz hR) _ ht] -- fix
    intro hh; rw [hh.2,hh.1] at ht; omega
  let i := e+slot b-slot p
  have hs : slot b ≤ i+slot p := by unfold i; omega
  have he : i+slot p-slot b=e := by unfold i; omega
  have hm:= audit_tile (i:=i) H (start_duty T b hz hR hP H h) (start_lank T b hz hR) p
  rw [if_pos hs, he] at hm
  have hh: (p=b ↔ p.label=b.label∧p.test=b.test) := by cases b; cases p; simp
  by_cases hO:i=0; swap
  · simp_rw [lights_out T b hz hR hP,if_neg hO,ladle_zero] at hm
    rw [if_neg ?_]; simpa using hm.symm
    rintro ⟨rfl,hE⟩; unfold i at hO; rw [hE] at hO; omega
  have hb:= show chant b hz hR (coinsT D p.test) = if b.test=p.test then 1 else 0 from pointed ..
  simp_rw [lights_out T b hz hR hP, if_pos hO,hb] at hm
  by_cases hf:b.test=p.test; swap
  · simp_rw [if_neg hf,zero_smul,ladle_zero] at hm; rw [if_neg (fun hg=> hf (by rw [hg.2]))]; simpa using hm.symm
  simp_rw [if_pos hf,one_smul] at hm; rw [map_sum,Finset.sum_apply] at hm
  rw [show slot p=(F.grades p.label).2 from rfl,costuming T b H h] at hm
  by_cases hx : p=b
  · have hj : e=0:= by unfold i at hO; rw [hx] at hO; omega
    rw [if_pos ⟨hj,hx⟩]; exact Complex.ofReal_injective ((by rw [if_pos (hx ▸ rfl)] at hm; simpa using hm.symm) : ((auditT _ _ _ _ _ : ℝ):ℂ)=Complex.ofReal 1)
  rw [if_neg fun h=> hx h.2]; rw [if_neg (fun h=> hx (hh.2 ⟨h.symm,hf.symm⟩))] at hm
  simpa using hm.symm
end YM.RG08.Vale
