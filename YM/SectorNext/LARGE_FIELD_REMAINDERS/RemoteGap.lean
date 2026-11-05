import YM.SectorNext.LARGE_FIELD_REMAINDERS.Coercive


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Chord counting-unit gap anchored to still-present F,I rows

Uses the actual predictor at the same k via E02, and the actual per-block tree.
No period loss even if nearly all links are frozen. Can use larger frozen sets
(subset of these remote links as active) if the caller chooses so.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {G : Gauge} {c f n : Side} (S : StepData c f)

private lemma macro_row (o : Site c) :
    ∑ i : Cell f, (Bid.mcharge S o i:ℝ) ≤ (box (macroR S.patch)).card * (Fintype.card PlaqAxes:ℝ) := by
  let X := box (macroR S.patch)
  let x z := wrap f z + S.ratio.embed o
  have h (i : Cell f) : (Bid.mcharge S o i:ℝ) ≤
      ∑ z∈X, if x z=i.1 then (1:ℝ) else (0:ℝ) := by
    unfold Bid.mcharge; rw [← Finset.sum_filter]; simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    gcongr
    exact fun h => h.1
  calc
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Cell,Fintype.sum_prod_type]
      -- sum over sites outside plaq sum
      simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ) (f:=fun (k : Site f) (_ : PlaqAxes) => _)]
      simp [X]

variable {S}

/-- Remaining canonical fine-coordinate displacement metric (embed and orientation as stored). -/
def linking (S : StepData c f) (V : Config G c) (U : Config G f) (i : Bond f) :=
  G.chord (U i*(replica S.ratio V i)⁻¹)

def linkCost (A : Stores S) (x : ℝ) (V : Config G c) (U : Config G f) :=
  ∑ i ∈ Finset.univ.filter (remote A (radiusB x)), linking S V U i ^2
lemma linkCost_nn (A : Stores S) (x V U) : 0 ≤ linkCost (G:=G) A x V U := by unfold linkCost; positivity

lemma link_compare {A : Stores S} {x : ℝ} {F : Forest S.ratio} {U : Config G f} {V : Config G c}
    {k : S.Choices}
    (h : Alive S U k) (hsize : 2*macroR S.patch<f.val) (hb : S.patch.J+8 ≤ radiusB x)
    (D : ℝ) (hD : 0 ≤ D) (hm : ∀ i : Bond f, remote A (radiusB x) i →
      usable S U (S.ratio.parent i.1) k → Bid.Cops (S:=S) U V (S.prediction U k) i D) :
    let K : ℝ := Fintype.card (Site S.patch.L)
    let E : ℝ := (box (macroR S.patch)).card * (Fintype.card PlaqAxes:ℝ)
    let l : ℝ := 2*(S.patch.J:ℝ)+17
    let R := E*l^4
    linkCost A x V U ≤ (2*(D^2*K*Fintype.card Axis*R + K)) * physical A x U (S.prediction U k) V := by
  intro K E l R
  let X := A.limit x; let Y := A.intern x
  let B := radiusB x
  let g := S.ratio; let Q := S.prediction U k
  let flag (i : Cell f) : ℝ := if i ∈ X then 0 else toll U i
  let tap (i : Bond c) : ℝ := if i ∈ Y then 0 else wire Q V i
  let M o i := (Bid.mcharge S o i:ℝ)
  let H := fun (o : Site c) => ∑ i, M o i * flag i
  let C := fun (i : Bond c) => 2*(D^2*(H i.1)^2+(tap i)^2)
  have hC (i : Bond c) : 0≤C i := by unfold C; positivity
  have hh (z : Bond f) (hz : remote A B z) : linking S V U z ≤ D*H (g.parent z.1)+tap (g.parent z.1,z.2) := by
    let o := g.parent z.1
    have ht : o ∉ A.dome (2*B) := outside_dome hz (by change separation o o + _ ≤ _; simp; omega)
    have hi i (he : 0< Bid.mcharge S o i) : i∉X := by
      intro hh
      have ha : separation o (g.parent i.1) ≤ B := (Work.E01.mcharge_maps S o i he).trans hb
      exact outside_dome hz (show separation o (g.parent i.1)+2*B≤4*B by omega) (Finset.mem_filter.mp hh).2
    have h1 : H o = port S o U := by
      rw [Work.E01.port_charge]; unfold H
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold flag M; split
      next h => rw [show Bid.mcharge S o i=0 from Nat.eq_zero_of_not_pos (fun a => hi i a h)]; simp
      next _ => rfl
    have h2 : tap (o,z.2)=wire Q V (o,z.2) := if_neg (show (o,z.2)∉Y from
      fun hi => ht (Finset.mem_filter.mp hi).2)
    have hc := hm z hz (uses_all h _)
    unfold Bid.Cops at hc
    change linking S V U z ≤ D*port S o U + _ at hc
    change _ ≤ D*H o+tap (o,z.2); rw [h1,h2]; apply hc.trans (add_le_add_right ?_ _)
    split; exact (G.chord_nonneg _); rfl
  have hy (z : Bond f) (hz : remote A B z) : linking S V U z ^2 ≤ C (g.parent z.1,z.2) := by
    apply (pow_le_pow_left₀ (G.chord_nonneg _) (hh z hz) 2).trans
    nlinarith [sq_nonneg (D*H (g.parent z.1) - tap (g.parent z.1,z.2))]
  have hZ : (∑ z∈ Finset.univ.filter (remote A B), linking S V U z ^2) ≤ K*(∑ i, C i) :=
    (Finset.sum_le_sum fun z hz => hy z (Finset.mem_filter.mp hz).2).trans
      ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => hC _)).trans_eq (Work.F01.sum_parent_bond g C))
  apply hZ.trans
  let V1 : ℝ := ∑ i∈Xᶜ,toll U i^2; let V2 : ℝ := ∑ i∈Yᶜ,wire Q V i^2
  have hf : ∑ i, flag i^2 = V1 := by
    rw [← Finset.sum_add_sum_compl X, Finset.sum_eq_zero (s:=X) (f:=fun i => flag i^2) (by intro i hi; simp [flag,hi]),zero_add]; unfold flag V1
    apply Finset.sum_congr rfl; intro i hi; rw [if_neg (Finset.mem_compl.mp hi)]
  have ht : ∑ i, tap i^2 = V2 := by
    rw [← Finset.sum_add_sum_compl Y, Finset.sum_eq_zero (s:=Y) (f:=fun i => tap i^2) (by intro i hi; simp [tap,hi]),zero_add]; unfold tap V2
    apply Finset.sum_congr rfl; intro i hi; rw [if_neg (Finset.mem_compl.mp hi)]
  have he : 0≤E := by unfold E; positivity
  have hx : 0≤R := by unfold R; positivity
  have hk : 0 ≤ K := by unfold K; positivity
  have hh' : ∑ i, (H i)^2 ≤ R*V1 := by
    rw [← hf]; apply schur_cost M flag (fun i j => by unfold M; positivity) he (macro_row S)
    intro i
    have hp := Work.E01.mcharge_count S hsize i
    unfold l M; rw [← Nat.cast_sum]
    exact (Nat.cast_le.mpr hp).trans_eq (by push_cast; ring)
  unfold C; rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum,ht]
  unfold Bond Edge; rw [Fintype.sum_prod_type]
  change K*(2*(D^2*(∑ o : Site c, ∑ _j : Axis, H o^2)+V2)) ≤ _
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have h1 : 0≤V1 := by unfold V1; positivity
  have h2 : 0≤V2 := by unfold V2; positivity
  let a : ℝ := Fintype.card Axis
  have ha : 0≤a := by unfold a; positivity
  change K*(2*(D^2*(a*∑ o, H o^2)+V2)) ≤ 2*(D^2*K*a*R+K)*(V1+V2)
  calc
    _ ≤ K*(2*(D^2*(a*(R*V1))+V2)) := by gcongr
    _ ≤ 2*(D^2*K*a*R+K)*V1 + 2*(D^2*K*a*R+K)*V2 := by
      have hh : 0≤ D^2*K*a*R := by positivity
      nlinarith [mul_nonneg hk h1,mul_nonneg hh h2]
    _ = _ := by ring

lemma link_post (P : Teller G) (L : Side) : ∃ R : ℝ, 0 < R ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L = L → 100*(1+radiusB x)≤c.val →
      P.Funds S T → ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Alive S U k → linkCost A x V U ≤ R * physical A x U (S.prediction U k) V := by
  obtain ⟨D,hD,hm⟩ := Work.E02.answer G L P.j P.bind
  let M := (P.j+7)*L.val
  let E : ℝ := (box M).card * (Fintype.card PlaqAxes:ℝ)
  let K : ℝ := Fintype.card (Site L)
  let r : ℝ := 2*(P.j:ℝ)+17
  let v : ℝ := D^2*K*Fintype.card Axis*(E*r^4)+K
  have hk : 0<K := by unfold K; exact_mod_cast Fintype.card_pos
  refine ⟨2*v,by unfold v E; positivity,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(M+P.j+10))] with x hx
  intro c f S T hL hc hT F A U k V hU h
  have hm' := hm c f S hT.knobs hL hT.atStep
  have he : macroR S.patch = M := by rw [Work.E01.macroR_eq, hT.atStep, hL]
  have hh : 100*macroR S.patch ≤ f.val := by
    have hy : c.val ≤ f.val := by
      rw [S.sizes]
      have h := S.patch.L.property; change 0 < S.patch.L.val at h; simpa using Nat.mul_le_mul_left c.val h
    omega
  have hf : 0 < f.val := f.property
  have hq := link_compare (A:=A) (x:=x) (F:=F) (V:=V) h (by omega) (by rw [hT.atStep]; omega) D hD.le
    (fun i _ hu => hm' hh (by omega) F U hU V i k hu)
  dsimp only at hq; rwa [hL,hT.atStep,he] at hq

lemma draped_link (A : Stores S) (x : ℝ) (F : Forest S.ratio) (a : F.Slice G) (V : Config G c) :
    ∑ i ∈ regular A (radiusB x) F, (G.chord (a i*(replica S.ratio V i.val)⁻¹))^2 ≤ linkCost A x V (F.drape a) := by
  let g (i : Bond f) := if remote A (radiusB x) i then linking S V (F.drape a) i^2 else 0
  have hg := sum_free_le F g (fun i => by unfold g; split; positivity; rfl)
  simpa only [linkCost, linking, Forest.off_tree, g, regular,Finset.sum_filter] using hg

end YM.SectorNext.Remainder
