import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineRows
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Clean


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Releasing the exterior analytic estimates at near-geometry stencils

Every gauge used only in its own evaluation. Include the real relative link a
and Q derivatives with true predictor in each oriented cell, at the vacuum cuts
but without assuming stationary hypotheses. Here seperate per-row lemmas (e.g.
to re-use with the caller's displacements in an already-charted integral).
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}
private lemma uniq {A B : Patch} (h : A.L=B.L) (ht : A.J=B.J) : A=B := by cases A; cases B; congr

lemma chart_in {S : StepData c f} (s : Slot) (i : Site f) (x : Site f) (h : x∈ (visits i s.walk).toFinset) :
    separation (S.ratio.parent i) (S.ratio.parent x) ≤ s.length := by
  suffices he : ∀ (w : Walk) i, x∈(visits i w).toFinset → separation (S.ratio.parent i) (S.ratio.parent x) ≤ w.length by
    exact (he _ _ h).trans (by unfold Slot.length; omega)
  intro w
  induction w with
  | nil => intro i h; have hg : x=i := by simpa only [visits,List.mem_toFinset,List.mem_singleton] using h
           simp [hg]
  | cons d w ih =>
    intro i hx;simp only [visits,List.mem_toFinset,List.mem_cons] at hx
    rcases hx with rfl|hx
    · simp
    have hi := ih (i+d.vec) (List.mem_toFinset.mpr hx)
    have he : separation (S.ratio.parent i) (S.ratio.parent (i+d.vec)) ≤ 1 := Work.E03.sep_walk S.ratio.parent (Work.E03.parent_step S) _ [d]
    exact (separation_triangle ..).trans ((Nat.add_le_add he hi).trans (by simp; omega))

lemma slot_based (s : Slot) (x : Site f) : (slotFace s x).1∈(visits x s.walk).toFinset := by
  have h : (slotFace s x).1 = stop x s.walk := by
    unfold slotFace Slot.offset; rw [wrap_stop_cover, map_zero, add_comm]; nth_rw 2 [show x=x+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
  rw [h,List.mem_toFinset]
  generalize s.walk=w
  clear h; induction w generalizing x <;> simp [visits,stop, *]

lemma faceLink {S : StepData c f} (p : Cell f) (j : Fin 4) :
    separation (S.ratio.parent p.1) (S.ratio.parent (patchFace p j).1) ≤ 1 := by
  fin_cases j <;> simp [patchFace,Work.E03.parent_step]

/-- All stencil argument sizes from `Cleans`, for use by the actual affine
Q & p data. Includes also a bound about the replica (!).
-/
lemma released (P : Teller G) (L : Side) (X : ℝ) (hX : 1≤X) :
    ∃ M : ℝ, X≤M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f), S.patch.L=L →
    ∀ (U : Config G f) (V : Config G c) (p : Site c) a, Cleans (S:=S) X x U V p a →
      let g := S.ratio.parent
      let s := weakRadius (G:=G) M L x
      ∃ (z : Site c → G.El) (b : Directions G c) (e : Directions G f),
        (∀ i : Bond c, separation p i.1 ≤ thin x →
          gauge z V i = G.lieExp (b i) ∧ ‖b i‖ ≤ s) ∧
          ∀ i : Bond f, separation p (g i.1) ≤ thin x →
            gauge (z∘g) (replica S.ratio V) i = G.lieExp (e i) ∧ ‖e i‖ ≤ s ∧
              U i=increment (replica S.ratio V) a i ∧ ‖a i‖ ≤ s ∧ linking S V U i≤s := by
  obtain ⟨C,r,hC,hr,H⟩ := log_chart_cost G
  have hx := zero_lt_one.trans_le hX
  let M := C*X+X
  let t x := Scales.b x^5*fiery G x L
  have he : Tendsto (fun x => X*t x) atTop (𝓝 0) := by
    have hu := (tally_g G L 5 1).const_mul X; rw [mul_zero] at hu
    exact hu.congr fun x => by unfold t; rw [fi]; ring
  have hh : X≤M := le_add_of_nonneg_left (by positivity)
  refine ⟨M,hh,?_⟩
  filter_upwards [he.eventually (ge_mem_nhds hr),(year G L).eventually_gt_atTop 0] with x hz hy
  intro c f S hL U V p a Hc g s
  obtain ⟨z,hz1,hz2⟩ := Hc.scene
  rw [hL] at hz1 hz2
  have hT : 0<fiery G x L := Work.E09.temp_pos hy
  have hb : 1≤Scales.b x := Scales.size x
  have hp : 0<t x := by unfold t; positivity
  let D (i : G.El) := G.plog (G.mat i)
  have hd i (h : G.chord i ≤ weakRadius (G:=G) X L x) : i=G.lieExp (D i) ∧ ‖D i‖ ≤ s := by
    rw [show weakRadius (G:=G) X L x=X*t x by unfold weakRadius t; ring] at h
    obtain ⟨H,H'⟩ := H i (h.trans hz)
    refine ⟨H.symm,(H'.trans (mul_le_mul_of_nonneg_left h hC.le)).trans ?_⟩
    unfold s weakRadius M; change C*(X*t x) ≤ (C*X+X)*(b x)^5 * _
    rw [mul_assoc (C*X+X)]; change _≤ M*t x
    nlinarith only [hp,hx]
  let T := replica S.ratio V
  refine ⟨z,D∘gauge z V,D∘gauge (z∘g) T,fun a ha => hd _ (hz1 _ ha),fun a ha => ?_⟩
  have hi : G.chord (gauge (z∘g) T a) ≤ weakRadius (G:=G) X L x := by
    change G.chord (gauge (constantGauge z _) T a) ≤ _
    unfold T; rw [copied _ S.patch.odd_side]; unfold replica; split
    · rw [G.chord_one]; unfold weakRadius; positivity
    exact hz1 (g a.1,a.2) ha
  obtain ⟨h1,h2⟩ := hd _ hi
  obtain ⟨h3,h4,h5⟩ := Hc.chart a ha
  have hm : X*fiery G x S.patch.L ≤ s := by
    unfold s weakRadius; rw [hL]; gcongr
    exact hh.trans (le_mul_of_one_le_right (hx.trans_le hh).le (one_le_pow₀ hb))
  exact ⟨h1,h2,h3,h4.trans hm,h5.trans hm⟩

/-- Lag quote for all three analytic response collections through eligible
stencils on a Cleans cone. `X` prior chord & displacement scaler bought from
cleans_at. Does not force any path witnesses across producers.
-/
structure Response (T : Tube G S) (x C v : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) (a : Directions G f) (p : Site c) : Prop where
  face (q : Cell f) : separation p (S.ratio.parent q.1)+1 ≤ thin x →
    DifferentiableAt ℝ (fun t : ℝ => G.curvature (faceValue (increment (replica S.ratio V) (t • a)) q)) 0 ∧
    ‖firstFace (replica S.ratio V) a q‖ ≤ C*v ∧
    ‖G.curvature (faceValue U q) - firstFace (replica S.ratio V) a q‖ ≤ C*v^2
  noise (q : Bond c) : q.1=p →
    let f := actuate S (replica S.ratio V) q k a; let u := qVar S (replica S.ratio V) q k a
    DifferentiableAt ℝ (fun t => G.curvature (f t*(f 0)⁻¹)) 0 ∧ DifferentiableAt ℝ (G.mat∘f) 0 ∧
    G.colorMat u=(deriv (G.mat∘f) 0)*G.mat ((S.prediction (replica S.ratio V) k q)⁻¹) ∧
    ‖Z S (S.prediction U k) V q - (Z S (S.prediction (replica S.ratio V) k) V q-Real.sqrt S.kernel.penalty • u)‖ ≤ C*v^2 ∧
    ‖Z S (S.prediction (replica S.ratio V) k) V q‖ ≤ C*v ∧ ‖Real.sqrt S.kernel.penalty • u‖ ≤ C*v
  links (q : Bond f) : separation p (S.ratio.parent q.1) ≤ thin x → linking S V U q ≤ v
  sees : ∃ z : Site c→G.El,
    (∀ i : Bond c, separation p i.1 ≤ thin x → G.chord (gauge z V i) ≤ v) ∧
    (∀ i : Bond f, separation p (S.ratio.parent i.1) ≤ thin x →
      G.chord (gauge (z ∘ S.ratio.parent) U i) ≤ v)

lemma reacts (P : Teller G) (L : Side) (X : ℝ) (h : 1≤X) : ∃ C M : ℝ, 0<C ∧ X ≤ M ∧
    (∀ n : ℕ, Tendsto (fun x : ℝ => b x^n * weakRadius (G:=G) M L x) atTop (𝓝 0)) ∧
    ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → P.Funds S T →
      ∀ U V y a, Cleans (S:=S) X x U V y a →
        ∀ k : S.Choices, Response T x C (weakRadius (G:=G) M L x) U V k a y := by
  by_cases hx : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap
  · refine ⟨1,X,one_pos,le_rfl,fun n => ?_,Eventually.of_forall fun x c f S T hl hv => ?_⟩
    · have hu := (tally_g G L (n+5) 1).const_mul X; rw [mul_zero] at hu
      refine hu.congr fun x => ?_; rw [weakRadius,fi]; rw [pow_add]; ring
    exact (hx ⟨S.patch,hl,hv.atStep,hv.kernel⟩).elim
  obtain ⟨D,hL,hD,hB⟩ := hx
  obtain ⟨M,hm,H⟩ := released P L X h
  obtain ⟨C,c,hc,hc0,hC⟩ := bond_local D P.bind G hB
  obtain ⟨Q,q,hq,hq0,hQ⟩ := face_affine G
  have hX := zero_lt_one.trans_le h
  have hM := hX.trans_le hm
  let v := weakRadius (G:=G) M L
  have he n : Tendsto (fun x : ℝ => b x ^ n * v x) atTop (𝓝 0) := by
    have hu := (tally_g G L (n+5) 1).const_mul M; rw [mul_zero] at hu
    refine hu.congr fun x => ?_; unfold v weakRadius; rw [fi]; rw [pow_add]; ring
  have hv : Tendsto v atTop (𝓝 0) := by simpa only [pow_zero,one_mul] using! he 0
  let C0 := max C (2*Q)
  have h1 : C≤C0 := le_max_left ..; have h2 : 2*Q≤C0 := le_max_right ..
  refine ⟨C0,M,hc.trans_le h1,hm,he,?_⟩
  filter_upwards [H,hv.eventually (ge_mem_nhds (lt_min hc0 hq0)),(year G L).eventually_gt_atTop 0,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(predReach D+10))] with x hz hx hy hy'
  intro c f S T hh ht U V y a hA k
  obtain ⟨z,f0,f1,hF0,hF1⟩ := hz _ _ S hh U V y a hA
  have hT := uniq (hh.trans hL.symm) (ht.atStep.trans hD.symm)
  have hp : predReach S.patch ≤ thin x := by unfold thin; rw [hT]; omega
  have hP : 0≤v x := by unfold v weakRadius; have := Scales.size x; have he : 0≤fiery G x L := (Work.E09.temp_pos hy).le; positivity
  let g := S.ratio.parent
  let R := replica S.ratio V
  constructor
  · intro p he0
    have he j : separation y (g (patchFace p j).1) ≤ thin x := (separation_triangle y (g p.1) _).trans
      ((Nat.add_le_add_left (faceLink (S:=S) p j) _).trans he0)
    have hf j := hF1 _ (he j)
    obtain ⟨ha,hb,hc,hd⟩ := hQ _ U R a f1 p (z∘g) (v x) hP (hx.trans (min_le_right ..))
      (fun j => (hf j).2.2.2.1) (fun j => (hf j).2.1) (fun j => (hf j).2.2.1) fun j => (hf j).1
    refine ⟨ha,(norm_add_le ..).trans ((add_le_add hc hd).trans ?_),hb.trans (mul_le_mul_of_nonneg_right
      (show Q≤C0 by linarith only [h2,hq]) (sq_nonneg _))⟩
    exact (show Q*v x+Q*v x=2*Q*v x by ring).trans_le (mul_le_mul_of_nonneg_right h2 hP)
  · intro p ha F u
    have he j (he : separation p.1 (g (j:Bond f).1) ≤ predReach S.patch) := hF1 _ (show separation y (g j.1) ≤ thin x by rw [← ha]; exact he.trans hp)
    have hz' : separation y p.1 ≤ thin x := by rw [ha]; simp
    obtain ⟨hC1,hC2,hC3,hC4,hC5,hC6⟩ := hC _ _ S hT ht.knobs U R V a f1 (f0 p) k p z (v x) hP
      (hx.trans (min_le_left ..)) (fun j h => ⟨(he j h).2.2.2.1,(he j h).2.1⟩) ((hF0 p hz').2)
      (fun j h => (he j h).2.2.1) (fun j h => (he j h).1) ((hF0 p hz').1)
    rw [← ht.knobs] at hC4 hC6
    exact ⟨hC1,hC2,hC3,hC4.trans (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)),hC5.trans (mul_le_mul_of_nonneg_right h1 hP),
      hC6.trans (mul_le_mul_of_nonneg_right h1 hP)⟩
  · intro p hp; exact (hF1 p hp).2.2.2.2
  obtain ⟨z,hz1,hz2⟩ := hA.scene
  have hh' : weakRadius (G:=G) X S.patch.L x ≤ v x := by
    unfold v weakRadius; rw [hh]; have h : 1 ≤ b x:= Scales.size x; have hz := Work.E09.temp_pos hy; unfold fiery; gcongr
  exact ⟨_,fun i hi => (hz1 _ hi).trans hh',fun i hi => (hz2 _ hi).trans hh'⟩
end YM.SectorNext.Remainder.Affine
