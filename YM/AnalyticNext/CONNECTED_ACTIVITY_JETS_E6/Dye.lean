import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rotation

/-!
# Rinsed plate vs flat (structural flags far)

Remote diag patch Gauged V (one local common gauge on the whole plate patch!)
Does not change the windows or F or sell a global determinant lemma.
Used only under manifest (output flags correct globally). Off-support use
would need supplying clean for all numerical sites within the halo.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {η r Q Y : ℝ} {L : Side} (X : Coat T F)

/-- Only serves flat plate reference for local estimates. Tree unchanged. -/
def blank : Coat T F := { X with V:=1,seeds := ⟨∅,∅,∅⟩ }
lemma bowed (h : 0 ≤ Pressure.temp X.x) : X.blank.manifest := by
  ext v; simp only [blank,notMem_empty,false_iff]
  intro H; obtain ⟨p,-,hk⟩ := (flags_spec ..).mp H
  unfold faceValue at hk; rw [SliceRows.trivial,G.chord_one] at hk; exact hk.not_ge h
lemma blank_no (o : Site c) (d : ℕ) : ¬ Inside o X.blank.seeds d := by simp [Inside,blank, dome, place, halo_spec]
lemma no_flat (i : Bond f) : X.blank.Hot i ↔ i ∉ F.trunks := by
  refine ⟨And.left,fun hf => ?_⟩; exact far_active X.blank.seeds F i (X.blank_no _ _) hf
lemma blank_all (s : Signed) (p : Spot c f) : X.blank.selected s p := X.blank_no _ _

private lemma onSing (Y : Coat T F) (i : Tubular f G) (he : Y.Hot i.1) : Y.lens (sing i) = sing i := by
  funext j; by_cases hi : j=i.1
  · rw [hi]; simp [lens,he]
  simp [lens, sing,hi]

def swell (G : Gauge) (C h : ℝ) (B : ℕ) := scale*(C*(2*G.colorScale*((B:ℝ)+1)*h*1))

/-- Compare all rows through *one* entry patch. -/
lemma dye_for (h : Room P S T X.x) (i : Bond f) (o : Site c) (x : G.ColorIndex) (p : Target c f G)
    {z : Site c→G.El} {M : ℝ}
    (hf : ¬Inside o X.seeds (30*X.B)) (ht : separation o (atEdge S i) ≤ X.B+2)
    {C : ℝ} (hC : 0 < C) (hy : Bounded T P.top.width C) (he : 0≤M)
    (hm : ∀ i : Bond c, separation o i.1 ≤ 6*X.B → G.chord (gauge z X.V i) ≤ M) :
    |(X.rinse z).form p (i,x)-X.blank.form p (i,x)| ≤ swell G C M X.B := by
  let Y := X.rinse z; let W := X.blank; let q : Tubular f G := (i,x)
  have hu := X.blank_no (aim S p) (6*X.B)
  have hZ : 0≤ swell G C M X.B := by have := G.colorScale_pos; have := scale_pos; unfold swell; positivity
  have hR : Room P S T Y.x := h
  have hg : Room P S T W.x := h
  change |Y.form p q-W.form p q| ≤ _
  obtain ⟨u,v,hA,-⟩ := h.accepted.feeds
  by_cases hp : i∈F.trunks
  · rw [Y.cold q (fun ht => ht.1 hp) hA, W.cold q (fun ht=> ht.1 hp) hA,sub_zero,abs_zero]; exact hZ
  have hB : 100 ≤ X.B := h.sight.1
  have hv : W.Hot i := (X.no_flat i).2 hp
  have hk : Y.Hot i := far_active X.seeds F i (B:=X.B) (clear hf (by omega)) hp
  by_cases he' : X.B/4 < separation (aim S p) (atEdge S i)
  · rw [Y.plume hR p q he', W.plume hg p q he', sub_zero,abs_zero]; exact hZ
  have hh : separation o (aim S p) ≤ 3*X.B := by
    refine (separation_triangle o (atEdge S i) _).trans ?_; rw [separation_comm (atEdge S i)]; omega
  have hhp : aim S p= Y.addr p.1.1 (spot S p.1.2) := by unfold addr aim root; rw [cost_is_here]
  have hx : Y.selected p.1.1 (spot S p.1.2) := by
    unfold selected; rw [← hhp]; apply clear hf; change 6*X.B+separation o _ ≤ _; omega
  let a := orientedRow T X.R p.1.1 p.1.2 Y.V (sing q)
  let b' := orientedRow T X.R p.1.1 p.1.2 (1:Config G c) (sing q)
  have hV : Y.form p q=scale*a p.2 := by
    simp only [form,of_apply,stand,Coat.motion,if_pos hx,onSing Y q hk]; rfl
  have hW : W.form p q=scale*b' p.2 := by
    have ht : W.selected p.1.1 (spot S p.1.2) := X.blank_all _ _
    simp only [form,of_apply,stand,Coat.motion,if_pos ht,onSing W q hv]; rfl
  have ha : ‖a-b'‖ ≤ C*(2*G.colorScale*((X.B:ℝ)+1)*M*1) := spinning h.accepted hC hy Y.V X.R X.B p.1.1 p.1.2
    zero_le_one (sing q) (fun i _ => by
      by_cases he : i=q.1
      · rw [he]; simp [sing,dot]
      simp [sing,he]) (by have he := h.sight.2; unfold Coat.B Coat.R; omega)
    he (fun i hi => hm i ((separation_triangle _ _ _).trans (show separation o (aim S p)+separation (aim S p) i.1 ≤ _ by
      change separation (aim S p) i.1 ≤ _ at hi; omega)))
  rw [hV,hW,← mul_sub,abs_mul,abs_of_pos scale_pos]
  exact mul_le_mul_of_nonneg_left ((stand_cap p.2 (a-b')).trans ha) scale_pos.le

def repair (G : Gauge) (C h Y : ℝ) (B : ℕ) := 2*(swell G C h B*Y)

lemma dye (h : Room P S T X.x) (o : Site c) {z : Site c→G.El} {M : ℝ} (θ : Rotator P L η r Q Y (X.rinse z))
    (hω : Rotator P L η r Q Y X.blank) (hf : ¬Inside o X.seeds (30*X.B)) (i j : Tubular f G)
    (ht : separation o (along S i) ≤ X.B+2) (hh : separation o (along S j) ≤ X.B+2)
    {C : ℝ} (hC : 0 < C) (hy : Bounded T P.top.width C) (he : 0≤M)
    (hm : ∀ i : Bond c, separation o i.1 ≤ 6*X.B → G.chord (gauge z X.V i) ≤ M) :
    |(X.rinse z).plate i j-X.blank.plate i j| ≤ repair G C M Y X.B := by
  let A := X.rinse z; let F' := X.blank
  have hB : 100 ≤ X.B := h.sight.1
  have hF : A.sleepy i j=F'.sleepy i j := by
    by_cases hk : i = j
    · subst j; have hp : A.Hot i.1 ↔ F'.Hot i.1 := by
        rw [show F'.Hot i.1 ↔ _ from X.no_flat i.1]
        exact ⟨And.left,fun hr => far_active X.seeds F i.1 (clear hf (u:=10*X.B+1) (by unfold along at ht; omega)) hr⟩
      simp [sleepy,hp]
    simp [sleepy,hk]
  let E := swell G C M X.B
  have h' : 0≤E := by unfold E swell; have := G.colorScale_pos; have:=scale_pos; positivity
  have he' k : |A.form k i*A.form k j-F'.form k i*F'.form k j| ≤ E*|A.form k j| + E*|F'.form k i| := by
    let a := A.form k i; let b := A.form k j; let c := F'.form k i; let d := F'.form k j
    have ha : |a-c| ≤ E := X.dye_for h i.1 o i.2 k hf ht hC hy he hm
    have hb : |b-d| ≤ E := X.dye_for h j.1 o j.2 k hf hh hC hy he hm
    change |a*b-c*d| ≤ _
    rw [show a*b-c*d=(a-c)*b+(b-d)*c by ring]
    apply (abs_add_le ..).trans; rw [abs_mul,abs_mul]; exact add_le_add
      (mul_le_mul_of_nonneg_right ha (abs_nonneg _)) (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
  change |A.plate i j-F'.plate i j| ≤ _
  simp only [plate, Matrix.add_apply, hF,add_sub_add_right_eq_sub, Matrix.mul_apply, transpose_apply,← sum_sub_distrib]
  apply ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun p _ => he' p)).trans
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]; unfold repair; rw [two_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (pure_pay θ.matrix.2 θ.full.hot.le j) h')
    (mul_le_mul_of_nonneg_left (pure_pay hω.matrix.2 hω.full.hot.le i) h')
end YM.ConnectedActivityE6.Coat
