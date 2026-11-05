import YM.Euclid.Window
import YM.Push.SECTOR_MEASURE.Bounds
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Exterior
import YM.SectorNext.LARGE_FIELD_REMAINDERS.PairCharts


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Uniform pair gap, still using seeded prerequisites

Variant not needing stationary centers. On a *given* remote link compare any two
candidate fine-array inputs even with different Choices (but same sector seeds and
V), by axis gauges about that link. Patchwise lift of logs doesn't assume absence of
holonomy about torus. Drows give literal v/w costs. This will permit preservation of
the Gaussian link scale at the actual remainder without a V-factor loan.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Center
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

def shiftedFine (T : Tube G S) (R : ℕ) (s : ℝ) (V : Config G c) (U : Config G f) (i : Cell f) :=
  shoot T.high U i - T.Mv R s V (i,false)

def shiftedBond (T : Tube G S) (R : ℕ) (s : ℝ) (V Q : Config G c) (i : Bond c) :=
  Z S Q V i-T.Mw R s V i

/-- Raw face/bond rows only at positions where we still have the squares. -/
def faceBill (T : Tube G S) (A : Stores S) (x : ℝ) (V : Config G c) (U : Config G f) (i : Cell f) : ℝ :=
  if i∈A.limit x then 0 else ‖shiftedFine T (till x) (temp x) V U i‖

def bondBill (T : Tube G S) (A : Stores S) (x : ℝ) (V Q : Config G c) (i : Bond c) : ℝ :=
  if i∈A.intern x then 0 else ‖shiftedBond T (till x) (temp x) V Q i‖

lemma faceBill_nn (T : Tube G S) (A x V U i) : 0 ≤ faceBill T A x V U i := by unfold faceBill; split; rfl; exact norm_nonneg _
lemma bondBill_nn (T : Tube G S) (A x V U i) : 0 ≤ bondBill T A x V U i := by unfold bondBill; split; rfl; exact norm_nonneg _

variable (S)
def patchAt (z : Cover) (i : Site c) := wrap f z + S.ratio.embed i

private lemma reaches (z : Cover) (i : Site c) (hz : z∈box (macroR S.patch)) :
    separation i (S.ratio.parent (patchAt S z i)) ≤ macroR S.patch + S.patch.L.val := by
  let g := S.ratio
  have hy := Work.E08.separation_box_add (g.embed i) hz
  have hu := Corona.foreshorten g (g.embed i) (patchAt S z i)
  rw [g.embed_parent] at hu
  change S.patch.L.val*separation i (g.parent (patchAt S z i)) ≤ separation (g.embed i) _ + S.patch.L.val at hu
  exact le_trans (le_mul_of_one_le_left (by positivity) S.patch.L.property) (hu.trans (Nat.add_le_add_right hy _))

variable {S}
private lemma uniq {A B : Patch} (h : A.L=B.L) (ht : A.J=B.J) : A=B := by cases A; cases B; congr

def isolated (A : Stores S) (B : ℕ) (e : Bond f) := remote A (2*B) e -- 8B

set_option maxHeartbeats 650000 in
/-- The estimate at *any* link designated active (outside 8B version).
One set of constants across period, V, k and legal F (hypotheses supplying U,W
on that tree). Error in counting link units itself; after squaring even cheaper.
The fixed constants here can depend on L. -/
lemma two_links (P : Teller G) (L : Side) (W : ℝ) (hw : 0 < W) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (U U' : Config G f) (k k' : S.Choices) (V : Config G c),
        SliceSet S F U → SliceSet S F U' → Seeded A U k V x W → Seeded A U' k' V x W → Alive S U k → Alive S U' k' →
        ∀ e : Bond f, isolated A (radiusB x) e →
          let R := macroR S.patch; let o := S.ratio.parent e.1
          let b := Scales.b x; let s := fiery G x L
          let q i := faceBill T A x V U i+faceBill T A x V U' i
          let p := (o,e.2)
          G.chord (U e*(U' e)⁻¹) ≤ C*
            ((∑ z∈box R, ∑ j : PlaqAxes, q (patchAt S z o,j)) + (bondBill T A x V (S.prediction U k) p+bondBill T A x V (S.prediction U' k') p) + (b^5*s)^2) := by
  by_cases hy : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap
  · refine ⟨1,one_pos,Eventually.of_forall fun b c f S T hL hv hT => ?_⟩
    exact (hy ⟨S.patch,hL,hT.atStep,hT.kernel⟩).elim
  obtain ⟨D,hL,hK,hD⟩ := hy
  obtain ⟨E,hE,he⟩ := outside_size P L W hw
  obtain ⟨A,rA,hA,hrA,HA⟩ := tree_chart_cost G
  obtain ⟨B,rB,hB,hrB,HB⟩ := extend_interior G
  obtain ⟨M,rM,hM,hrM,HM⟩ := face_chart_cost G
  obtain ⟨N,rN,hN,hrN,HN⟩ := z_chart_cost D P.bind G hD
  obtain ⟨C,rC,hC,hrC,HC⟩ := distance_cost G
  obtain ⟨Y,hY,HY⟩ := Work.E02.answer G L P.j P.bind
  let X := macroR D
  let q : ℝ := (box X).card * (Fintype.card PlaqAxes:ℝ)
  let α := Real.sqrt P.top.clip.direct; let u := Real.sqrt P.bind.penalty
  have hα : 0 < α := Real.sqrt_pos.2 P.top.clip.quadratic_pos
  have hu : 0 < u := Real.sqrt_pos.2 P.bind.penalty_pos
  let m := 3*E*(A+B)
  have hm : 0<m := by unfold m; have hh : 0<E := zero_lt_one.trans_le hE; positivity
  let a := Y*α⁻¹
  let w := (Y*q*2*M + 2*N/u + C) * m^2
  have ha : 0<a := by unfold a; positivity
  have hq : 0 ≤ q := by unfold q; positivity
  have hw' : 0 < w := by unfold w; positivity
  refine ⟨max a (max u⁻¹ w), ha.trans_le (le_max_left ..),?_⟩
  let R := min rA (min rB (min rM (min rN rC)))
  have hR : 0 < R := lt_min hrA (lt_min hrB (lt_min hrM (lt_min hrN hrC)))
  let y x := Scales.b x^5 * fiery G x L
  let o x := (3*E + m)*y x
  have hm' : Tendsto o atTop (𝓝 0) := by
    have hh := (tally_g G L 5 1).const_mul (3*E+m); rw [mul_zero] at hh
    exact hh.congr fun x => by unfold o y; rw [fi]; ring
  filter_upwards [he,(year G L).eventually_gt_atTop 0,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (20*(X+L.val+predReach D+10)),
    hm'.eventually (ge_mem_nhds hR)] with x hx hT hl hJ
  intro c f S T hs hz hT' F Z U U' k k' V hl1 hl2 h1 h2 h3 h4 i hi R' j b t θ pt
  let g := S.ratio
  have hj := hT'.atStep
  have hk := hT'.knobs
  have HZ : S.patch=D := uniq (hs.trans hL.symm) (hj.trans hK.symm)
  have He : 100*macroR S.patch ≤ f.val := by
    change 20*(macroR D+L.val+predReach D+10)≤radiusB x at hl
    have h : c.val ≤ f.val := by
      rw [S.sizes]
      have h := S.patch.L.property; change 0<S.patch.L.val at h
      simpa using Nat.mul_le_mul_left c.val h
    rw [HZ]; omega
  have ht : 0<t := Work.E09.temp_pos hT
  let r := 2*radiusB x/5
  obtain ⟨z,hz1,hz2⟩ := (hx c f S T hs hz hT' F Z U V k hl1 h1 h3).2 j (outside_dome hi (by
    change separation j j + _ ≤ _; simp; omega))
  let e := z ∘ g.parent
  let l : ℝ := 2*E*(b^5*t)
  let t0 : ℝ := m * y x
  have hp : 1 ≤ b := Scales.size x
  have hP : 0 ≤ y x := mul_nonneg (pow_nonneg (zero_le_one.trans hp) _ ) ht.le
  have he' : 0 ≤ l := by unfold l; have hh := hE; positivity
  have hb : l ≤ E*3*y x := by unfold l y; change 2*E*y x≤_; nlinarith only [hE,hP]
  have hl0 : l≤rA ∧ l≤rB := by
    have hw : 0≤t0 := mul_nonneg hm.le hP
    dsimp only [o] at hJ
    have hh : l ≤ R := by unfold t0 at hw; nlinarith only [hb,hJ,hw]
    exact ⟨hh.trans (min_le_left ..), hh.trans ((min_le_right ..).trans (min_le_left ..))⟩
  have ht0 : t0≤min rM (min rN rC) := by
    apply le_trans (b:=R) ?_ ((min_le_right ..).trans (min_le_right ..)); unfold t0
    unfold o at hJ; have hQ : 0 ≤ E * y x := mul_nonneg (by linarith) hP
    nlinarith only [hJ,hQ]
  have HH : E*(radiusB x:ℝ)^5*fiery G x S.patch.L ≤ E*(y x) := by
    rw [hs]; unfold y; have h := Nat.cast_nonneg (α:=ℝ) (radiusB x)
    change _ > 0 at ht
    have hE' := (zero_lt_one.trans_le hE).le
    rw [← mul_assoc]; gcongr; unfold Scales.b; linarith
  have HHz : E*(y x) ≤ l := by unfold l; change E*y x≤2*E*y x; nlinarith only [hE,hP]
  have HV a (ha : separation j (a : Bond c).1 ≤ r) := ((hz2 a ha).trans HH).trans HHz
  have ha' a (ha : separation j (g.parent (a : Bond f).1) ≤ r) := ((hz1 a ha).trans HH).trans HHz
  have hb' a (ha0 : separation j (g.parent (a : Bond f).1) ≤ r) : G.chord (Lattice.gauge e U' a) ≤ l := by
    let o := g.parent a.1
    have hh : remote Z (radiusB x) a := by
      apply outside_dome hi
      change separation j o + _ ≤ _; unfold r at ha0; unfold o; omega
    have hh' := (hx c f S T hs hz hT' F Z U' V k' hl2 h2 h4).1 a hh
    let P := replica S.ratio V
    have hc : G.chord (gauge e P a) ≤ E*y x := by
      change G.chord (gauge (constantGauge z S.ratio) (replica S.ratio V) a) ≤ _
      rw [copied _ S.patch.odd_side V z]; unfold replica; split
      · rw [G.chord_one]; exact mul_nonneg (by linarith only [hE]) hP
      exact (hz2 (o,a.2) ha0).trans HH
    rw [show gauge e U' a = (e a.1*(U' a*(P a)⁻¹)*(e a.1)⁻¹)*gauge e P a by unfold Lattice.gauge; group]
    apply (G.chord_triangle ..).trans
    rw [G.chord_conj]; apply (add_le_add hh' hc).trans
    rw [hs]; unfold l y
    have hf : 1 ≤ b^5 := one_le_pow₀ hp
    change E*t+E*(b^5*t) ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hf (show 0≤E*t by have := ht; have h := zero_lt_one.trans_le hE; positivity)]
  obtain ⟨a1,ha1,he1,hf1⟩ := HA S F j r U l z he' hl0.1 hl1 ha'
  obtain ⟨a2,ha2,he2,hf2⟩ := HA S F j r U' l z he' hl0.1 hl2 hb'
  obtain ⟨b0,hb0,he0⟩ := HB id j r (gauge z V) l he' hl0.2 HV
  have hA0 : A*l ≤ t0 := by unfold t0 m; nlinarith [mul_le_mul_of_nonneg_left hb hA.le,mul_nonneg hB.le (mul_nonneg (by linarith : 0 ≤ E) hP)]
  have hB0 : B*l ≤ t0 := by unfold t0 m; nlinarith [mul_le_mul_of_nonneg_left hb hB.le,mul_nonneg hA.le (mul_nonneg (by linarith : 0 ≤ E) hP)]
  have hbr := funds_branch hT'
  let dx := a1-a2
  have hw := Work.F01.link_bound S hbr F k dx (fun e he => by rw [show Exterior.collect G dx _ = _ from congr_fun (collect_sub G a1 a2) e,Pi.sub_apply,hf1 e he,hf2 e he,sub_self]) Y hY.le i
    (fun U hU hi => HY c f S hk hs hj He (by omega) F U hU 1 _ k hi)
  have hQ (i' : Cell f) (hl : i'∉Z.limit x) (hr : separation j (g.parent i'.1)+4 ≤ r) :
      ‖Work.F03.faceCurl i' dx‖ ≤ α⁻¹*(faceBill T Z x V U i'+faceBill T Z x V U' i') + 2*M*(t0)^2 := by
    have hi : α*‖G.curvature (faceValue U i') - G.curvature (faceValue U' i')‖ ≤ faceBill T Z x V U i'+faceBill T Z x V U' i' := by
      unfold faceBill; rw [if_neg hl,if_neg hl]
      have h1 : α * ‖G.curvature (faceValue U i') - G.curvature (faceValue U' i')‖ = ‖shiftedFine T (till x) (temp x) V U i' - shiftedFine T (till x) (temp x) V U' i'‖ := by
        rw [shiftedFine,shiftedFine,sub_sub_sub_cancel_right,shoot,shoot,← smul_sub,norm_smul,hT'.high,Real.norm_of_nonneg hα.le]
      rw [h1]; exact norm_sub_le ..
    apply (face_pair S i' M t0 rM hM.le (fun u hu => (HM u i').2 hu) (ht0.trans (min_le_left ..))
      U U' z j a1 a2 r hr (ha1.trans hA0) (ha2.trans hA0) he1 he2).trans
    have ht := mul_le_mul_of_nonneg_left hi (inv_pos.mpr hα).le
    rw [← mul_assoc,inv_mul_cancel₀ hα.ne',one_mul] at ht; linarith
  have hpt : pt ∉ Z.intern x := by
    intro hb
    exact outside_dome hi (show separation j pt.1+2*radiusB x≤4*(2*radiusB x) by change separation j j+_ ≤ _; simp; omega) (Finset.mem_filter.mp hb).2
  let n1 := bondBill T Z x V (S.prediction U k) pt+bondBill T Z x V (S.prediction U' k') pt
  have Hp : ‖Bid.bills S dx (pole pt)‖ ≤ u⁻¹*n1+ (2*N/u)*t0^2 := by
    have hu' : predReach S.patch ≤ r := by rw [HZ]; unfold r; omega
    have he := prediction_pair S pt k k' N t0 rN hN.le hbr (fun k u hu => (HN c f S HZ hk k pt u).2 hu)
      (ht0.trans ((min_le_right ..).trans (min_le_left ..))) U U' V z a1 a2 b0 r hu' (ha1.trans hA0) (ha2.trans hA0) (hb0.trans hB0) he1 he2 he0
    unfold n1 bondBill; rw [if_neg hpt,if_neg hpt]
    rw [hk] at he -- rewrites Z? Z uses kernel but not apparent
    have hv : ‖Pressure.Tube.Z S (S.prediction U k) V pt-Pressure.Tube.Z S (S.prediction U' k') V pt‖ ≤ ‖shiftedBond T (till x) (temp x) V (S.prediction U k) pt‖ + ‖shiftedBond T (till x) (temp x) V (S.prediction U' k') pt‖ :=
      (by
        have h := norm_sub_le (shiftedBond T (till x) (temp x) V (S.prediction U k) pt) (shiftedBond T (till x) (temp x) V (S.prediction U' k') pt)
        unfold shiftedBond at h; rwa [sub_sub_sub_cancel_right] at h)
    change u*‖_‖ ≤ _ at he
    refine (le_of_mul_le_mul_left (a:=u) ?_ hu)
    apply he.trans
    rw [div_eq_mul_inv]
    apply (add_le_add_left hv _).trans_eq
    field_simp
  have hf : C*(t0)^2+‖Exterior.collect G dx i‖ ≥ G.chord (U i*(U' i)⁻¹) := by
    have hh1 w (a : Bid.Dir G f) (he : AgreeNear g.parent j r (gauge e w) (represent a)) : gauge e w i=G.lieExp (Exterior.collect G a i) := by
      rw [he i (by change separation j j ≤ _; simp)]; unfold represent increment; simp
    have H : gauge e U i*(gauge e U' i)⁻¹ = e i.1*(U i*(U' i)⁻¹)*(e i.1)⁻¹ := by unfold Lattice.gauge; group
    rw [← G.chord_conj (e i.1), ← H, hh1 _ a1 he1, hh1 _ a2 he2]
    have hh := HC t0 (Exterior.collect G a1 i) (Exterior.collect G a2 i) (ht0.trans ((min_le_right ..).trans (min_le_right ..)))
      ((norm_le_pi_norm a1 (pole i)).trans (ha1.trans hA0)) ((norm_le_pi_norm a2 (pole i)).trans (ha2.trans hA0))
    unfold dx; rw [collect_sub,Pi.sub_apply, add_comm]; exact hh
  let yF (z : Cover) (p : PlaqAxes) := (patchAt S z j,p)
  have HS z (h : z∈box (macroR S.patch)) (p : PlaqAxes) :
      (yF z p:Cell f)∉ Z.limit x ∧ separation j (g.parent (yF z p:Cell f).1)+4 ≤ r := by
    have hv : separation j (g.parent (yF z p:Cell f).1) ≤ macroR D + L.val := by rw [← HZ,← hs]; exact reaches S z j h
    have hx : separation j (g.parent (yF z p:Cell f).1)+4 ≤ r := by unfold X at hl; unfold r; omega
    refine ⟨fun hb => ?_,hx⟩
    apply outside_dome hi ?_ (Finset.mem_filter.mp hb).2
    change separation j (g.parent (yF z p:Cell f).1)+2*radiusB x ≤ 4*(2*radiusB x); unfold r at hx; omega
  let v := ∑ z ∈ box (macroR S.patch), ∑ p : PlaqAxes, θ (yF z p:Cell f)
  have H1 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z (hz:z∈box (macroR S.patch)) => Finset.sum_le_sum fun p (_:p∈Finset.univ) =>
    hQ (yF z p) (HS z hz p).1 (HS z hz p).2) hY.le
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,Finset.card_univ] at H1
  -- q card
  change G.chord (U i*(U' i)⁻¹) ≤ max _ _ * (v+n1+(b^5*t)^2)
  have hU : 0 ≤ v := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun _ _ => add_nonneg (faceBill_nn ..) (faceBill_nn ..)
  have hU' : 0 ≤ n1 := add_nonneg (bondBill_nn ..) (bondBill_nn ..)
  let a' := max a (max u⁻¹ w)
  have hi' : a ≤ a' := le_max_left ..
  have h8 : u⁻¹ ≤ a' := (le_max_left ..).trans (le_max_right ..)
  have h9 : w ≤ a' := (le_max_right ..).trans (le_max_right ..)
  suffices HH : _ ≤ a*v+u⁻¹*n1+w*(b^5*t)^2 by
    exact HH.trans (by nlinarith only [mul_le_mul_of_nonneg_right hi' hU, mul_le_mul_of_nonneg_right h8 hU', mul_le_mul_of_nonneg_right h9 (sq_nonneg (b^5*t))])
  apply hf.trans
  have h6 : Y * (∑ z ∈ box (macroR S.patch), ∑ p : PlaqAxes, ‖Exterior.dColor G f 1 dx ((wrap f z + S.ratio.embed j), Exterior.plaquette p)‖) ≤ a*v + Y*q*2*M*t0^2 := by
    apply H1.trans_eq
    have H : q = (box (macroR S.patch)).card * (Fintype.card PlaqAxes:ℝ) := by rw [HZ]
    unfold a v θ; rw [H]; ring
  apply (add_le_add_right (hw.trans (add_le_add h6 Hp)) _).trans_eq
  unfold w t0 y b t; ring
end YM.SectorNext.Remainder.Center
