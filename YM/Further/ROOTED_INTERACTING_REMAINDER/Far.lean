import YM.Push.SECTOR_MEASURE.Oriented


/-!
# Truly exterior rows of the intact all-store/tag grant

Not an implementation of a
component Gaussian remainder.

We do NOT drop defaults from the Allocation
premise.

Unassigned = rows OUTSIDE the very store that was charged (even if
booking read all plaquettes); use the earned Interior receipt with rotated
gauges centered on those rows (in contrast to Stitches / unhit which have
prerequisite `i ∈ outs`).

This produces the small defect loss *per site*,
not the annular claim for post-affine remainders in other campaigns.

All
statements kept on true real torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open Pressure Pressure.Stores Pressure.Teller Pressure.Tube Bid Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}
  {A : Stores S} {U : Config G f} {k : S.Choices} {V : Config G c}

/-- Header used ONLY before removing the Allocation factor. -/
def Beyond (A : Stores S) (x : ℝ) (o : Site c) := o ∉ A.dome (2*radiusB x)

private lemma untouched {o y : Site c} (ho : Beyond A x o) (h : separation o y ≤ 2*radiusB x) : y ∉ A.place := by
  intro hy; exact ho (halo_spec.mpr ⟨y,hy,(separation_comm o y) ▸ h⟩)

lemma fineMargin (h : Seeded A U k V x W) {o : Site c} (ho : Beyond A x o)
    {b : Cell f} (hh : separation o (S.ratio.parent b.1) ≤ 2*radiusB x) : toll U b ≤ fiery G x S.patch.L/2 := by
  apply (h.fine b).2; intro hz
  apply untouched ho hh
  apply mem_union_left
  apply mem_union_left
  apply mem_biUnion.mpr
  exact ⟨b,hz,mem_image_of_mem _ (by simp [RG.touched,Lattice.visits,square])⟩

lemma wireMargin (h : Seeded A U k V x W) {o : Site c} (ho : Beyond A x o)
    {b : Bond c} (hh : separation o b.1 ≤ 2*radiusB x) :
    wire (S.prediction U k) V b ≤ 2*W*fiery G x S.patch.L := by
  apply (h.coarse _).2; intro hz
  apply untouched ho hh
  exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨b,hz,by simp [pinPos]⟩))

lemma outMargin (h : Seeded A U k V x W) {o : Site c} (ho : Beyond A x o)
    {b : Cell c} (hh : separation o b.1 ≤ 2*radiusB x) : toll V b ≤ temp x := by
  by_contra! hg
  apply untouched ho hh
  apply mem_union_right
  rw [h.exactFlags]
  exact (RG.flags_spec ..).mpr ⟨b,by simp [RG.touched,Lattice.visits,square],hg⟩

lemma keptMargin {o : Cell f} (h : Seeded A U k V x W) (ho : o ∉ A.limit x)
    {T : Tube G S} {b : ℝ} (hb : LaneCounts T.up x (fiery G x S.patch.L) T.high b 1 S.ratio.parent) :
    PathData.kept T.high (fiery G x S.patch.L) o.1 U := by
  have he : Beyond A x (S.ratio.parent o.1) := fun hi=> ho (mem_filter.mpr ⟨mem_univ _,hi⟩)
  intro i
  by_contra! hf
  have hx := hb.dropped _ _ _ hf
  have hw := fineMargin (b:=i) h he (show separation _ _ ≤ 2*radiusB x by omega)
  -- ensure inference on b
  let t := fiery G x S.patch.L
  have ht : 0≤t := Push.SectorMeasure.temp_nonneg _
  have hq : t ≤ t * Real.exp ((separation o.1 i.1:ℝ) / T.high.relaxation) :=
    le_mul_of_one_le_right ht (Real.one_le_exp (by have := T.high.radius_pos; positivity))
  exact not_le_of_gt hf ((show toll U i ≤ t from hw.trans (by linarith)).trans hq)

-- Square estimates for the intact rows ; even retain a radial
-- shifted Gaussian version useful if changing number of default hypotheses.
private lemma shifted {m r : ℝ} (hm : 0 ≤ m) (v y : G.Color) (hy : ‖y‖ ≤ Real.sqrt m*r) :
    (Real.sqrt m*r-‖v‖)^2/2 ≤ m*r^2/2 + (‖v‖^2/2 - inner ℝ v y) := by
  have hi := (real_inner_le_norm v y).trans (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  nlinarith only [hi,show Real.sqrt m^2*r^2=m*r^2 by rw [Real.sq_sqrt hm]]

lemma fine_retained (T : Tube G S) (i : Cell f) (h : Seeded A U k V x W) (he : i ∉ A.limit x)
    {C : ℝ} (hb : LaneCounts T.up x (fiery G x S.patch.L) T.high C 1 S.ratio.parent) :
    let v := T.Mv (till x) (temp x) V (i,false)
    (Real.sqrt T.high.direct*toll U i-‖v‖)^2/2 ≤
      T.workF (till x) U V (fiery G x S.patch.L) (temp x) i := by
  intro v
  let d := T.Mv (till x) (temp x) V (i,true)
  have hs : ‖Pressure.shoot T.high U i‖ ≤ Real.sqrt T.high.direct*toll U i := by
    rw [Pressure.shoot,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)
  have hu := shifted T.high.quadratic_pos.le v _ hs
  let y := shorten T.up (till x) 1 U i
  have H : 0 ≤ ‖y‖^2/2 + (‖d‖^2/2-inner ℝ d y) := by
    nlinarith [real_inner_le_norm d y,sq_nonneg (‖d‖-‖y‖)]
  have hz : Beyond A x (S.ratio.parent i.1) := fun H=> he (mem_filter.mpr ⟨mem_univ _,H⟩)
  have hf := fineMargin (b:=i) h hz (by simp)
  have hh := keptMargin h he hb
  have hn : G.chord (faceValue U i) ≤ fiery G x S.patch.L := by
    change G.chord _ ≤ _ at hf
    linarith only [hf,show 0 ≤ fiery G x S.patch.L from Push.SectorMeasure.temp_nonneg (betaF G x S.patch.L)]
  unfold Tube.workF
  rw [Fintype.sum_bool,crown,trunk,if_pos hh,PathData.clipped,if_pos hn]
  unfold Tube.Xf plotted
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold toll at hu ⊢; unfold d v y at *
  linarith only [H,hu]

lemma bond_retained (T : Tube G S) (V Q : Config G c) (i : Bond c) (x : ℝ) :
    let w := T.Mw (till x) (temp x) V i
    (Real.sqrt S.kernel.penalty*wire Q V i - ‖w‖)^2/2 ≤ T.workI (till x) Q V (temp x) i := by
  intro w
  refine shifted S.kernel.penalty_pos.le w (Z S Q V i) ?_
  rw [Z,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)

/-! Need a held small chart for interior_cost, centered at **any exterior o**,
not at a p in A.outs as Stitches buys. Kept polynomial B loss is harmless
here, even with h calculated from `largeT`: β*t*h²→0. -/
lemma brazed (P : Teller G) (L : Side) (W : ℝ) (_hW : 0<W) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
      ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
      ∀ T : Tube G S, P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
      SliceSet S F U → Alive S U k → Seeded A U k V x W →
      let B := radiusB x; let h := C*(B:ℝ)^10*largeT G x L
      ∀ o, Beyond A x o → ∃ z : Site c → G.El,
        (∀ i : Bond c, separation o i.1 ≤ 2*B/5 → G.chord (Lattice.gauge z V i) ≤ h) ∧
        ∀ i : Bond f,separation o (S.ratio.parent i.1) ≤ 2*B/5 →
          G.chord (Lattice.gauge (z∘S.ratio.parent) U i) ≤ h := by
  obtain ⟨D,hD,HD⟩ := Work.E02.answer G L P.j P.bind
  -- Shift to `largeT` coarse too.
  let a := G.slopeConstant*Real.log L.val
  let m := (P.j+3)*L.val+4*L.val
  let nP := (Fintype.card PlaqAxes:ℝ)
  let b := (2*(m:ℝ)+1)^4*nP
  let H := 16*3^5*nP
  let C := H+(D*b+1)
  have hnP : 0 ≤ nP := by unfold nP; positivity
  have h0 : 0 ≤ b := by unfold b; positivity
  have hH : 0 ≤ H := by unfold H; positivity
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [Work.E08.eventual_radiusB (100*(m+L.val+1)),
    Work.E04.eventually_temp_le a (Work.E04.shift_nonneg G L),
    Work.E08.eventual_fiery G L 2, Work.E08.eventual_fiery G L (2*W)] with x hx ha hf hw
  intro c f S hL hs T hT F A U k V hU hk hV B h o ho
  have hm : macroR S.patch=m := by unfold m macroR RG.Patch.radius; rw [hT.atStep,hL]
  change 100*(m+L.val+1)≤ B at hx
  change 100*(1+B)≤ c.val at hs
  have he : 100*macroR S.patch ≤ f.val := by
    have hh : c.val ≤ f.val := by
      rw [S.sizes]; exact Nat.le_mul_of_pos_right _ S.patch.L.property
    omega
  have hB : 1 ≤ (B:ℝ) := by exact_mod_cast (show 1≤B by omega)
  let t := largeT G x L
  have ht : 0 ≤ t := by unfold t largeT; positivity
  have hf0 : 0 ≤ fiery G x L := Push.SectorMeasure.temp_nonneg _
  have ha' : temp x ≤ 2*fiery G x L := ha
  have hface (y : Site c) (h : separation o y ≤ B) (j : PlaqAxes) : toll V (y,j) ≤ t := by
    apply (outMargin (b:=(y,j)) hV ho (by change _≤2*B; exact h.trans (by omega))).trans (ha'.trans hf)
  obtain ⟨z,hz⟩ := Work.E08.axial_patch o V (2*B/5) B (by omega) (by omega) t ht hface
  let t0 := H*(B:ℝ)^5*t
  have hzV (i : Bond c) (hi : separation o i.1 ≤ 2*B/5) : G.chord (Lattice.gauge z V i) ≤ t0 := by
    apply (hz i hi).trans
    calc
      (16:ℝ)*(2*(B:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*t ≤ 16*(3*(B:ℝ))^5*(Fintype.card PlaqAxes:ℝ)*t := by gcongr; linarith only [hB]
      _ = _ := by unfold t0 H nP; ring
  have ht0 : 0 ≤ t0 := by unfold t0; positivity
  have hprice : (D*b+1)*t+t0 ≤ h := by
    calc
      _ ≤ (D*b+1)*(B:ℝ)^10*t + H*(B:ℝ)^10*t := add_le_add
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB)) ht)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by norm_num)) hH) ht)
      _ = _ := by dsimp only [h,t,C]; ring
  refine ⟨z,fun i hi=>(hzV i hi).trans ((le_add_of_nonneg_left (by positivity)).trans hprice), fun i hi => ?_⟩
  let y := S.ratio.parent i.1
  have hy : separation o y ≤ 2*B/5 := hi
  have hpo : port S y U ≤ b*t := by
    have hh : ∀ j : Cell f, separation o (S.ratio.parent j.1) ≤ 2*B → toll U j ≤ t := fun j hj => by
      have hu := fineMargin (b:=j) hV ho hj; rw [hL] at hu
      change _ ≤ largeT G x L; linarith only [hf,hf0,hu]
    have hg := Work.E08.port_le o (2*B) t ht hh y (by rw [hm,hL]; omega)
    rw [hm] at hg; exact hg
  let Q := S.prediction U k
  let R := replica S.ratio V
  have hl : G.chord (U i*(R i)⁻¹) ≤ (D*b+1)*t := by
    have huse : usable S U y k := fun j hj => listed_of_alive hk _
    have hi := HD c f S hT.knobs hL hT.atStep he (by omega) F U hU V i k huse
    apply hi.trans
    have hwire : wire Q V (y,i.2) ≤ t := by
      have he := wireMargin (b:=(y,i.2)) hV ho (show separation o y ≤ 2*B by omega)
      rw [hL] at he; exact he.trans hw
    have hh : (if y = S.ratio.parent (i.1+step i.2) then 0 else wire Q V (y,i.2)) ≤ t := by split <;> assumption
    exact (add_le_add (mul_le_mul_of_nonneg_left hpo hD.le) hh).trans_eq (by ring)
  let g := z∘S.ratio.parent
  have hv' : G.chord (gauge g R i) ≤ t0 := by
    change G.chord (gauge (constantGauge z S.ratio) (replica S.ratio V) i) ≤ t0
    rw [copied _ S.patch.odd_side V z]
    unfold replica; split
    · rw [G.chord_one]; exact ht0
    exact hzV _ hi
  change G.chord (gauge g U i) ≤ h
  rw [show gauge g U i=(g i.1*(U i*(R i)⁻¹)*(g i.1)⁻¹)*gauge g R i by unfold Lattice.gauge; group]
  apply (G.chord_triangle _ _).trans
  rw [G.chord_conj]
  exact (add_le_add hl hv').trans hprice

/-- A convenient joint currency for late-x use. -/
def fade (t h q : ℝ) (R : ℕ) (A C τ : ℝ) :=
  2*(A*t)*(C*h*widen R h τ)+(A*t)*(C*(A*t)*widen R h τ)+C*q^4

-- splitting off Crowds constant for now
lemma toll_LD (F J h e : ℝ) (hF : 0 ≤ F) (T : Tube G S) (R : ℕ) (t : ℝ)
    (U : Config G f) (Q V : Config G c) (i : Cell c)
    (hf : ∀ v : Bool, ‖T.vision R t V (i,v)‖ ≤ F)
    (hG : ∀ v : Bool, ‖lGap T R U Q V (i,v)‖ ≤ J*h*e ∧
        ‖dGap T R V (T.vision R t V) (i,v)‖ ≤ J*F*e) :
    -(2*F*(J*h*e) + F*(J*F*e)) ≤ T.workL R U Q V t i + T.workD R V t i := by
  have h1 j : -(F*(J*h*e)) ≤ inner ℝ (T.vision R t V (i,j)) (lGap T R U Q V (i,j)) := by
    exact neg_le_of_abs_le ((abs_real_inner_le_norm ..).trans (mul_le_mul (hf _) ((hG j).1) (norm_nonneg _) hF))
  have h2 j : -(F*(J*F*e)) ≤ inner ℝ (T.vision R t V (i,j)) (dGap T R V (T.vision R t V) (i,j)) := by
    exact neg_le_of_abs_le ((abs_real_inner_le_norm ..).trans (mul_le_mul (hf _) ((hG j).2) (norm_nonneg _) hF))
  rw [workL_gap,workD_gap,Fintype.sum_bool,Fintype.sum_bool]
  linarith only [h1 true,h1 false,h2 true,h2 false]

private lemma unspent_x (C D τ h : ℝ) (x W : ℝ)
    (o : Stores S) {T : Tube G S} {U : Config G f} (V : Config G c) (k : S.Choices) (hz : Seeded o U k V x W)
    (hc : 0 ≤ C) (hd : 0 ≤ D) (hh : 0 ≤ h)
    (hl : LaneCounts T.up x (fiery G x S.patch.L) T.high D 1 S.ratio.parent)
    (hM : Maximum D T x V)
    (hC : ∀ i : Cell c,i ∉ o.outs x → -(C*temp x^4) ≤ T.workC (till x) V (temp x) i)
    (hLD : ∀ i : Cell c,i ∉ o.outs x → ∀ v : Bool,
      ‖lGap T (till x) U (S.prediction U k) V (i,v)‖ ≤ C*h*widen (till x) h τ ∧
      ‖dGap T (till x) V (T.vision (till x) (temp x) V) (i,v)‖ ≤ C*(D*(fiery G x S.patch.L))*widen (till x) h τ) :
    -((Fintype.card (Cell c):ℝ)*fade (fiery G x S.patch.L) h (temp x) (till x) D C τ) ≤
      unassigned o T x U k V := by
  let R := till x
  let s := temp x
  let t := fiery G x S.patch.L
  let Q := S.prediction U k
  let l := fade t h s R D C τ
  have ht : 0≤t := Push.SectorMeasure.temp_nonneg _
  have hs : 0≤s := Push.SectorMeasure.temp_nonneg _
  have he : 0 ≤ widen R h τ := widen_nonneg _ hh
  have hh' : 0 ≤ l := by unfold l fade; positivity
  have hout : ∀ i ∈ (o.outs x)ᶜ, -l ≤ T.workC R V s i + (T.workL R U Q V s i + T.workD R V s i) := by
    intro i hi
    have hx : i ∉ o.outs x := mem_compl.mp hi
    have hr := hC i hx
    have hp := toll_LD (D*t) C h (widen R h τ) (by positivity) T R s U Q V i (fun v => hM.up _) (hLD i hx)
    unfold l fade
    linarith only [hr,hp]
  have hcS : -((Fintype.card (Cell c):ℝ)*l) ≤ ∑ i ∈ (o.outs x)ᶜ,(T.workC R V s i+(T.workL R U Q V s i+T.workD R V s i)) := by
    have he : (((o.outs x)ᶜ.card):ℝ) ≤ Fintype.card (Cell c) := by exact_mod_cast card_le_univ _
    calc
      _ ≤ (((o.outs x)ᶜ.card):ℝ)*(-l) := by rw [mul_neg]; exact neg_le_neg (mul_le_mul_of_nonneg_right he hh')
      _ = ∑ i ∈ (o.outs x)ᶜ, -l := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hout
  have hfS : 0 ≤ ∑ i∈(o.limit x)ᶜ,T.workF R U V t s i :=
    sum_nonneg fun i hi => (by positivity : 0 ≤ (_:ℝ)^2 / 2).trans (fine_retained T i hz (mem_compl.mp hi) hl)
  have hiS : 0 ≤ ∑ i∈(o.intern x)ᶜ,T.workI R Q V s i :=
    sum_nonneg fun i hi => (by positivity : 0 ≤ (_:ℝ)^2 / 2).trans (bond_retained T V Q i x)
  have hnS : 0 ≤ ∑ i∈(o.coordN x)ᶜ,T.workN R V s i := sum_nonneg fun i _ => by unfold Tube.workN; positivity
  unfold unassigned assessed tally talli tallc talln talll
  dsimp only
  rw [← sum_add_sum_compl (o.limit x),←sum_add_sum_compl (o.intern x),←sum_add_sum_compl (o.outs x),
    ←sum_add_sum_compl (o.coordN x),←sum_add_sum_compl (o.outs x),←sum_add_sum_compl (o.outs x)]
  rw [sum_add_distrib]
  rw [sum_add_distrib,sum_add_distrib] at hcS
  dsimp only [R,t,s,Q,l] at hcS hfS hiS hnS
  linarith only [hcS,hfS,hiS,hnS]

lemma patch_same {A B : Patch} (h : A.L=B.L) (hh : A.J=B.J) : A=B := by cases A; cases B; congr

/-- Post-L uniform sufficiency on arbitrarily deep plateau uses (denominator
and labels not arguments!). Retains turn across the true `Alive`. -/
theorem far_station (P : Teller G) (L : Side) (W : ℝ) (hW : 0<W) :
    ∃ D C J τ : ℝ, 0<D ∧ 0<C ∧ 0<J ∧ 0<τ ∧ ∀ᶠ x : ℝ in atTop,
      let t := fiery G x L; let h := stitchCost G L J x; let s := temp x
      let err := fade t h s (till x) D C τ
      0≤err ∧ ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
        ∀ (T : Tube G S), P.Funds S T →
        ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
        SliceSet S F U → Alive S U k → Seeded A U k V x W →
          -(Fintype.card (Cell c):ℝ)*err ≤ meanRest A T x U k V := by
  obtain ⟨D,hD,HD⟩ := Work.E04.answer Work.E03.answer P
  obtain ⟨δ,hδ,B,hB,HB⟩ := Work.E05.answer P
  obtain ⟨J,hJ,HJ⟩ := brazed P L W hW
  by_cases he : ∃ X : Patch,X.L=L ∧ X.J=P.j ∧ X.Branches P.bind G
  swap
  · refine ⟨1,1,1,1,by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
    filter_upwards [(Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0)] with x hx
    intro t H s err
    have ht := Push.SectorMeasure.temp_nonneg x
    have hf : 0≤t := Push.SectorMeasure.temp_nonneg _
    have hh : 0≤H := by unfold H stitchCost largeT; positivity
    have hv : 0≤widen (till x) H 1 := widen_nonneg _ hh
    refine ⟨by unfold err s fade; positivity, fun c f S hL _ T h=>?_⟩
    exact False.elim (he ⟨S.patch,hL,h.atStep,h.kernel⟩)
  obtain ⟨X,hL,hX,he⟩ := he
  obtain ⟨E,τ,r,hE,hτ,hr,H⟩ := interior_cost P X he
  let C := max B E
  have hC : 0<C := hB.trans_le (le_max_left ..)
  refine ⟨D,C,J,τ,hD,hC,hJ,hτ,?_⟩
  have HT : Tendsto (stitchCost G L J) atTop (𝓝 0) := by
    convert radius_stitch G L J 0 using 2; simp
  filter_upwards [HT.eventually (ge_mem_nhds hr), HJ, (HB L W).late,(HD L W).late,
    (Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0),
    Work.E08.eventual_radiusB (100*(predReach X+10))] with x hx hj hb hd hz hh
  intro t g s err
  have ht := Push.SectorMeasure.temp_nonneg x
  have hf : 0≤t := Push.SectorMeasure.temp_nonneg _
  have hg : 0≤g := by unfold g stitchCost largeT; positivity
  have hv : 0≤widen (till x) g τ := widen_nonneg _ hg
  refine ⟨by unfold err fade; have hs : 0 ≤ s := ht; positivity,fun c f S hm hs T hP F A U k V hU hk hV=>?_⟩
  have hSp : S.patch=X := patch_same (hm.trans hL.symm) (hP.atStep.trans hX.symm)
  have hq (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c)
      (hU : SliceSet S F U) (hk : Alive S U k) (hV : Seeded A U k V x W) :
      -(Fintype.card (Cell c):ℝ)*err ≤ unassigned A T x U k V := by
    have hTr := hd c f S hm hs T hP F A U k V hU (hV.plot hk)
    rw [←hm] at hTr
    have hCover := hb c f S hm hs T hP F A U k V hU (hV.plot hk)
    dsimp only [err,t,g,s]; rw [neg_mul,←hm]
    refine unspent_x C D τ _ x W A V k hV hC.le hD.le (by rw [hm]; exact hg) hTr.1 hTr.2.2 ?_ ?_
    · intro i hi
      have he : Beyond A x i.1 := fun hh=>hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
      apply le_trans _ (hCover.middle i (outMargin hV he (by simp)))
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
    intro i hi v
    have he : Beyond A x i.1 := fun hh=>hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
    obtain ⟨z,h1,h2⟩ := hj c f S hm hs T hP F A U k V hU hk hV i.1 he
    have hR : 3*till x+4+predReach S.patch ≤ 2*radiusB x/5 := by rw [hSp]; unfold till; omega
    obtain ⟨ha,hi⟩ := H c f S T hSp hP k (till x) _ hR U V g hg hx (i,v) z h2 h1
    rw [hm]
    have hw (j) : ‖T.vision (till x) (temp x) V j‖ ≤ D * fiery G x L := hm ▸ hTr.2.2.up j -- dependent S hm? dangerous
    have hp := hi _ (D*t) (by positivity) hw
    exact ⟨ha.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hg) hv),
      hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity : 0≤D*t)) hv)⟩
  unfold meanRest; rw [← av_const (-(Fintype.card (Cell c):ℝ)*err)]; refine av_mono ?_
  intro i
  have p := funds_branch hP
  have h₁ := Oriented.carry (S:=S) i p k U
  have hAlive : Alive S (pull i 0 U) (choice i k) := by
    unfold Alive; rw [h₁.1]; exact hk
  exact hq (turnForest i F) (turnStore i A) (pull i 0 U) (choice i k) (pull i 0 V)
    (turn_sliced i F U hU) hAlive (pull_seeded i p hV)

end YM.Further.RootedInteractingRemainder
