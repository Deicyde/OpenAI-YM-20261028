import YM.SectorNext.LARGE_FIELD_REMAINDERS.CollarData


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Local annulus analytic quote (individual rows)

cost at fixed P,L (and can use any Cleans satisfying those
purchases, in particular the actual one from local Wide). Even though Teller
quotes in `Serves` issue only under Plot, can employ the per-path, unmasked shift
and Crowds estimates also here: even if the caller wants this _after_
drop of unrelated defaults and doesn't supply the entire global Plot.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

structure Returns (T : Tube G S) (x e : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) (a : Directions G f) (p : Site c) : Prop where
  face (q : Cell f) : S.ratio.parent q.1=p →
    Summable (perCharge T.up (till x) (replica S.ratio V) a q) ∧
    -e ≤ T.workF (till x) U V (fiery G x S.patch.L) (temp x) q - squareP T (till x) (temp x) V (replica S.ratio V) a q
  coarse (q : Cell c) : q.1=p →
    -e ≤ T.workC (till x) V (temp x) q + (T.workL (till x) U (S.prediction U k) V (temp x) q+
      T.workD (till x) V (temp x) q)
  noise (q : Bond c) : q.1=p →
    -e ≤ T.workI (till x) (S.prediction U k) V (temp x) q - squareQ T (till x) (temp x) V (replica S.ratio V) k a q
  -- real legality receipt for derivatives, even at unselected exterior rows and all
  -- possible slots through cut lists.
  cover (q : Cell f) : S.ratio.parent q.1=p →
    let test b := DifferentiableAt ℝ (fun t : ℝ => G.curvature (faceValue (increment (replica S.ratio V) (t • a)) b)) 0
    test q ∧ ∀ i : ℕ, (T.up.row q.2 i).2.length ≤ till x → test (slotFace (T.up.row q.2 i).2 q.1)
  Qline (q : Bond c) : q.1=p →
    let J := actuate S (replica S.ratio V) q k a; let u := qVar S (replica S.ratio V) q k a
    DifferentiableAt ℝ (fun t => G.curvature (J t*(J 0)⁻¹)) 0 ∧ DifferentiableAt ℝ (G.mat∘J) 0 ∧
    G.colorMat u=(deriv (G.mat∘J) 0)*G.mat ((S.prediction (replica S.ratio V) k q)⁻¹)

private lemma uniq {A B : Patch} (h : A.L=B.L) (ht : A.J=B.J) : A=B := by cases A; cases B; congr
private def bill (G : Gauge) (M C : ℝ) (L : Side) (x : ℝ) := C*b x * weakRadius (G:=G) M L x^3
private lemma bill_pay (M C : ℝ) (L : Side) (n : ℕ) :
    Tendsto (fun x => b x^n * y G L x * bill G M C L x) atTop (𝓝 0) := by
  have he := (tally_g G L (n+16) 3).const_mul (C*M^3)
  rw [mul_zero] at he
  refine he.congr' ?_
  filter_upwards [(year G L).eventually_gt_atTop 0] with x hx
  have hg := yg2 G L hx
  unfold bill weakRadius
  rw [fi]
  calc
    _ = C*M^3*(b x^(n+16)*p G L x^3*g G L x)*(y G L x*g G L x^2) := by rw [hg]; ring
    _ = b x^n * y G L x * _ := by rw [pow_add]; ring

private lemma frees_plot (F : Stores S) (x W : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) :
    ∃ A : Stores S, A.Plot U k V x W := by
  let A : Stores S := ⟨∅,∅,∅⟩
  have h b : A.dome b=∅ := by ext; simp [Stores.dome,halo_spec,Stores.place,A]
  refine ⟨A,⟨fun p hp => ?_,fun e he => ?_,fun i hi => ?_,fun j hj => ?_⟩⟩ <;> simp_all only [h,Finset.disjoint_empty_left,not_true_eq_false, Finset.notMem_empty]

set_option maxHeartbeats 880000 in
/-- One exponent cost valid at every exterior sweep row, including affine
subtractions and the L/D defects. Selected-row geometry need NOT proved for
this statement: quote is simultaneous even at every unselected exterior row.
To use the comparison in a full step still need to respect this exterior on
all rows actually assigned to it, and to instantiate Δ on their actual paths as
in `perCharge`,`qVar`. Halo size D any; need pay separately after summing those
anchors.
-/
lemma coat (P : Teller G) (L : Side) (X : ℝ) (hX : 1 ≤ X) : ∀ W : ℝ, ∃ e : ℝ → ℝ,
    (∀ᶠ x in atTop,0≤e x) ∧ (∀ n : ℕ,Tendsto (fun x => b x^n*y G L x*e x) atTop (𝓝 0)) ∧ ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ D (F : Forest S.ratio) O A U k V p a, SliceSet S F U → Cleans (S:=S) X x U V p a →
        inSweep O A D (radiusB x) p → Wide O A D x W U k V → Returns T x (e x) U V k a p := by
  intro W; by_cases hx : ∃ D : Patch, D.L=L ∧ D.J=P.j ∧ D.Branches P.bind G
  swap
  · refine ⟨fun _=>0,by simp,fun n => ?_,Eventually.of_forall fun b c f S T hL hv hT => ?_⟩
    · simp only [mul_zero]; exact tendsto_const_nhds
    exact (hx ⟨S.patch,hL,hT.atStep,hT.kernel⟩).elim
  obtain ⟨D,hL,hD,hB⟩ := hx
  obtain ⟨C,τ,r,hC,ht,hr,h⟩ := interior_cost P D hB
  obtain ⟨E,M,hE,hM,hr',he⟩ := reacts P L X hX
  obtain ⟨ξ,hξ,J,hJ,hpJ⟩ := Work.E05.answer P
  obtain ⟨A0,hA,hP⟩ := Work.E04.answer Work.E03.answer P
  let d := P.top.clip.direct
  let m := Real.sqrt d + P.top.paths + 1
  let N := max (2*G.colorScale+1) 1
  have hh : 0 < m := lt_of_lt_of_le zero_lt_one (by unfold m; have := P.top.paths_pos; have hd := Real.sqrt_nonneg d; linarith)
  have hN : 0 < N := zero_lt_one.trans_le (le_max_right ..)
  let B := max E A0
  have hb : A0≤B := le_max_right ..
  have hv : E≤B := le_max_left ..
  have hQ := hE.trans_le hv
  let Y := 4*(m*B)^2*N+4*B^2
  have hY : 0≤Y := by unfold Y; positivity
  let e x := weakLoss (G:=G) M C τ A0 J L x
  let s := weakRadius (G:=G) M L
  have hz := zero_lt_one.trans_le (hX.trans hM)
  have hr₁ (x : ℝ) : 0 ≤ s x := by unfold s weakRadius; have := Scales.size x; unfold fiery; have := temp_nonneg (betaF G x L); positivity
  have hq x : 0≤e x := by
    have ht := hr₁ x
    have he := temp_nonneg (betaF G x L)
    have hw := widen_nonneg (till x) (τ:=τ) ht
    unfold e weakLoss fiery; unfold s at *; positivity
  let E0 := fun x => e x+bill G M Y L x
  have he0 x : e x ≤ E0 x := by unfold E0 bill; have := hr₁ x; have := Scales.size x; unfold s at *; linarith [show 0≤Y*b x * weakRadius (G:=G) M L x^3 by positivity]
  have hl0 x : bill G M Y L x ≤ E0 x := le_add_of_nonneg_left (hq x)
  refine ⟨E0,Eventually.of_forall (fun x => (hq x).trans (he0 x)),fun n => ?_,?_⟩
  · have ht' := (loss_delay G L M C τ A0 J hz.le hC.le ht hA.le hJ.le n).add (bill_pay (G:=G) M Y L n)
    rw [add_zero] at ht'
    exact ht'.congr fun x => by dsimp only [E0,e,Function.comp_apply]; ring
  have hnear : Tendsto s atTop (𝓝 0) := by simpa only [pow_zero,one_mul] using hr' 0
  filter_upwards [he,hnear.eventually (ge_mem_nhds hr), (hpJ L W).late, (hP L W).late,
    (year G L).eventually_gt_atTop 0, Work.E07.temp_coarse_le G L,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (10*(predReach D+10))] with x he hf hu hF hs hθ hd
  intro c f S T hL' hR hT j F O Z U k V i a hU hcl hsw hWide
  have hD' : S.patch=D := uniq (hL'.trans hL.symm) (hT.atStep.trans hD.symm)
  obtain ⟨xi,hxi⟩ := frees_plot Z x W U V k
  obtain ⟨h1,h4,h2⟩ := hF c f S hL' hR T hT F xi U k V hU hxi
  have h3 := hu c f S hL' hR T hT F xi U k V hU hxi
  obtain ⟨Λ,Λ',hP,hP'⟩ := hT.feeds
  rw [← hT.high] at hP
  have hvalues := he _ _ S T hL' hT U V i a hcl k
  let t := fiery G x L
  let v := s x
  let R := till x
  have hz : 0 < t := Work.E09.temp_pos hs
  have hv0 : t≤v := by
    have h : 1 ≤ M := hX.trans hM
    have hb := one_le_pow₀ (Scales.size x) (n:=5)
    unfold v s weakRadius
    exact le_mul_of_one_le_left hz.le (one_le_mul_of_one_le_of_one_le h hb)
  have hv1 := hz.trans_le hv0
  obtain ⟨hE0,hB0,hK0,hframe⟩ := CleanFaces O Z j x W U k V hWide i hsw
  rw [hL'] at hE0 hB0
  have hD (Q : ℕ) : R+1 ≤ thin x := by unfold R till thin; omega
  have hslot (u : Cell f) (hu : S.ratio.parent u.1=i) (i₀ : ℕ) (h₀ : (T.up.row u.2 i₀).2.length ≤ R) :
      let w := (T.up.row u.2 i₀).2
      ∀ y : Site f, y ∈ (visits u.1 w.walk).toFinset → separation i (S.ratio.parent y) ≤ R := fun y hy => by
        rw [← hu]; exact (chart_in _ _ _ hy).trans h₀
  let Y0 := replica S.ratio V
  have htips (u : Cell f) (hu : S.ratio.parent u.1=i) := hvalues.face u (by rw [hu]; simp; have := hD 0; omega)
  constructor
  · intro u hx
    have htoll : toll U u ≤ fiery G x S.patch.L := by rw [hL']; exact (hE0 u (by rw [hx]; simp)).trans (show t/2≤t by linarith)
    have hk : PathData.kept T.high (fiery G x S.patch.L) u.1 U := by
      intro p; rw [hL']; by_contra! hp
      have h := h1.dropped U u.1 p hp; rw [hx] at h
      have hl := hE0 p (h.trans (Nat.div_le_self _ _))
      have hi : 0<T.high.relaxation := T.high.radius_pos
      have hw : 1≤Real.exp (separation u.1 p.1/T.high.relaxation : ℝ) := Real.one_le_exp (by positivity)
      have ht : t≤t*_ := le_mul_of_one_le_right hz.le hw
      unfold toll at hl; change _ < _ at hp; unfold t at *; linarith only [ht,hl,hp,hz]
    have hM' (j : Bool) : ‖T.Mv R (temp x) V (u,j)‖ ≤ B*v := by
      apply (h2.phi (u,j)).trans
      rw [hL']
      have h0 : (1:ℝ) ≤ (L.val:ℝ) := by exact_mod_cast L.property
      have hw := (div_le_self hA.le (one_le_pow₀ h0 (n:=2))).trans hb
      exact mul_le_mul hw hv0 hz.le hQ.le
    have hperm p (h : separation i (S.ratio.parent (p : Cell f).1)+1 ≤ thin x) :
        ‖firstFace Y0 a p‖ ≤ B*v ∧ ‖G.curvature (faceValue U p)-firstFace Y0 a p‖ ≤ B*v^2 :=
      ⟨((hvalues.face p h).2.1).trans (mul_le_mul_of_nonneg_right hv hv1.le),
        ((hvalues.face p h).2.2).trans (mul_le_mul_of_nonneg_right hv (sq_nonneg v))⟩
    obtain ⟨hp,hA'⟩ := fine_squares T hP R (fiery G x S.patch.L) (temp x) V U Y0 a u htoll hk B v hQ hv1.le hM'
      (hperm u (by rw [hx]; simp; have := hD 0; omega)) (fun k he => by
        intro w p; have hk := hslot u hx k he
        have hl := hperm p (show _ +1 ≤ _ from (Nat.add_le_add_right (hk _ (slot_based ..)) 1).trans (hD 0))
        exact ⟨fun y hy => hvalues.links y ((hk y.1 hy).trans (by have := hD 0; omega)),hl⟩)
    refine ⟨hp,(neg_le_neg (le_trans ?_ (hl0 x))).trans hA'⟩
    -- R & cost conversion
    rw [hT.high]; unfold bill
    have hh1 : (R:ℝ) ≤ b x := le_trans (Nat.cast_le.mpr (show R≤radiusB x from Nat.div_le_self ..))
      (by unfold b; linarith)
    have hG := G.colorScale_pos
    have hB1 : 1≤b x := Scales.size x
    have hh2 := mul_le_mul_of_nonneg_left hh1 (show 0≤2*G.colorScale by positivity)
    have hP1 : 1+2*G.colorScale*R ≤ N*(b x) := by
      have hh3 := mul_le_mul_of_nonneg_right (show 2*G.colorScale+1≤N from le_max_left ..) (show 0≤b x by linarith)
      linarith only [hh2,hB1,hh3]
    change 4*(m*B)^2*(1+2*G.colorScale*R)*v^3 ≤ Y * b x * v^3
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hv1.le _)
    apply (mul_le_mul_of_nonneg_left hP1 (show 0≤4*(m*B)^2 by positivity)).trans
    unfold Y; nlinarith only [show 0≤4*B^2*b x by positivity]
  · intro p hp
    have hC0 := h3.middle p (hK0 p (by simp only [hp,separation_self,Nat.zero_le]))
    obtain ⟨y,hV,hU⟩ := hvalues.sees
    have hZ : 3*till x+4+predReach S.patch ≤ thin x := by rw [hD']; unfold thin till; omega
    rw [← hp] at hV hU
    have hh (j : Bool) := h c f S T hD' hT k R (thin x) hZ U V v hv1.le hf (p,j) y hU hV
    have hh2 p : ‖T.vision (till x) (temp x) V p‖ ≤ A0*t := by have hp := h2.up p; rw [hL'] at hp; exact hp
    have ht' := mul_nonneg hA.le hz.le
    refine (neg_le_neg (he0 x)).trans ((le_trans ?_ (add_le_add hC0 (workLD_lower (till x) U V (S.prediction U k) p A0 C t (temp x) v
      (widen R v τ) ht' hh2 (fun i => ⟨(hh i).1,(hh i).2 _ _ ht' hh2⟩)))))
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (temp_nonneg _) hθ 4) hJ.le
    unfold e weakLoss v s R t at *; linarith only [hp]
  · intro p hp
    obtain ⟨-, -,-, hb1,hb2,hb3⟩ := hvalues.noise _ hp
    have ht (i) : E*v^i ≤ B*v^i := mul_le_mul_of_nonneg_right hv (pow_nonneg hv1.le (i:ℕ))
    have he := mul_le_mul_of_nonneg_right hv hv1.le
    have hB' : ‖T.Mw R (temp x) V p‖ ≤ B*v := by
      apply (h2.hot _).trans; rw [hL']; exact mul_le_mul hb hv0 hz.le hQ.le
    apply le_trans ?_ (bond_square T (till x) (temp x) V U Y0 a k p B v hQ hv1.le hB' ⟨hb1.trans (ht 2),hb2.trans he,hb3.trans he⟩)
    apply neg_le_neg (le_trans ?_ (hl0 x))
    unfold bill
    have H : 4*B^2 ≤ Y := le_add_of_nonneg_left (by positivity)
    have hh : Y ≤ Y*b x := le_mul_of_one_le_right hY (Scales.size _)
    exact mul_le_mul_of_nonneg_right (H.trans hh) (pow_nonneg hv1.le _)
  · intro q hq
    refine ⟨(htips q hq).1,fun i ht => ?_⟩
    exact (hvalues.face _ ((Nat.add_le_add_right (hslot q hq i ht _ (slot_based ..)) 1).trans (hD 0))).1
  intro p hp; obtain ⟨ha,hb,hc,-⟩ := hvalues.noise _ hp
  exact ⟨ha,hb,hc⟩
end YM.SectorNext.Remainder.Affine
