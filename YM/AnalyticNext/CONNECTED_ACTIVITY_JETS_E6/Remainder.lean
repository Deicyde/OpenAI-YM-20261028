import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.PatchCap

/-!
# Weak annulus F/I true costs and remote Mayer germs (values)

Use natural vector residuals and chart tests about the measured U. Permits
large poly powers later; fixed rates. No payment from hessian or Taylor-jet
estimates of an integrated function. Raw compulsory still on its core masks.
One direction channel at a time with actual predictor. `soft` agrees with
`workF` even at threshold equality whenever the stencil is accepted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent Bid
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

abbrev bill (T : Tube G S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) (p : Rod c f) :=
    entryCost T (till x) U k V p-guide T x V p

def flaw (u : G.El) : ℝ := (G.chord u^2-‖G.curvature u‖^2)/2

lemma flaw_nonneg (u : G.El) : 0 ≤ flaw u :=
    div_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm _) 2)) (by norm_num)

lemma crown_split {x : ℝ} (T : Tube G S) (U : Config G f) (p : Cell f)
    (hv : toll U p ≤ Pressure.fiery G x S.patch.L) (hg : PathData.kept T.high (Pressure.fiery G x S.patch.L) p.1 U) :
    crown T.up T.high (till x) 1 (Pressure.fiery G x S.patch.L) U p=
      T.high.direct*flaw (faceValue U p)+∑ i : Bool, ‖entryCost T (till x) U (Classical.arbitrary _) 1 (.inl (p,i))‖^2/2 := by
  unfold crown trunk PathData.clipped; rw [if_pos (show G.chord _ ≤ _ from hv), if_pos hg,Fintype.sum_bool]
  dsimp only [flaw,entryCost,Tube.Xf,Sum.elim,plotted]; rw [if_pos (by simp),if_neg (by simp)]
  unfold shoot; rw [norm_smul,mul_pow,Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt T.high.quadratic_pos.le]; ring

/-- Algebraic good version for F, with k a dummy index *on that same
choice list* (fine Xf data not depending k in this grammar). -/
def soft (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) (p : Cell f) :=
    T.high.direct*flaw (faceValue U p)+∑ i : Bool, ‖bill T x U k V (.inl (p,i))‖^2/2

theorem splitF (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) (p : Cell f)
    (hv : toll U p ≤ Pressure.fiery G x S.patch.L) (hg : PathData.kept T.high (Pressure.fiery G x S.patch.L) p.1 U) :
      T.workF (till x) U V (Pressure.fiery G x S.patch.L) (Pressure.temp x) p=soft T x U V k p := by
  unfold Tube.workF soft; rw [crown_split T U p hv hg, add_assoc, ← Finset.sum_add_distrib]
  apply congr_arg _; refine Finset.sum_congr rfl fun i _ => ?_
  change _+_=‖T.Xf (till x) U (p,i)-T.Mv (till x) (Pressure.temp x) V (p,i)‖^2/2
  dsimp only [entryCost,guide, Sum.elim]; rw [norm_sub_sq_real, real_inner_comm]
  ring

abbrev softI (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) (p : Bond c) :=
    S.kernel.penalty*flaw (V p*(S.prediction U k p)⁻¹)+‖bill T x U k V (.inr p)‖^2/2

theorem splitI (T : Tube G S) (x : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) (p : Bond c) :
      T.workI (till x) (S.prediction U k) V (Pressure.temp x) p=softI T x U V k p := by
  unfold Tube.workI monetary softI flaw bill entryCost guide; rw [norm_sub_sq_real,real_inner_comm]
  unfold Z; simp only [Sum.elim]; rw [norm_smul,mul_pow,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt S.kernel.penalty_pos.le]
  unfold wire; ring

lemma sqrt_compare {K α : ℝ} (hK : 0 < K) (_hα : 0 ≤ α) (w : G.El)
    (hc : 3/4 * G.chord w^2 ≤ ‖G.curvature w‖^2)
    (he : ‖Real.sqrt K • G.curvature w‖ ≤ α) : G.chord w ≤ (2 / Real.sqrt K)*α := by
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at he
  have hq : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  have hi : G.chord w ≤ 2*‖G.curvature w‖ := by nlinarith [G.chord_nonneg w,norm_nonneg (G.curvature w)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hq]
  nlinarith only [mul_le_mul_of_nonneg_right hi hq.le,he]

lemma flaw_bound {K A : ℝ} (hK : 0 ≤ K) {w : G.El} (hs : G.chord w^2-K*G.chord w^4 ≤ ‖G.curvature w‖^2)
    (he : G.chord w ≤ A) : |flaw w| ≤ (K/2)*A^4 := by
  rw [abs_of_nonneg (flaw_nonneg w)]; unfold flaw
  nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (G.chord_nonneg _) he 4) hK,hs]

abbrev request (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) (p : Rod c f) :=
    baseStroke T x k V p - guide T x V p

/-- Vector used in the actual subtracted affine square. -/
def reply (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (u : Directions G f) (p : Rod c f) :=
    request T x k V p + straightened T (till x) V u p

lemma ticket_sq {v w : G.Color} {h r : ℝ} (hr : ‖v‖ ≤ h) (he : ‖v-w‖ ≤ r) :
    |‖v‖^2/2-‖w‖^2/2| ≤ r*(2*h+r)/2 := by
  have hx := abs_norm_sub_norm_le v w
  have hh := (abs_le.mp (hx.trans he)).1
  have hp : 0 ≤ r := (norm_nonneg _).trans he
  have hz := norm_nonneg w; have hk := norm_nonneg v
  rw [← sub_div, abs_div,abs_of_nonneg (by norm_num : (0:ℝ)≤2),sq_sub_sq,abs_mul,
    abs_of_nonneg (add_nonneg hk hz)]
  rw [mul_comm (‖v‖ + ‖w‖)]
  exact div_le_div_of_nonneg_right (mul_le_mul (hx.trans he) (by linarith) (add_nonneg hk hz) hp) (by norm_num)

lemma paysGuide (p : Rod c f) {A x : ℝ} (hA : 0 ≤ A) (V : Config G c) (h : Maximum A T x V) :
    ‖guide T x V p‖ ≤ A*Pressure.fiery G x S.patch.L := by
  rcases p with i|b
  · refine (h.phi i).trans ?_
    have he : (1:ℝ) ≤ (S.patch.L.val:ℝ)^2 := one_le_pow₀ (by exact_mod_cast S.patch.L.property)
    exact mul_le_mul_of_nonneg_right (div_le_self hA he) (by unfold fiery Pressure.temp; positivity)
  exact h.hot b

lemma accuracy2 {T : Tube G S} {C : ℝ} {U : Config G f} {u : Directions G f} {V : Config G c} {k : S.Choices} {x : ℝ}
    (i : Rod c f) (h : ‖entryCost T (till x) U k V i - (baseStroke T x k V i + straightened T (till x) V u i)‖ ≤ C) :
    ‖bill T x U k V i - reply T x V k u i‖ ≤ C := by
  unfold bill reply request;
  rw [show entryCost T (till x) U k V i-guide T x V i - _ = entryCost T (till x) U k V i - (baseStroke T x k V i+straightened T (till x) V u i) by abel]; exact h

/-- With room in the cost even when a flat-stencil budget was already
spent at RScene. Neither Plot nor stationarity assumptions buy this
affine remainder: use the actual (possibly previously frozen) V,U
close on the patch explicitly. -/
lemma soft_bills (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (A : ℝ) (hA : 0<A)
    {w : ℝ → ℝ} (h : Rate G L (-(1/2)) w) (hp : ∀ᶠ x in atTop, 0 ≤ w x) :
    ∃ F, Rate G L (-(3/2)) F ∧
      ∀ᶠ x : ℝ in atTop, 0 ≤ F x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch=D →
      S.patch.L=L → Room P S T x → ∀ (U : Config G f) (k : S.Choices) (V : Config G c) (p : Site c) (u : Directions G f),
        Maximum A T x V → Clean V x p (radiusB x) → Grafted V U u p (radiusB x/2) (w x) S →
        (∀ b : Cell f, S.ratio.parent b.1=p → |soft T x U V k b-(∑ i : Bool, ‖reply T x V k u (.inl (b,i))‖^2/2)|≤F x) ∧
        ∀ b : Bond c, b.1=p → |softI T x U V k b-‖reply T x V k u (.inr b)‖^2/2|≤ F x := by
  obtain ⟨J,δ,hJ,hd,hw⟩ := Work.E05.curvature_lower G
  obtain ⟨M,E,hM,hE,H⟩ := strokes P L D hD h hp
  let a := P.top.clip.direct; let b := P.bind.penalty
  let X x := a*(J/2)*(2 / Real.sqrt a*M x)^4
  let Y x := b*(J/2)*(2 / Real.sqrt b*M x)^4
  let m x := M x + A*Pressure.fiery G x L
  let Z x := E x*(2*m x+E x)*(1/2:ℝ)
  let F x := X x+Y x+2*Z x
  have hX (v : ℝ) : Rate G L (-2) (fun x => v*(J/2)*(2/Real.sqrt v*M x)^4) := by
    convert ((hM.mul_left (2/Real.sqrt v)).pow 4).mul_left (v*(J/2)) using 1; norm_num
  have hm := hM.add (Rate.flame.mul_left A)
  have hz : Rate G L (-(3/2)) Z := by
    convert (hE.mul ((hm.mul_left 2).add (hE.weaken (by norm_num)))).mul_right (1/2:ℝ) using 1; norm_num
  refine ⟨F,((hX a |>.add (hX b)).weaken (by norm_num)).add (hz.mul_left 2),?_⟩
  filter_upwards [H,marks_here P L D hD h hp δ hd] with x hx he
  obtain ⟨hy,hz,H⟩ := hx
  have ha : 0<a := P.top.clip.quadratic_pos; have hb : 0<b := P.bind.penalty_pos
  have hf : 0 ≤ X x := by unfold X; positivity
  have hh : 0 ≤ Y x := by unfold Y; positivity
  have hn : 0 ≤ Pressure.fiery G x L := by unfold Pressure.fiery Pressure.temp; positivity
  have hr : 0 ≤ m x := by unfold m; positivity
  have hY : 0 ≤ Z x := by unfold Z; positivity
  refine ⟨(by unfold F; positivity),?_⟩
  intro c f S T hS hL hR U k V p u hV hc hu
  obtain ⟨-,hdir,hfine⟩ := he c f S T hS hL hR U k V p u hc hu
  let R i := ‖bill T x U k V i‖^2/2
  have ht i (hi : focus S i=p) : ‖entryCost T (till x) U k V i‖ ≤ M x ∧
      |R i-‖reply T x V k u i‖^2/2| ≤ Z x := by
    obtain ⟨h,hp'⟩ := H c f S T hS hL hR U k V i u (hi.symm ▸ hc) (hi.symm ▸ hu)
    have he := hR.accepted
    have hk : ‖bill T x U k V i‖ ≤ m x := (norm_sub_le ..).trans
      (add_le_add h ((paysGuide i hA.le V hV).trans_eq (by rw [hL])))
    refine ⟨h,(ticket_sq hk (accuracy2 i hp')).trans_eq ?_⟩
    unfold Z; ring
  have hz1 : T.high.direct=a := by rw [hR.accepted.high]
  have hz2 : S.kernel.penalty=b := by rw [hR.accepted.knobs]
  constructor
  · intro i hi
    have hv := hw _ (hfine i hi.symm)
    have ht0 : ‖Real.sqrt T.high.direct • G.curvature (faceValue U i)‖≤M x := (ht (.inl (i,false)) hi).1
    rw [hz1] at ht0
    have hF := mul_le_mul_of_nonneg_left (flaw_bound hJ.le hv.1 (sqrt_compare ha hy _ hv.2 ht0)) ha.le
    unfold soft
    rw [add_sub_assoc,hz1, ← Finset.sum_sub_distrib]
    apply (abs_add_le ..).trans
    rw [abs_mul,abs_of_pos ha]; change a* _ ≤ _ at hF
    have hm : |∑ i' : Bool,(R (.inl (i,i'))-‖reply T x V k u (.inl (i,i'))‖^2/2)| ≤ 2*Z x := by
      rw [Fintype.sum_bool]; apply (abs_add_le ..).trans
      exact (add_le_add (ht (.inl (i,true)) hi).2 (ht (.inl (i,false)) hi).2).trans_eq (by ring)
    apply (add_le_add hF hm).trans
    unfold F X; linarith only [hh]
  rintro ⟨q,i⟩ hq; change q=p at hq; subst q
  let j := (p,i); let u' := V j*(S.prediction U k j)⁻¹
  have Hv := hw u' (hdir i).2
  have Ht : ‖Real.sqrt S.kernel.penalty • G.curvature u'‖≤M x := (ht (.inr j) rfl).1
  rw [hz2] at Ht
  have Hb := mul_le_mul_of_nonneg_left (flaw_bound hJ.le Hv.1 (sqrt_compare hb hy _ Hv.2 Ht)) hb.le
  unfold softI; rw [hz2,add_sub_assoc]
  apply (abs_add_le ..).trans
  rw [abs_mul, abs_of_pos hb]
  apply (add_le_add Hb (ht (.inr j) rfl).2).trans
  unfold F Y; linarith only [hf,hY]
end YM.ConnectedActivityE6.SliceRows
