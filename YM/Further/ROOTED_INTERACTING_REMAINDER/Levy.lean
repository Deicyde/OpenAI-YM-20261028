import YM.Further.ROOTED_INTERACTING_REMAINDER.Fades
/-!
# Quantitative improvement: leave quadratic tails alive outside the Assessment

etc.

At the TRUE `SectorMeasure` leftOver on intact
profiles we can do rather better than integrating just the default mask
indicators.

Key observation: the coarse sieve itself can **pay for the
shifts** of all squares.

Only store's limit/intern
lose the pivots – charge radiusB^4 per seed through the same Teller gates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.RootedInteractingRemainder.Levy
open Filter Function Lattice RG RG.Patch Axial Wilson Finset Precision Tree Exterior Bloch Laurent
open Pressure Pressure.Stores Pressure.Teller Pressure.Tube Bid Next.Fluctuations
open Next.Fluctuations.Sector Push.SectorMeasure Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}

def coarse (T : Tube G S) (x : ℝ) (V : Config G c) :=
    ∑ i, crown T.down T.low (till x) S.patch.L.val (temp x) V i

def pulley (A : Clip) := 2 + A.direct / A.linear

lemma pulley_pos (A : Clip) : 0<pulley A := by unfold pulley; have := A.quadratic_pos; have := A.tail_pos; positivity

lemma cozy (T : Tube G S) (x : ℝ) (V : Config G c) (i : Cell c) :
    0 ≤ crown T.down T.low (till x) S.patch.L.val (temp x) V i := by
  unfold crown; apply add_nonneg
  · unfold trunk; split <;> positivity
  · unfold PathData.clipped; have := T.low.tail_pos; have := Push.SectorMeasure.temp_nonneg x; have := G.chord_nonneg (faceValue V i); have := T.low.quadratic_pos; split <;> positivity
lemma coarse_nn (T : Tube G S) (x : ℝ) (V : Config G c) : 0 ≤ coarse T x V := sum_nonneg fun _ _ => cozy ..

private lemma scales (T : Tube G S) (x : ℝ) (V : Config G c) :
    ∑ i, ‖T.vision (till x) (temp x) V i‖^2 ≤ pulley T.low * coarse T x V := by
  unfold coarse; rw [Finset.mul_sum]
  -- break rows into each plaquette
  unfold Twin; rw [Fintype.sum_prod_type]
  apply sum_le_sum; intro i _
  rw [Fintype.sum_bool]
  let r := toll V i
  have hr : 0 ≤ r := G.chord_nonneg _
  let a := temp x
  have ha : 0≤a := Push.SectorMeasure.temp_nonneg _
  have h : 2≤pulley T.low := le_add_of_nonneg_right (div_nonneg T.low.quadratic_pos.le T.low.tail_pos.le)
  let z := trunk T.down T.low (till x) S.patch.L.val (temp x) V i
  have hz : 0≤z := by unfold z trunk; split <;> positivity
  have he : ‖T.vision (till x) a V (i,true)‖^2 ≤ pulley T.low*z := by
    apply le_trans (b:=2*z) _ (mul_le_mul_of_nonneg_right h hz)
    refine le_of_eq ?_
    unfold z trunk Tube.vision thinned; simp only [↓reduceIte,a]; split
    · ring
    simp
  let f := Pressure.shoot T.low V i
  let d := T.low.direct
  have hd : 0<d := T.low.quadratic_pos
  have hQ : ‖f‖ ≤ Real.sqrt d * r := by
    unfold f Pressure.shoot; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (G.curvature_norm _) (Real.sqrt_nonneg _)
  let cP := PathData.clipped T.low a r
  have hi : ‖T.vision (till x) a V (i,false)‖^2 ≤ pulley T.low*cP := by
    unfold Tube.vision thinned; simp only [Bool.false_eq_true,↓reduceIte]; change ‖(if r=0 then (1:ℝ) else min 1 (a/r)) • f‖^2 ≤ _
    have HH (s : ℝ) (hs : 0 ≤ s) : ‖s • f‖^2 ≤ d*(s*r)^2 := calc
      _ ≤ (s*(Real.sqrt d*r))^2 := by rw [norm_smul,Real.norm_of_nonneg hs]; exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hQ hs) _
      _ = _ := by rw [mul_pow, mul_pow,Real.sq_sqrt hd.le]; ring
    rcases le_or_gt r a with h1|h2
    · have hx : (if r=0 then (1:ℝ) else min 1 (a/r))=1 := by
        split; rfl
        next hm => rw [min_eq_left ((one_le_div (hr.lt_of_ne' hm)).2 h1)]
      have h3 : (0:ℝ)≤d*r^2/2 := by positivity
      rw [hx]; apply (HH 1 zero_le_one).trans
      unfold cP PathData.clipped; rw [if_pos h1,one_mul]
      linarith only [mul_le_mul_of_nonneg_right h h3]
    have h0r := ha.trans_lt h2
    rw [if_neg h0r.ne',min_eq_right ((div_le_one h0r).mpr h2.le)]
    apply (HH _ (div_nonneg ha hr)).trans
    unfold cP PathData.clipped; rw [if_neg (by linarith),div_mul_cancel₀ _ h0r.ne']
    unfold pulley
    let b := T.low.linear
    have hb : 0<b := T.low.tail_pos
    change d*a^2 ≤ (2+d/b)*(b*a*r)
    calc
      _ ≤ d*a*r := by nlinarith only [mul_le_mul_of_nonneg_left h2.le (mul_nonneg hd.le ha)]
      _ = d/b*(b*a*r) := by field_simp
      _ ≤ _ := by gcongr; linarith only
  unfold crown; change _ ≤ pulley _*(z+cP)
  rw [mul_add]
  linarith only [he,hi]

-- Schur on the actual zip. One coefficient from each of the two sides
-- of the Allowance budget–L^{+-2} factors cancel, even with orientations.
private lemma second {ι J : Type*} [Fintype ι] [Fintype J] (g : ι→J→Pay G) (v : J → G.Color)
    {C D : ℝ} (hC : 0≤C) (hD : 0≤D) (h : ∀ i,∑ j,‖g i j‖ ≤ C) (he : ∀ j,∑ i,‖g i j‖ ≤ D) :
    ∑ i, ‖zip g v i‖^2 ≤ C*D * ∑ j, ‖v j‖^2 := by
  let s (i j) := ‖g i j‖
  let b j := ‖v j‖^2
  have hs (i j) : 0≤s i j := norm_nonneg _
  have hb j : 0≤b j := sq_nonneg _
  calc
    _ ≤ ∑ i,C*∑ j,s i j*b j := sum_le_sum fun i _ => by
      calc
        _ ≤ (∑ j,s i j * ‖v j‖)^2 := by
          unfold zip; refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le ..).trans ?_) 2
          exact sum_le_sum fun j _=> (g i j).le_opNorm _
        _ ≤ (∑ j,s i j)*∑ j,s i j*b j := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j hj=>hs i j)
          (fun j _=>mul_nonneg (hs ..) (hb _)) (fun j _ => (by unfold b; rw [mul_pow,pow_two (s i j)]; linarith))
        _ ≤ _ := mul_le_mul_of_nonneg_right (h i) (sum_nonneg fun j _=> mul_nonneg (hs ..) (hb _))
    _ ≤ _ := by
      rw [← Finset.mul_sum,mul_assoc,Finset.sum_comm,Finset.mul_sum _ _ D]
      simp_rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ hC
      exact sum_le_sum fun i _=> mul_le_mul_of_nonneg_right (he i) (hb i)

lemma shiftsF (T : Tube G S) (x : ℝ) (V : Config G c) {b : ℝ} (h : 0≤b) (H : Allowance b T x V) :
    (∑ i, ‖T.Mv (till x) (temp x) V i‖^2) ≤ b^2*pulley T.low*coarse T x V := by
  apply le_trans (second _ (T.vision (till x) (temp x) V) (by positivity : 0≤b/(S.patch.L.val:ℝ)^2)
    (by positivity : 0≤b*(S.patch.L.val:ℝ)^2) H.wide.rows H.wide.columns)
  have hL : 0 < (S.patch.L.val:ℝ) := by exact_mod_cast S.patch.L.property
  rw [show b/(S.patch.L.val:ℝ)^2*(b*(S.patch.L.val:ℝ)^2)=b^2 by field_simp,mul_assoc]
  exact mul_le_mul_of_nonneg_left (scales ..) (sq_nonneg _)
lemma shiftsI (T : Tube G S) (x : ℝ) (V : Config G c) {b : ℝ} (h : 0≤b) (H : Allowance b T x V) :
    (∑ i, ‖T.Mw (till x) (temp x) V i‖^2) ≤ b^2*pulley T.low*coarse T x V := by
  rw [pow_two (b),mul_assoc (b*b)]
  apply (second _ _ h h H.narrow.rows H.narrow.columns).trans
  exact mul_le_mul_of_nonneg_left (scales ..) (mul_nonneg h h)

/-- Those link costs whose pivots we'll keep. -/
def coin (A : Stores S) (x : ℝ) (U : Config G f) (Q V : Config G c) :=
  (∑ i∈(A.limit x)ᶜ,(toll U i)^2)+(∑ i∈(A.intern x)ᶜ,(wire Q V i)^2)
lemma coin_nn (A : Stores S) (x : ℝ) (U : Config G f) (Q V : Config G c) : 0≤ coin A x U Q V := by
  exact add_nonneg (sum_nonneg fun i _ => sq_nonneg _) (sum_nonneg fun i _ => sq_nonneg _)

/-- Pay half the sieve to hold the shifts on the full incoming rows.
ζ chosen independently of W and period. rho represented by b; allow C
larger in defect estimate. -/
private lemma leaving (C D b τ h : ℝ) (x W : ℝ) {η ζ : ℝ} (hζ : 0≤ζ) (hη : 0≤η) (hζ1 : ζ ≤ 1) (hb : 0 ≤ b)
    (o : Stores S) {T : Tube G S} {U : Config G f} (V : Config G c) (k : S.Choices) (hz : Seeded o U k V x W)
    (hc : 0≤C) (hd : 0≤D) (hh : 0≤h) (hA : Allowance b T x V)
    (h₁ : η ≤ ζ*T.high.direct/4) (h₂ : η≤ζ*S.kernel.penalty/4)
    (hHole : ζ*(b^2*pulley T.low) ≤ (1:ℝ)/2)
    (hl : LaneCounts T.up x (fiery G x S.patch.L) T.high D 1 S.ratio.parent)
    (hM : Maximum D T x V)
    (hC : ∀ i : Cell c,i∉o.outs x → -(C*temp x^4) ≤ T.workC (till x) V (temp x) i)
    (hLD : ∀ i : Cell c,i∉o.outs x → ∀ v : Bool,
      ‖lGap T (till x) U (S.prediction U k) V (i,v)‖ ≤ C*h*widen (till x) h τ ∧
      ‖dGap T (till x) V (T.vision (till x) (temp x) V) (i,v)‖ ≤ C*(D*(fiery G x S.patch.L))*widen (till x) h τ) :
    η*coin o x U (S.prediction U k) V - ((Fintype.card (Cell c):ℝ)*fade (fiery G x S.patch.L) h (temp x) (till x) D C τ) ≤
      unassigned o T x U k V + coarse T x V / 2 := by
  let R := till x; let s := temp x; let t := fiery G x S.patch.L; let Q := S.prediction U k
  let l := fade t h s R D C τ
  have ht : 0≤t := Push.SectorMeasure.temp_nonneg _
  have hs : 0≤s := Push.SectorMeasure.temp_nonneg _
  have he : 0 ≤ widen R h τ := widen_nonneg _ hh
  have hh' : 0 ≤ l := by unfold l fade; positivity
  have hout : ∀ i∈(o.outs x)ᶜ, -l ≤ T.workC R V s i + (T.workL R U Q V s i + T.workD R V s i) := by
    intro i hi
    have hx : i ∉ o.outs x := mem_compl.mp hi
    have hr := hC i hx
    have hp := toll_LD (D*t) C h (widen R h τ) (by positivity) T R s U Q V i (fun v => hM.up _) (hLD i hx)
    unfold l fade; linarith only [hr,hp]
  let X := coarse T x V
  let β := b^2*pulley T.low
  have hcS : -((Fintype.card (Cell c):ℝ)*l) ≤ ∑ i∈(o.outs x)ᶜ,(T.workC R V s i + (T.workL R U Q V s i + T.workD R V s i)) := by
    have he : (((o.outs x)ᶜ.card):ℝ) ≤ Fintype.card (Cell c) := by exact_mod_cast card_le_univ _
    calc
      _ ≤ (((o.outs x)ᶜ.card):ℝ)*(-l) := by rw [mul_neg]; exact neg_le_neg (mul_le_mul_of_nonneg_right he hh')
      _ = ∑ i∈(o.outs x)ᶜ, -l := by rw [sum_const,nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hout
  have hw {ι : Type} [Fintype ι] (w u X : ι→ℝ) (d : ℝ) (I : Finset ι)
      (h : ∀ i∈I,(Real.sqrt d*u i - w i)^2/2 ≤ X i) (hd : 0≤d) (hη : η≤ζ*d/4) (L : ℝ) (hZ : ∑ i,w i^2 ≤ L) :
      η* (∑ i∈I,u i^2) ≤ (∑ i∈I,X i) + (ζ/2)*L := by
    have hf (i) (hi:i∈I) : η*u i^2 ≤ X i + ζ/2*w i^2 := by
      have hh := h i hi
      have hx : (Real.sqrt d*u i)^2=d*u i^2 := by rw [mul_pow,Real.sq_sqrt hd]
      have he : d*u i^2/4-w i^2/2 ≤ (Real.sqrt d*u i - w i)^2/2 := by
        nlinarith only [hx,sq_nonneg (Real.sqrt d*u i/2 - w i)]
      have ha : 0≤X i := (by positivity : 0 ≤ (Real.sqrt d*u i - w i)^2/2).trans hh
      have hp := mul_le_mul_of_nonneg_left (he.trans hh) hζ
      linarith only [hp, mul_le_of_le_one_left ha hζ1,mul_le_mul_of_nonneg_right hη (sq_nonneg (u i))]
    rw [Finset.mul_sum]
    apply le_trans (sum_le_sum hf)
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ ζ/2)) _
    exact le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => sq_nonneg _) hZ
  have hZ := shiftsF T x V hb hA
  have hL : (∑ i : Cell f,‖T.Mv R s V (i,false)‖^2) ≤ b^2*pulley T.low*X := by
    unfold Twin at hZ; rw [Fintype.sum_prod_type] at hZ
    refine le_trans (sum_le_sum fun i _ => ?_) hZ
    exact single_le_sum (f:=fun j => ‖T.Mv R s V (i,j)‖^2) (fun i _ => sq_nonneg _) (mem_univ _)
  have hfS := hw _ _ _ T.high.direct (o.limit x)ᶜ (fun i hi=>fine_retained T i hz (mem_compl.mp hi) hl)
    T.high.quadratic_pos.le h₁ (β*X) hL
  have hiS := hw _ _ _ S.kernel.penalty (o.intern x)ᶜ (fun i _=> bond_retained T V Q i x)
    S.kernel.penalty_pos.le h₂ (β*X) (shiftsI T x V hb hA)
  have hnS : 0 ≤ ∑ i∈(o.coordN x)ᶜ,T.workN R V s i := sum_nonneg fun i _=>by unfold Tube.workN; positivity
  have hy := mul_le_mul_of_nonneg_right hHole (coarse_nn T x V)
  unfold coin unassigned assessed tally talli tallc talln talll; dsimp only
  -- rewrite RHS carefully (will match LHS terms?) sum_add_sum_compl matches full univ only
  rw [← sum_add_sum_compl (o.limit x),←sum_add_sum_compl (o.intern x),←sum_add_sum_compl (o.outs x),
    ←sum_add_sum_compl (o.coordN x),←sum_add_sum_compl (o.outs x),←sum_add_sum_compl (o.outs x),sum_add_distrib]
  rw [sum_add_distrib,sum_add_distrib] at hcS
  -- names Q etc
  change η*(∑ i∈(o.limit x)ᶜ,toll U i ^2) ≤ (∑ i∈(o.limit x)ᶜ,T.workF R U V t s i)+_*_ at hfS
  dsimp only [R,t,s,Q,β,X,l] at hcS hfS hiS hnS
  linarith only [hcS,hfS,hiS,hnS,hy]

private lemma alone_store (A : Stores S) : turnStore 1 A=A := by
  have h {ι : Type} [Fintype ι] [DecidableEq ι] (e : Equiv.Perm ι) (h : ∀ i,e i=i) (z : Finset ι) : z.map e.symm.toEmbedding=z := by
    have he : e=Equiv.refl _ := by ext i; exact h i
    rw [he]; ext; simp
  have ha := h (Oriented.faces 1 f) (fun i => by
    rcases i with ⟨a,⟨⟨x,y⟩,hi⟩⟩
    change x<y at hi
    change Face.send 1 0 _ = _
    simp [Face.send,Face.lower,atFace,affine,PlaqAxes.rotate,PlaqAxes.ordered,posDir,hi.le]) A.costs
  have hb := h (StepData.sendBonds (c:=c) 1 0) (fun i => by
    change sendEdge 1 0 i=i
    simp [sendEdge,Step.used,affine,posDir]) A.aisles
  have hc := h (StepData.sendSites 1 (0:Site c)) (fun i => by
    change affine 1 0 i=i; simp [affine]) A.flags
  obtain ⟨i,j,k⟩ := A; simp only [turnStore,ha,hb,hc]

private lemma still_turn (U : Config G f) : pull 1 0 U=U := by rw [pull_one]; funext; simp [translate]

-- keep just one (positive weighted) orientation tail
private lemma communal (P : Teller G) {T : Tube G S} (hP : P.Funds S T) (D ε : ℝ) (hD : 0<D)
    (H : ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
        SliceSet S F U → Alive S U k → Seeded A U k V x W →
          D*coin A x U (S.prediction U k) V-ε ≤ unassigned A T x U k V+coarse T x V/2)
    (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c)
    (hU : SliceSet S F U) (hk : Alive S U k) (hV : Seeded A U k V x W) :
    D/(Fintype.card Signed:ℝ)*coin A x U (S.prediction U k) V-ε ≤
      meanRest A T x U k V + averaged (fun j => coarse T x (pull j 0 V))/2 := by
  let J := fun j : Signed => coin (turnStore j A) x (pull j 0 U) (S.prediction (pull j 0 U) (choice j k)) (pull j 0 V)
  let K := fun j : Signed=> coarse T x (pull j 0 V)
  have hX (j : Signed) : D*(J j)-ε ≤ unassigned (turnStore j A) T x (pull j 0 U) (choice j k) (pull j 0 V) + K j/2 := by
    refine H _ _ _ _ _ (turn_sliced j F U hU) ?_ (pull_seeded j (funds_branch hP) hV)
    unfold Alive; rw [(carry j (funds_branch hP) k U).1]; exact hk
  have hh : J 1=coin A x U (S.prediction U k) V := by
    have he := (carry 1 (funds_branch hP) k U).2
    dsimp only [J]; rw [he,still_turn,still_turn,still_turn,alone_store]
  have he := av_mono hX
  let b := (Fintype.card Signed:ℝ)
  have hx : averaged (fun j=> D*J j - ε)= b⁻¹*(∑ j,D*J j)-ε := by
    rw [av_sub _ (fun _=>ε),av_const]; rfl
  rw [hx,av_add _ (fun j=>K j / 2),← meanRest] at he
  apply le_trans _ (he.trans_eq ?_)
  · rw [←hh];
    have hh := single_le_sum (f:=fun i => D*J i) (fun i _ => mul_nonneg hD.le (coin_nn ..)) (mem_univ 1)
    change D/b*J 1-ε≤_
    rw [div_eq_mul_inv]
    have hv : 0 ≤ b⁻¹ := by unfold b; positivity
    linarith only [mul_le_mul_of_nonneg_left hh hv]
  unfold averaged K; rw [←sum_div]; ring

/-- The levy is real, earmarked before size L. `crown` here is the same price
as in `sieve`. The x-delay error is per coarse site.
-/
theorem branch (P : Teller G) (ε : ℝ) (hε : 0<ε) : ∃ η : ℝ,0<η ∧ ∀ L : Side, ∀ W : ℝ,0<W → ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f), S.patch.L=L → 100*(1+radiusB x) ≤ c.val →
      ∀ (T : Tube G S), P.Funds S T →
      ∀ (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c),
        SliceSet S F U → Alive S U k → Seeded A U k V x W →
        ∀ β : ℝ,0≤β → β≤2*betaF G x L →
          β*(η*coin A x U (S.prediction U k) V) - ε*Fintype.card (Site c) ≤
          β*(meanRest A T x U k V + averaged (fun j=>coarse T x (pull j 0 V))/2) := by
  obtain ⟨b,hb,Hb⟩ := Work.E03.answer P
  obtain ⟨D,hD,HD⟩ := Work.E04.answer Work.E03.answer P
  obtain ⟨δ,hδ,B,hB,HB⟩ := Work.E05.answer P
  let q := b^2*pulley P.below.clip
  have hq : 0<q := mul_pos (by positivity) (pulley_pos _)
  let ζ := min 1 ((1/2)/q)
  have hζ : 0<ζ := lt_min zero_lt_one (by positivity)
  let K := min (ζ*P.top.clip.direct/4) (ζ*P.bind.penalty/4)
  have hK : 0<K := by unfold K; exact lt_min (by have := P.top.clip.quadratic_pos; positivity) (by have := P.bind.penalty_pos; positivity)
  refine ⟨K/(Fintype.card Signed:ℝ),by have : 0<(Fintype.card Signed:ℝ) := Nat.cast_pos.mpr Fintype.card_pos; positivity,fun L W hW=>?_⟩
  obtain ⟨J,hJ,HJ⟩ := brazed P L W hW
  by_cases he : ∃ X : Patch,X.L=L ∧ X.J=P.j ∧ X.Branches P.bind G
  swap
  · filter_upwards with x c f S hL _ T h
    exact False.elim (he ⟨S.patch,hL,h.atStep,h.kernel⟩)
  obtain ⟨X,hL,hX,he⟩ := he
  obtain ⟨E,τ,r,hE,hτ,hr,H⟩ := interior_cost P X he
  let C := max B E
  have hC : 0<C := hB.trans_le (le_max_left ..)
  have HT : Tendsto (stitchCost G L J) atTop (𝓝 0) := by convert radius_stitch G L J 0 using 2; simp
  let g := fun x=>stitchCost G L J x
  let t := fun x=>fiery G x L
  let Y : ℝ := Fintype.card PlaqAxes
  let p := fun x=>fade (t x) (g x) (temp x) (till x) D C τ
  have hPC : Tendsto (fun x=>Y*((2*betaF G x L)*p x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (fade_small (G:=G) (L:=L) D C J τ hD hC hJ hτ).const_mul Y
  filter_upwards [HT.eventually (ge_mem_nhds hr),HJ,(HB L W).late,(HD L W).late,(Hb L W).late,
    (Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0),Work.E08.eventual_radiusB (100*(predReach X+10)),hPC.eventually (ge_mem_nhds hε)] with x hx hj hbb hd ha hz hh hε
  intro c f S hm hs T hP F A U k V hU hk hV β hβ hR
  have hSp : S.patch=X := patch_same (hm.trans hL.symm) (hP.atStep.trans hX.symm)
  have hf : 0≤t x := Push.SectorMeasure.temp_nonneg _
  have hg : 0≤g x := by unfold g stitchCost largeT; positivity
  have hv : 0≤widen (till x) (g x) τ := widen_nonneg _ hg
  have hp : 0≤p x := by unfold p fade; have := Push.SectorMeasure.temp_nonneg x; positivity
  let ε := (Fintype.card (Cell c):ℝ)*p x -- shadow epsilon!
  have hq (F : Forest S.ratio) (A : Stores S) (U : Config G f) (k : S.Choices) (V : Config G c)
      (hU : SliceSet S F U) (hk : Alive S U k) (hV : Seeded A U k V x W) :
      K*coin A x U (S.prediction U k) V-ε ≤ unassigned A T x U k V+coarse T x V/2 := by
    have hl := hd c f S hm hs T hP F A U k V hU (hV.plot hk)
    rw [←hm] at hl
    have hCov := hbb c f S hm hs T hP F A U k V hU (hV.plot hk)
    have hAllow := ha c f S hm hs T hP F A U k V hU (hV.plot hk)
    dsimp only [ε,p,t]; rw [←hm]
    refine leaving C D b τ (g x) x W (η:=K) hζ.le hK.le (min_le_left ..) hb.le A V k hV hC.le hD.le hg hAllow ?_ ?_ ?_ hl.1 hl.2.2 ?_ ?_
    · rw [hP.high]; exact min_le_left ..
    · rw [hP.knobs]; exact min_le_right ..
    · rw [hP.low]; exact (le_div_iff₀ hq).mp (min_le_right ..)
    · intro i hi
      have he : Beyond A x i.1 := fun hh=>hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
      apply le_trans _ (hCov.middle i (outMargin hV he (by simp)))
      exact neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
    intro i hi v
    have he : Beyond A x i.1 := fun hh=>hi (mem_filter.mpr ⟨mem_univ _,hh⟩)
    obtain ⟨z,h1,h2⟩ := hj c f S hm hs T hP F A U k V hU hk hV i.1 he
    have hR : 3*till x+4+predReach S.patch ≤ 2*radiusB x/5 := by rw [hSp]; unfold till; omega
    obtain ⟨ha,hi⟩ := H c f S T hSp hP k (till x) _ hR U V (g x) hg hx (i,v) z h2 h1
    rw [hm]
    have hw (j) : ‖T.vision (till x) (temp x) V j‖ ≤ D * fiery G x L := hm ▸ hl.2.2.up j
    have hp := hi _ (D*(t x)) (by positivity) hw
    exact ⟨ha.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) hg) hv),
      hp.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity : 0≤D*(t x))) hv)⟩
  have hh := communal (x:=x) P hP K ε hK hq F A U k V hU hk hV
  have he := mul_le_mul_of_nonneg_right hε (a:=(Fintype.card (Site c):ℝ)) (by positivity)
  have hS' := mul_le_mul_of_nonneg_right hR (mul_nonneg (Nat.cast_nonneg (Fintype.card (Cell c))) hp)
  have hfC : (Fintype.card (Cell c):ℝ)=Fintype.card (Site c)*Y := by simp [Y,Cell,Site,Face]
  unfold ε at hh; rw [hfC] at hh hS'
  change (_:ℝ)*_ ≤ _ at hε
  linarith only [he,hS',mul_le_mul_of_nonneg_left hh hβ]

end YM.Further.RootedInteractingRemainder.Levy
