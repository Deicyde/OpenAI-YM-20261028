import YM.AnalyticBridge.SECTOR_AFFINE_JETS.FiniteStack
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.RowStencil
import YM.Push.FREE_RESOLVENT.Layout



/-!
# Doubly sided bills on kernel entries

Put external-coordinate-location marks on every entry, even those made
from infinite rows of cut path coefficients. No implicit period factors
from input operator norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps
open YM.Push.Uniform
open YM.FreeResolvent (Mark Bundle native)
open YM.FreeResolvent.TestD
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable {n : ℕ} {r C M σ d δ : ℝ}

section entries
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev marks (G : Gauge) (c : Side) := Mark.positions (native c) (coordRoot (G:=G))

/-- Ordered jet (left coordinate patch; not Lie derivatives). Exponential
weight paid from either entry location, and mark costs on external derivative
locations from either. This is a pre-summation budget per entry. -/
structure Pays (B : PriceCoords G c) (p q : Site c) (k : ℕ) (s d C : ℝ) (u : PriceCoords G c → E) : Prop where
  smooth : ContDiffAt ℝ ω u B
  each (z : Site c) : z=p ∨ z=q → ∀ l : List (Coord G c), l.length ≤ k →
    (marks G c d).pay l z * ((native c).weight s p q * ‖jet bolt u l B‖) ≤ C

namespace Pays
variable {B : PriceCoords G c} {p q : Site c} {u : PriceCoords G c → E}

lemma mono (hp : Pays B p q n σ d C u) (hC : C ≤ M) : Pays B p q n σ d M u :=
  ⟨hp.smooth, fun z h l hh => (hp.each z h l hh).trans hC⟩

lemma zero (hC : 0≤C) : Pays B p q n σ d C (0 : PriceCoords G c → E) := by
  refine ⟨contDiffAt_const,fun z hz l h => ?_⟩
  have he : jet bolt (0 : PriceCoords G c → E) l B=0 := by
    by_cases he : l=[]
    · subst l; rw [zeroth]; rfl
    exact jet_const bolt l he 0 B
  rw [he,norm_zero,mul_zero,mul_zero]; exact hC

lemma line (hp : Pays B p q n σ d C u) {M : ℝ} {L : E →L[ℝ] F} (h : ‖L‖ ≤ M) :
    Pays B p q n σ d (M*C) (fun x => L (u x)) := by
  refine ⟨L.contDiff.contDiffAt.comp _ hp.smooth, fun z hx l h₀ => ?_⟩
  rw [jet_linear bolt _ L (hp.smooth.of_le le_top)]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (hp.each _ hx l h₀) ((norm_nonneg _).trans h))
  rw [mul_left_comm M,mul_left_comm M ((native c).weight σ p q)]
  apply mul_le_mul_of_nonneg_left _ ((marks G c d).pay_pos ..).le
  apply mul_le_mul_of_nonneg_left _ ((native c).weight_nn ..)
  exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))

lemma scale (hp : Pays B p q n σ d C u) (a : ℝ) : Pays B p q n σ d (|a| *C) (fun y => a • u y) :=
  hp.line (L:=a • ContinuousLinearMap.id ℝ E) (le_trans (le_of_eq (norm_smul _ _))
    (mul_le_of_le_one_right (abs_nonneg _) (ContinuousLinearMap.norm_id_le)))

lemma sum_price {ι : Type} (v : Finset ι) {f : ι → PriceCoords G c → E} (C : ι → ℝ)
    (hp : ∀ i∈v, Pays B p q n σ d (C i) (f i)) :
    Pays B p q n σ d (∑ i∈v, C i) (fun x => ∑ i ∈ v, f i x) := by
  refine ⟨ContDiffAt.sum (fun i hi => (hp i hi).smooth),fun z hz l he => ?_⟩
  rw [jet_sum _ _ _ _ (fun i hi => (hp i hi).smooth.of_le le_top)]
  have ha := (marks G c d).pay_pos l z; have hw := (native c).weight_nn σ p q
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le ..) hw) ha.le).trans ?_
  rw [Finset.mul_sum,Finset.mul_sum]; exact Finset.sum_le_sum fun i hi => (hp i hi).each z hz l he

/-- Convert ordinary stencil support into the polarized entry convention,
even at nonzero field parameters. -/
lemma stencil (hp : Allows n u B C) {R : ℕ} (h : Requests univ u coordRoot p R)
    (he : ¬separation p q ≤ R → u=0) (hd : 0 ≤ d) (hσ : 0 ≤ σ) :
    Pays B p q n σ d (Real.exp ((2*(n:ℝ)*d+σ)*R)*C) u := by
  have hC := hp.nonneg; have hg := Real.exp_pos ((2*(n:ℝ)*d+σ)*R)
  by_cases hL : separation p q ≤ R
  swap
  · rw [he hL]; exact Pays.zero (mul_nonneg hg.le hC)
  refine ⟨hp.analytic, fun z hq l hl => ?_⟩
  by_cases hi : jet bolt u l B=0
  · rw [hi,norm_zero,mul_zero,mul_zero]; positivity
  have hj : (native c).d p q ≤ R := by change ((separation p q):ℝ) ≤ _; exact_mod_cast hL
  have hf : ‖jet bolt u l B‖ ≤ C :=
    (entry_bound (p:=B) (f:=u) l.get).trans (hp.norm_le l.length hl)
  have ht (i : Coord G c) (he : i∈l) : (native c).d z (coordRoot i) ≤ 2*(R:ℝ) := by
    obtain ⟨x,hx⟩ := List.get_of_mem he
    subst i
    let i := l.get x
    have hw : (native c).d p (coordRoot i) ≤ R := by
      change ((separation p _):ℝ) ≤ _
      have hh : separation p (coordRoot i) ≤ R := by
        by_contra hy
        exact hi (h.zero (Filter.univ_mem) (hp.analytic.of_le le_top) l.get x hy)
      exact_mod_cast hh
    have hv : (native c).d z p ≤ R := by
      rcases hq with rfl|rfl
      · rw [(native _).self]; positivity
      rw [(native _).comm]; exact hj
    exact le_trans ((native c).triangle z p _) ((add_le_add hv hw).trans_eq (two_mul _).symm)
  have ha := YM.FreeResolvent.Affine.plumb (native c) z coordRoot l hd (2*(R:ℝ)) ht
  refine (mul_le_mul ha (mul_le_mul
    (Real.exp_monotone (mul_le_mul_of_nonneg_left hj hσ)) hf (norm_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg ((native c).weight_nn ..) (norm_nonneg _)) (Real.exp_pos _).le).trans ?_
  rw [← mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_right (Real.exp_monotone _) hp.nonneg
  have hx : (l.length:ℝ) ≤ n := by exact_mod_cast hl
  nlinarith only [mul_le_mul_of_nonneg_right hx (mul_nonneg hd (Nat.cast_nonneg R))]
end Pays
end entries

variable {A : Stores S} {T : Tube G S} {F : Forest S.ratio} {i : Cell f} {l : RG.Slot} {s : Signed}

private lemma face_price {B : PriceCoords G c} (V : Config G c) (j : Coord G f)
    {u : PriceCoords G c → G.Color} (hu : u=fun y => plaquetteJet S (field V y) s i (fineRay j))
    (hw : Allows n u B C) (hσ : 0 ≤ σ) (hd : 0 ≤ d) :
    Pays B (s.act (S.ratio.parent i.1)) (location S j) n σ d (Real.exp ((2*n*d+σ)*5)*C) u := by
  subst u
  refine (Pays.stencil hw (R:=5) (fun v _ w _ h => ?_) (fun h => funext fun z => off_face h _) hd hσ)
  dsimp only; rw [face_field_dep i s (W:=field V w) (field_dep (fun _ _ => rfl) h)]

private lemma noise_price {B : PriceCoords G c} (V : Config G c) (i : Bond c) (k : S.Choices)
    (j : Coord G f) {u : PriceCoords G c → G.Color}
    (hu : u=fun y => blockJet (field V y) k s i (fineRay j)) (hk : S.patch.Branches S.kernel G)
    (hw : Allows n u B C) (hσ : 0 ≤ σ) (hd : 0 ≤ d) :
    Pays B (s.act i.1) (location S j) n σ d (Real.exp ((2*n*d+σ)*(predReach S.patch+1:ℕ))*C) u := by
  subst u
  refine (Pays.stencil hw (R:=predReach S.patch+1) (fun v _ w _ h => ?_)
    (fun h => funext fun z => off_prediction hk h _) hd hσ)
  dsimp only; rw [predictor_field_dep k i s hk (W:=field V w) (field_dep (fun _ _ => rfl) h)]

section stack
variable {o : Cell f} {x : ℝ} {B : PriceCoords G c} {b K κ : ℝ}

private lemma piece_price (V : Config G c) (j : Coord G f) (hC : 0 ≤ C)
    (hw : Allows n (piece S V s (fineRay j) o l) B (C*Real.exp (κ*l.length))) (hσ : 0≤σ) (hd : 0≤d)
    (hh : 2*n*d + σ + κ ≤ δ) :
    Pays B (s.act (S.ratio.parent o.1)) (location S j) n σ d
      ((Real.exp ((2*n*d+σ)*5)*C)*Real.exp (δ*l.length)) (piece S V s (fineRay j) o l) := by
  have h := Pays.stencil hw (R:=l.length+5) (q:=location S j) (p:=s.act (S.ratio.parent o.1))
    (fun v hv w hz hl => transported_field_dep _ _ _ _ (W:=field V w) (field_dep (fun _ _ => rfl) hl)) off_piece hd hσ
  apply h.mono
  calc Real.exp _*(C*_) = C*Real.exp ((2*n*d+σ)*((l.length:ℝ)+5)+κ*l.length) := by push_cast; rw [Real.exp_add]; ring
       _ ≤ C*Real.exp ((2*n*d+σ)*5+δ*l.length) := by
         apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hC; linarith only [mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg l.length)]
       _ = _ := by rw [Real.exp_add]; ring

private lemma barrel_price (j : Coord G f) (V : Config G c) (hC : 0 ≤ C) {Λ : ℝ}
    {c₀ : Clip} (hT : T.up.Bounds c₀ δ b Λ) (hσ : 0 ≤ σ) (hd : 0 ≤ d) (hh : 2*n*d+σ+κ ≤ δ)
    (hp : ∀ l : RG.Slot, l.length≤ Stores.till x → Allows n (piece S V s (fineRay j) o l) B
      (C*Real.exp (κ*l.length))) :
    Pays B (s.act (S.ratio.parent o.1)) (location S j) n σ d (b*(Real.exp ((2*n*d+σ)*5)*C))
      (fun y : PriceCoords G c => barrel T.up (Stores.till x) (facade S s (field V y) 0)
        (fun u => plaquetteJet S (field V y) s u (fineRay j)) o) := by
  let N := Stores.till x
  let M := Real.exp ((2*n*d+σ)*5)*C
  let F := Stack.allShort N
  simp_rw [Stack.finite_price o _ _ _ hT]
  change Pays B _ _ _ _ _ _ (fun y => ∑ z ∈ F, Stack.grouped T.up o.2 z • piece S V s (fineRay j) o z y)
  refine Pays.mono (Pays.sum_price F _ fun l h => (piece_price V j hC (hp l ((Stack.short_iff ..).mp h)) hσ hd hh).scale (Stack.grouped T.up o.2 l)) ?_
  change (∑ l ∈ F, |Stack.grouped T.up o.2 l| * (M*Real.exp (δ*l.length))) ≤ b*M
  simp_rw [mul_comm M _, ← mul_assoc, ← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (Stack.grouped_le F hT o.2) (mul_nonneg (Real.exp_pos _).le hC)
end stack

lemma Pays.read_color {B : PriceCoords G c} {f : PriceCoords G c → G.Color} {p q : Site c}
    (h : Pays B p q n σ d C f) (i : G.ColorIndex) : Pays B p q n σ d C (fun y => f y i) := by
  let L := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hl : ‖L‖ ≤ 1 := L.opNorm_le_bound zero_le_one (fun y => by
    rw [one_mul]; change |y i| ≤ _
    rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ y i]
    simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ i) y)
  have he := h.line hl; rw [one_mul] at he; exact he

/-- Uniform post-L and period independent entry and mark price. Local
genuine Stored flags on the base V taken globally here. -/
lemma selected_priced (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r d M : ℝ, 0<r ∧ 0<d ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
      100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (B : PriceCoords G c), ‖B‖≤r →
    ∀ (k : S.Choices) (i : Rows.Receipt G S) (j : Coord G f),
      Pays B (Wisps.down S i) (location S j) n (2*d) d M
        (fun z => tape.symm (Rows.selected T x (field V z) k (shots S x) A F (fineRay j)) i) := by
  let σ := Pt.top.width; let K := Pt.bind; let κ := σ/2; have hσ : 0<σ := Pt.top.width_pos
  have hκ : 0<κ := half_pos hσ
  let d := σ/(4*(n+1:ℕ))
  have hd : 0<d := div_pos hσ (by positivity)
  have hh : 2*n*d + 2*d + κ ≤ σ := by
    have he : d*(4*(n+1:ℕ))=σ := div_mul_cancel₀ _ (by positivity)
    unfold κ; push_cast at *; linarith only [he]
  obtain ⟨r,C,hr,hC,H⟩ := face_paid G n
  obtain ⟨s,M,hs,hM,H'⟩ := path_paid G hκ n
  obtain ⟨t,E,ht,hE,Hm⟩ := block_paid G P K hk n
  let R := min r (min s t)
  let v := 2*n*d+2*d
  let L₀ := Real.exp (v*5)
  let L := Real.sqrt Pt.top.clip.direct * (L₀*C)
  let U := Pt.top.paths*(L₀*M)
  let W := Real.sqrt Pt.bind.penalty*(Real.exp (v*(predReach P+1:ℕ))*E)
  let m := max W (max L U)
  have hR : 0<R := lt_min hr (lt_min hs ht)
  have hW : 0<W := mul_pos (Real.sqrt_pos.2 Pt.bind.penalty_pos) (mul_pos (Real.exp_pos _) hE)
  have hz : 0<slip*m := mul_pos slip_pos (lt_of_lt_of_le hW (le_max_left ..))
  refine ⟨R,d,_,hR,hd,hz,?_⟩
  filter_upwards [Hm] with x hx
  rintro c f S T hP hf hT A F V hA B hB k ⟨⟨i,u⟩,l⟩ j
  have he : Pays B (i.act (roots S (u.elim (fun j => .inl j.1) .inr))) (location S j) n
      (2*d) d (slip*m) (fun z => Rows.restrict x (shots S x) A F
        (bump T x (field V z) k (fineRay j)) (i,u)) := by
    unfold Rows.restrict; split
    next ha =>
      suffices h : Pays B (i.act (roots S (u.elim (fun j => .inl j.1) .inr))) (location S j) n
          (2*d) d m (fun z => bump T x (field V z) k (fineRay j) (i,u)) by
        simpa only [abs_of_pos slip_pos] using h.scale slip
      rcases u with u|u
      · simp only [Sum.elim_inl,bump,faceKick]; split
        · obtain ⟨X,Y,hD,-⟩ := hT.feeds
          refine (barrel_price (x:=x) (B:=B) (o:=u.1) (s:=i) j V hM.le hD (by positivity) hd.le hh ?_).mono
            ((le_max_right L U).trans (le_max_right W _))
          exact fun l _ => H' _ _ _ _ (fineRay_norm j).le _ _ _ (hB.trans ((min_le_right ..).trans (min_le_left ..)))
        · have Hc := (H S V B (hB.trans (min_le_left ..)) i u.1).2 _ (fineRay_norm j).le
          have hw := (face_price V j (i:=u.1) (s:=i) rfl Hc (σ:=2*d) (by positivity) hd.le).scale (Real.sqrt T.high.direct)
          simp_rw [abs_of_nonneg (Real.sqrt_nonneg _),hT.high] at hw ⊢
          exact hw.mono ((le_max_left L U).trans (le_max_right W _))
      simp only [bump, noiseKick, Sum.elim_inr, ← neg_smul]
      have Hb := (hx S hP hT.knobs hf F A V hA i u B ha (hB.trans ((min_le_right ..).trans (min_le_right ..))) k).2 _ (fineRay_norm j).le
      have hk' : S.patch.Branches S.kernel G := hT.knobs.symm ▸ hT.kernel
      have hp := (noise_price V u k j (s:=i) rfl hk' Hb (σ:=2*d) (by positivity) hd.le).scale (- Real.sqrt S.kernel.penalty)
      rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)] at hp
      refine hp.mono (le_trans (le_of_eq ?_) (le_max_left W _))
      unfold W v; rw [hP,hT.knobs]
    exact Pays.zero hz.le
  exact he.read_color l

/-- Apply to the active D (already includes frozen exclusion). -/
lemma moves_priced (G : Gauge) (P : Patch) (Pt : Teller G) (hk : P.Branches Pt.bind G) (n : ℕ) :
    ∃ r d M : ℝ, 0<r ∧ 0<d ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
      100*(1+radiusB x) ≤ c.val → Pt.Funds S T → ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (B : PriceCoords G c), ‖B‖≤r →
    ∀ (k : S.Choices) (i : Rows.Receipt G S) (j : Rows.In x A F (G:=G)),
      Pays B (Wisps.down S i) (Wisps.front A F j) n (2*d) d M
        (fun z => Rows.move T x (field V z) k (shots S x) A F i j) := by
  obtain ⟨r,d,M,hr,hd,hM,h⟩ := selected_priced G P Pt hk n
  refine ⟨r,d,M,hr,hd,hM,?_⟩; filter_upwards [h] with x hx
  intro c f S T hs hf hP A F V ha B hB k i j
  simp_rw [move,Matrix.of_apply,show fresh x (shots S x) A F (axisPrice j)=fineRay (j.1.val.val, j.2) from sourceKey_eq j]
  exact hx S T hs hf hP A F V ha B hB k i (j.1.val.val,j.2)
end YM.AnalyticBridge.SectorAffine
