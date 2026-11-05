import YM.Next.FOUNDATIONS.Primary
import YM.SectorNext.LARGE_FIELD_REMAINDERS.CollarData


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Ownable annulus bound on merged regions

Lower bound, in
per-seed price, delay-priced e(times halo)^4 even after β.

To use with ANY
squared reference on the caller's selected F,I addresses; provide actual
positions for a on their stencils, or use `Cleans` auxiliary witnessing common
constructor.

The a supplied doesn't need to satisfy untrue global log laws at
frozen links.

This applies BEFORE a later Gaussian substitution or after only
in the sense that one has kept these hypotheses at the U in question (or has
paid all other rows separately); not claiming the entire integrand then has
no other corrections.

Does not pull a forbidding overlap apart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Scales Metric   Exterior Bloch Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Reserve e.g. a `$K_L t$` shell on all exterior/affine positions. It's ALSO okay to
ask this only near the particular rows on which the squares are selected (omit
unselected); here we don't require the selection predicate itself if so. Threshold
constant may include larger post-L broad cut radii. -/
def PatchInputs (U : Config G f) (V : Config G c) (a : Directions G f) (K x : ℝ) (y : Site c) :=
    let g := S.ratio.parent; let W := replica S.ratio V
    ∀ i : Bond f, separation y (g i.1) ≤ thin x → U i = increment W a i ∧ ‖a i‖ ≤ K*fiery G x S.patch.L

/-- Even legitimate if an unachieved approximation spec uses only this annulus
extraction with *ANY* choices of a inputs coinciding on the indicated patches.
This estimate doesn't need the mean or covariance entries. -/
lemma patch_agreed (T : Tube G S) (U : Config G f) (V : Config G c) (a a₀ : Directions G f) (k : S.Choices)
    {K X x : ℝ} (hv : fiery G x S.patch.L > 0)
    (hs : (max K X)*fiery G x S.patch.L < (Next.Foundations.chart G).radius)
    (hd : till x+1 ≤ thin x) (he : predReach S.patch ≤ thin x)
    (hb : S.patch.Branches S.kernel G) {i : Site c} :
    PatchInputs (S:=S) U V a K x i → PatchInputs (S:=S) U V a₀ X x i →
    (∀ p : Cell f, S.ratio.parent p.1=i →
      squareP T (till x) (temp x) V (replica S.ratio V) a p=squareP T (till x) (temp x) V (replica S.ratio V) a₀ p ∧
      perCharge T.up (till x) (replica S.ratio V) a p=perCharge T.up (till x) (replica S.ratio V) a₀ p ∧
      let t (q : Cell f) (a : Directions G f) (r : ℝ) := G.curvature (faceValue (increment (replica S.ratio V) (r • a)) q)
      t p a=t p a₀ ∧ ∀ j : ℕ, (T.up.row p.2 j).2.length ≤ till x →
        let u := slotFace (T.up.row p.2 j).2 p.1
        t u a=t u a₀) ∧
      ∀ p : Bond c,p.1=i →
        squareQ T (till x) (temp x) V (replica S.ratio V) k a p = squareQ T (till x) (temp x) V (replica S.ratio V) k a₀ p ∧
        actuate S (replica S.ratio V) p k a=actuate S (replica S.ratio V) p k a₀ := by
  intro h h0
  have hx (b : Bond f) (hi : separation i (S.ratio.parent b.1) ≤ thin x) : a b=a₀ b := by
    obtain ⟨h1,h2⟩ := h b hi; obtain ⟨h3,h4⟩ := h0 b hi
    have hl : G.lieExp (a b)=G.lieExp (a₀ b) := mul_right_cancel (h1.symm.trans h3)
    apply (Next.Foundations.chart_ok G).inject ?_ ?_ hl <;> rw [mem_ball_zero_iff]
    · exact h2.trans_lt ((mul_le_mul_of_nonneg_right (le_max_left ..) hv.le).trans_lt hs)
    exact h4.trans_lt ((mul_le_mul_of_nonneg_right (le_max_right ..) hv.le).trans_lt hs)
  let W := replica S.ratio V
  have ha (q : ℝ) b (hi : separation i (S.ratio.parent (b:Bond f).1) ≤ thin x) :
      increment W (q • a) b=increment W (q • a₀) b := by unfold increment; simp only [Pi.smul_apply,hx b hi]
  constructor
  · intro p hp
    let t (q : Cell f) (a : Directions G f) (r : ℝ) := G.curvature (faceValue (increment W (r • a)) q)
    have H q (he : separation i (S.ratio.parent (q : Cell f).1) ≤ till x) : t q a=t q a₀ := by
      have hg (r : ℝ) (j : Fin 4) := ha r (patchFace q j) ((separation_triangle ..).trans
        ((Nat.add_le_add he (faceLink (S:=S) q j)).trans hd))
      funext r; unfold t faceValue
      let x := q.1; let i0 := q.2.val.1; let j := q.2.val.2
      have ht (x : Site f) (i j : Axis) : x+step i+step j-step i=x+step j:= by abel
      have ht' (x : Site f) (i j : Axis) : x+step i+step j+(-step i)=x+step j:= by abel
      simp only [square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,ht,ht',add_sub_cancel_right]
      rw [show increment W (r • a) (q.1,q.2.val.1)=increment W (r • a₀) (x,i0) from hg r 0,
        show increment W (r • a) (q.1+step q.2.val.1,q.2.val.2)=increment W (r • a₀) (x+step i0,j) from hg r 1,
        show increment W (r • a) (q.1+step q.2.val.2,q.2.val.1)=increment W (r • a₀) (x+step j,i0) from hg r 2,
        show increment W (r • a) (q.1,q.2.val.2)=increment W (r • a₀) (x,j) from hg r 3]
    let v j := (T.up.row p.2 j).2
    have hl j (h : (v j).length≤till x) := H (slotFace (v j) p.1) (show separation i _ ≤ _ by
      rw [← hp]; exact (chart_in _ _ _ (slot_based ..)).trans h)
    have hT : t p a=t p a₀ := H p (by simp only [hp,separation_self,Nat.zero_le])
    have hq : perCharge T.up (till x) W a p=perCharge T.up (till x) W a₀ p := by
      funext j; unfold perCharge firstSlot firstFace faceVar; dsimp only; split
      next hw => rw [show (fun r => G.curvature (faceValue (increment W (r • a)) _))=_ from hl j hw]
      next _ => rfl
    have hZ : faceVar W a p=faceVar W a₀ p := congr_arg (fun u : ℝ→G.Color => deriv u 0) hT
    refine ⟨?_,hq,hT,hl⟩
    unfold squareP affF1 affF0 firstFace firstCut W at *; rw [hq,hZ]
  intro b ht
  have hf : actuate S W b k a=actuate S W b k a₀ := funext fun r => prediction_near_eq hb _ _ k b
    (fun j hj => ha r j (show separation i _ ≤ _ by rw [← ht]; exact hj.trans he))
  refine ⟨?_,hf⟩; unfold squareQ qVar W at *; rw [hf]

structure Window (S : StepData c f) where
  face : Finset (Cell f)
  noise : Finset (Bond c)
  coarse : Finset (Cell c)
  rows : Finset (Co c Gain)

variable (Q : Window S)

def Window.work (T : Tube G S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
    onWindow T x Q.face Q.noise Q.coarse Q.rows U (S.prediction U k) V

def Window.selects (F : Window S) : Prop := Q.face ⊆ F.face ∧ Q.noise ⊆ F.noise

def Window.extract (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) (a : Directions G f) :=
    (∑ i∈Q.face, squareP T (till x) (temp x) V (replica S.ratio V) a i)+
      (∑ i∈Q.noise, squareQ T (till x) (temp x) V (replica S.ratio V) k a i)

def Window.charts (U : Config G f) (V : Config G c) (a : Directions G f) (K x : ℝ) :=
    (∀ i∈Q.face, PatchInputs (S:=S) U V a K x (S.ratio.parent i.1)) ∧
      ∀ i∈Q.noise, PatchInputs (S:=S) U V a K x i.1

def Window.annulus (O A : Stores S) (D B : ℕ) :=
    (∀ i∈Q.face, inSweep O A D B (S.ratio.parent i.1)) ∧
    (∀ i∈Q.noise, inSweep O A D B i.1) ∧
    (∀ i∈Q.coarse, inSweep O A D B i.1)

def Window.written (T : Tube G S) (x : ℝ) (k : S.Choices) (V : Config G c) (a : Directions G f) : Prop :=
    let W := replica S.ratio V
    let f p (t : ℝ) := G.curvature (faceValue (increment W (t • a)) p)
    (∀ i∈Q.face, Summable (perCharge T.up (till x) W a i) ∧ DifferentiableAt ℝ (f i) 0 ∧
      ∀ j, (T.up.row i.2 j).2.length ≤ till x → DifferentiableAt ℝ (f (slotFace (T.up.row i.2 j).2 i.1)) 0) ∧
      (∀ i∈Q.noise,
        let v := actuate S W i k a
        DifferentiableAt ℝ (fun t => G.curvature (v t*(v 0)⁻¹)) 0 ∧ DifferentiableAt ℝ (G.mat∘v) 0 ∧
        G.colorMat (qVar S W i k a) = deriv (G.mat∘v) 0*G.mat ((S.prediction W k i)⁻¹))

lemma Window.torus {O A : Stores S} {D x} (h : Q.annulus O A D (radiusB x)) :
    let K := 4*((D+D+1:ℕ):ℝ)^4 * b x ^4 * O.shares
    ((Q.face.card:ℝ) ≤ (S.patch.L.val:ℝ)^4 * (Fintype.card PlaqAxes:ℝ)*K) ∧
    ((Q.noise.card:ℝ) ≤ (Fintype.card Axis:ℝ)*K) ∧ ((Q.coarse.card:ℝ) ≤ (Fintype.card PlaqAxes:ℝ)*K) := by
  intro K
  let H := O.dome (D*radiusB x)
  let P := Fintype.card PlaqAxes
  have hc {α : Type} [Fintype α] (s : Finset (Site c × α)) (he : ∀ i∈s, (i:Site c × α).1∈H) :
      s.card ≤ H.card*Fintype.card α := (Finset.card_le_card (show s ⊆ H ×ˢ Finset.univ from
        fun i hi => Finset.mem_product.mpr ⟨he i hi,Finset.mem_univ _⟩)).trans_eq (by simp)
  let g := S.ratio
  let e : Equiv (Cell f) ((Site c × Site g.count) × PlaqAxes) := Equiv.prodCongr g.splitSites (Equiv.refl _)
  let F := Q.face.map e.toEmbedding
  have hv : F ⊆ (H ×ˢ (Finset.univ : Finset (Site g.count))) ×ˢ (Finset.univ : Finset PlaqAxes) := by
    intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨(h.1 a ha).2,Finset.mem_univ _⟩, Finset.mem_univ _⟩
  have hp : Q.face.card ≤ H.card*S.patch.L.val^4 * P := by
    rw [← site_card S.patch.L]
    have hk := Finset.card_le_card hv; simp only [F,Finset.card_product,Finset.card_univ,Finset.card_map] at hk; exact hk
  have hH : (H.card:ℝ)≤K := by
    apply le_trans (Nat.cast_le (α:=ℝ).mpr (Corona.halo_size O.place _))
    have hi := Nat.cast_le (α:=ℝ).mpr (Work.E01.place_card O); push_cast at hi
    have hm : (radiusB x:ℝ)+1=b x := add_comm _ _
    push_cast; unfold K
    have hh : (↑D:ℝ)*radiusB x+D*radiusB x+1 ≤ ((↑D:ℝ)+D+1)*b x := by rw [← hm]; have := Nat.cast_nonneg (α:=ℝ) D; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
    have he := mul_le_mul hi (pow_le_pow_left₀ (by positivity) hh 4) (by positivity) (by positivity); rw [mul_pow] at he
    apply he.trans_eq; push_cast; ring
  obtain hh := Nat.cast_le (α:=ℝ).mpr hp
  obtain h1 := Nat.cast_le (α:=ℝ).mpr (hc Q.noise (fun i hi => (h.2.1 _ hi).2))
  obtain h2 := Nat.cast_le (α:=ℝ).mpr (hc Q.coarse (fun i hi => (h.2.2 _ hi).2))
  push_cast at hh h1 h2
  constructor
  · refine hh.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hH (show 0 ≤ (S.patch.L.val:ℝ)^4 by positivity)) (Nat.cast_nonneg P)).trans_eq (by unfold P; ring))
  constructor
  · exact h1.trans ((mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg _)).trans_eq (mul_comm _ _))
  exact h2.trans ((mul_le_mul_of_nonneg_right hH (Nat.cast_nonneg _)).trans_eq (mul_comm _ _))

end YM.SectorNext.Remainder.Affine
