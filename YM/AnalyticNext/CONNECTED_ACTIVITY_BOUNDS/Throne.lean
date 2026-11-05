import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Palace

/-!
# E estimates F/I work against affine square

Pointwise on patch of a real sector. Equality to original multipliers
only requested on their masks. `Fextend` is one choice for exponent
letters outside compulsory. I requires no such expansion for values:
use its real Q, with the branch forced on broad patches. Unselected F/I
pay with their own sign on the patch prerequisites. Even though E writes
an analytic Taylor split, for ungraded hit it suffices to retain the real
values. Needn't extend DIFFERENT casts for every incoming mask term.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Rates
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def squareOf (a : G.Color) := ‖a‖^2/2

def missed (G : Gauge) (u : G.El) := G.chord u^2- ‖G.curvature u‖^2

theorem missed_nn (G : Gauge) (u : G.El) : 0≤ missed G u :=
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm u) _)

lemma currency (C : ℝ) (D : Patch) (p : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ u : G.El, G.chord u ≤ allowance G D x 1 p → |C*missed G u| ≤ allowance G D x 4 (p+p+p+p+1) := by
  obtain ⟨K,r,hK,hr,h⟩ := Work.E05.curvature_lower G
  filter_upwards [(vanishes G D p).eventually (ge_mem_nhds hr), grow G D (|C| *K)
    (show p+p+p+p<p+p+p+p+1 by omega) 4] with x hx hv u he
  have hz := (h u (he.trans hx)).1
  rw [abs_mul,abs_of_nonneg (missed_nn ..)]
  apply le_trans _ hv
  calc
    _ ≤ |C| *(K*G.chord u^4) := by
      unfold missed
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith
    _ ≤ |C| *(K*allowance G D x 1 p^4) := by gcongr; exact G.chord_nonneg _
    _ = _ := by rw [← mul_assoc]; unfold allowance pieces; ring

lemma difference_pay (G : Gauge) (D : Patch) (p q : ℕ) : ∀ᶠ x : ℝ in atTop,
    ∀ a b : G.Color, ‖a‖ ≤ allowance G D x 1 p → ‖a-b‖ ≤ allowance G D x 2 q →
      |squareOf a-squareOf b| ≤ allowance G D x 3 (q+p+1) := by
  filter_upwards [grow G D (3/2) (show q+p<q+p+1 by omega) 3, Rates.widen G D 1 (show 0≤p by omega),
    burn G D 1 q 1 1 (by norm_num)] with x hx he hp a b ha h
  have ht : ‖b‖ ≤ 2*allowance G D x 1 p := by
    have hh := norm_le_norm_sub_add b a; rw [norm_sub_rev] at hh; linarith
  apply le_trans _ hx
  have hq : 0 ≤ allowance G D x 2 q := allowance_nn ..
  calc
    _ = |‖a‖-‖b‖| *((‖a‖+‖b‖)/2) := by
      rw [← abs_of_nonneg (show 0 ≤ (‖a‖+‖b‖)/2 by positivity), ← abs_mul]; unfold squareOf; ring_nf
    _ ≤ allowance G D x 2 q * (3/2*allowance G D x 1 p) :=
      mul_le_mul ((abs_norm_sub_norm_le ..).trans h) (by linarith) (by positivity) hq
    _ = _ := by rw [mul_left_comm,exchange]

def sqref (T : Tube G S) (x : ℝ) (k : S.Choices) (i : Pos S) (V : Config G c) (w : Directions G f) :=
    squareOf (target T (till x) (temp x) i k V (replica S.ratio V) + derivative T (till x) i V w)

def crownF (T : Tube G S) (x : ℝ) (k : S.Choices) (s : Signed) (i : Cell f) (V : Config G c) (a : Directions G f) :=
    ∑ l : Bool, sqref T x k (s,Sum.inl (i,l)) V a

def crownI (T : Tube G S) (x : ℝ) (k : S.Choices) (s : Signed) (i : Bond c) (V : Config G c) (a : Directions G f) :=
    sqref T x k (s,Sum.inr i) V a

/-- unweighted inside exponent, per entire oriented face, scalar. -/
def Fextend (T : Tube G S) (x : ℝ) (k : S.Choices) (s : Signed) (i : Cell f) (V : Config G c) (U : Config G f) :=
    let W := pull s 0 U
    T.high.direct/2*missed G (faceValue W i) + ∑ l : Bool, squareOf (target T (till x) (temp x) (s,Sum.inl (i,l)) k V U)



lemma square_residue (A B : G.Color) : squareOf A + (‖B‖^2/2-inner ℝ B A)=squareOf (A-B) := by
  unfold squareOf; rw [norm_sub_sq_real,real_inner_comm]; ring

lemma work_expandF (T : Tube G S) (x : ℝ) (k : S.Choices) (s : Signed) (i : Cell f) (V : Config G c) (U : Config G f)
    (hp : PathData.kept T.high (fiery G x S.patch.L) i.1 (pull s 0 U)) :
    T.workF (till x) (pull s 0 U) (pull s 0 V) (fiery G x S.patch.L) (temp x) i = Fextend T x k s i V U := by
  let W := pull s 0 U; let R := till x; let X j := T.Xf R W (i,j); let H j := T.Mv R (temp x) (pull s 0 V) (i,j)
  have ht : toll W i ≤ fiery G x S.patch.L := by
    have he := hp i; simpa only [W,toll,separation_self,Nat.cast_zero,zero_div,Real.exp_zero,mul_one] using he
  have h1 : crown T.up T.high R 1 (fiery G x S.patch.L) W i =
      T.high.direct/2*missed G (faceValue W i)+ ∑ l:Bool,squareOf (X l) := by
    unfold crown; rw [trunk,if_pos hp,PathData.clipped, if_pos (show G.chord (faceValue W i)≤_ from ht),Fintype.sum_bool]
    simp only [squareOf,missed,X,Tube.Xf,plotted,Bool.false_eq_true, ↓reduceIte,shoot,norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt T.high.quadratic_pos.le]
    ring
  unfold Tube.workF; rw [h1,add_assoc]; unfold Fextend; apply congr_arg (fun v : ℝ => T.high.direct/2*missed G (faceValue W i)+v)
  rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => square_residue (X j) (H j)

lemma work_expandI (T : Tube G S) (Q V : Config G c) (s : ℝ) (R : ℕ) (i : Bond c) :
    T.workI R Q V s i = S.kernel.penalty/2 * missed G (V i * (Q i)⁻¹) + squareOf (Tube.Z S Q V i-T.Mw R s V i) := by
  rw [← square_residue]; unfold Tube.workI Tube.monetary
  unfold wire squareOf Tube.Z missed
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt S.kernel.penalty_pos.le]; ring






-- Momentum-to-chord bootstrapping. Need to pay `Mw` here; can't deduce
-- connector accuracy from a bound on `Z-Mw` alone. N. likelihood bought
-- on the same stencil. State for all turned I though stencils overlap.
lemma alerts (P : Teller G) (C : ℝ) (he : Reserve P C) (D : Patch) (hD : D.Branches P.bind G) (p : ℕ) (hp : 7≤p) :
    ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → P.Funds S T → ∀ (V : Config G c) (A : Stores S) (_F : Forest S.ratio), cert S x A V →
      ∀ (k : S.Choices) (U : Config G f) (i : Bond c) (s : Signed) (w : Directions G f), let B := radiusB x
      let o := s.act i.1
      o∉A.dome (2*B) → Stops S w V U o B (allowance G D x 1 p) →
      let W := pull s 0 V; let U' := pull s 0 U; let k' := choice s k; let Q := S.prediction U' k'
      wire Q W i ≤ allowance G D x 1 (p+6) ∧ αSite U' i.1 k'=1 ∧ αBond U' i k'=1 := by
  obtain ⟨K,r,hK,hr,hk⟩ := Work.E05.curvature_lower G
  let l := Real.sqrt P.bind.penalty
  have hl : 0 < l := Real.sqrt_pos.mpr P.bind.penalty_pos
  filter_upwards [arc_bill P C he D hD p hp, shine G D p hp, cordF D P.bind hD (p+2) r hr, he.receipt D.L,
    grow G D C (show 0<p+4 by omega) 1,grow G D (2*(2/l)) (show p+4<p+6 by omega) 1]
    with x hx hv hp ht hh hm c f S T hS hT V A F he k U i s w B o hA hw W U' k' Q
  obtain ⟨z,hz⟩ := hv c f S U V A w hS he s i.1 hA hw
  obtain ⟨ha,hy,hv⟩ := hp S i W U' z k' hS hT.knobs hz
  let b := allowance G D x 1 (p+4)
  let g := W i * (Q i)⁻¹
  refine ⟨?_,hy,hv⟩
  have hf : ‖Tube.Z S Q W i - T.Mw (till x) (temp x) W i‖ ≤ b := (hx c f S T hS hT V A F he k U (s,Sum.inr i) w hA hw).1
  have hc : ‖T.Mw (till x) (temp x) W i‖ ≤ b := by
    have hp := (ht c f S T hT (congr_arg Patch.L hS) he.1 F W).2.2.hot i
    rw [hS] at hp; simp only [allowance,pieces,pow_zero,one_mul,pow_one] at hh; apply hp.trans; simpa [b,allowance,pieces] using hh
  have hs : l * ‖G.curvature g‖ ≤ 2*b := by
    have he : ‖Tube.Z S Q W i‖ ≤ 2*b := le_trans (norm_le_norm_sub_add _ _) ((add_le_add hf hc).trans_eq (two_mul b).symm)
    rwa [Tube.Z,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hT.knobs] at he
  have hh : ‖G.curvature g‖ ≤ 2/l*b := le_of_mul_le_mul_left (hs.trans (le_of_eq (show 2*b=l*(2/l*b) by field_simp))) hl
  calc
    _ ≤ 2 * ‖G.curvature g‖ := by unfold wire; change G.chord g ≤ 2*_; nlinarith only [(hk g ha.le).2,norm_nonneg (G.curvature g)]
    _ ≤ _ := le_trans (mul_le_mul_of_nonneg_left hh (by norm_num)) (by rw [← mul_assoc]; exact hm)


end YM.AnalyticNext.ConnectedActivity.Aff
