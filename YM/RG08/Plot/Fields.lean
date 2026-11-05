import YM.RG08.Bands.Cannon
/-!
# Testing profiles on the full UV wing with rho^-power convention on root

Address derivatives are Euclidean. Roots may be arbitrarily distant from the
origin within these conventions; proofs use measurements native to interpretation.
`Load` cost charged for full compact profiles only.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Plot
open Filter Analysis Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Town Bands
open scoped BigOperators Topology Real ContDiff Classical
variable {I J Y:Type}{m b i K L D t r:ℕ} {z:Cover}{v θ R A B:ℝ}{x w:E4}{G:Gauge}{X: Chain}{g:Exam D}
section tests
def stud (a:ℝ)(x:E4)(z:Cover) := a • Place.seat z - x
def exteriorP (φ:Exam D)(a:ℝ)(x:E4)(z:Cover) : Exam D:= Pages.roll (stud a x z) a φ
def Reads (φ:Exam D)(P:ℝ): Prop := ∀ i≤D,∀ x:E4,‖iteratedFDeriv ℝ i φ.val x‖≤ P
lemma reads_roll (p:Reads g A)(hp:0≤θ)(hx:θ≤1) : Reads (exteriorP g θ x z) A:= by
   intro i hi y; unfold exteriorP; rw [Pages.facades _ _ _ _ hi,norm_smul, Real.norm_of_nonneg (pow_nonneg hp _)]; exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hp hx)).trans (p _ hi _)
lemma tutelage (h:Reads g A)(ht:0≤A) (R:ℝ) : ‖plug g R‖ ≤ A := by
   have hp : ‖sheet D R g‖ ≤ A:= by
     refine (bound D R g ht).mpr ?_; rintro ⟨⟨i,hi⟩,y⟩ x
     have ht:i≤D:=by omega
     change ‖iteratedFDeriv ℝ i g.val _ _‖ ≤ _
     refine ((iteratedFDeriv ℝ i g.val x.val).le_opNorm (basis ∘ y)).trans ?_; have hh : ∀ a: Fin i, ‖(basis∘y) a‖=1:= fun a=> by simp [basis]; -- @basis E4
     simp_rw [hh]; rw [prod_const_one,mul_one]; exact h _ ht _
   exact ContinuousLinearMap.opNorm_le_bound _ ht fun f=> (f.le_opNorm (sheet D R g)).trans (by rw [mul_comm A]; exact mul_le_mul_of_nonneg_left hp (norm_nonneg _))
-- reached support points include derivative support

def Spatial (g:Exam D)(C:ℝ):Prop:= ∀ x∈ tsupport g.val, x∈Scores.examinable C
def reached (g:Exam D)(x:E4)(θ R:ℝ)(z:Cover):Prop:= ∃ w:Scores.Close R, (stud θ x z+θ•w.val)∈ tsupport g.val
lemma no_exam (h:¬ reached g x θ R z)(u:Voice D R): plug (exteriorP g θ x z) R u=0:= by
   let F:= exteriorP g θ x z;
   have hv: sheet D R F = 0 := by
     apply Subtype.ext; ext1 i; apply ContinuousMap.ext; intro t
     obtain ⟨⟨i,hi⟩,p⟩:= i; have ht:i≤D:=by omega
     change iteratedFDeriv ℝ i F.val t.val (basis ∘ p)=0
     rw [show F=Pages.roll _ _ g from rfl,Pages.facades _ _ _ _ ht]
     have hp(t:Close R): iteratedFDeriv ℝ i g.val (stud θ x z+θ•t.val)=0:= not_ne_iff.mp fun hv=>h ⟨t,support_iteratedFDeriv_subset (𝕜:=ℝ) i hv⟩
     rw [hp t,smul_zero]; rfl
   change u (sheet D R F)=0; rw [hv, map_zero]
-- can charge operator cost explicitly with arbitrary readouts and native norm
lemma slot_budget (V: EnvelopeU D R G r) (hv:cis K v V B)(hp:0≤v)(h:Reads g A)(ht:0≤A): cis K v (plug g R ∘ V) (A*B) := Ink.raise (hv.some _ (zero_le_one.trans (tailp hp))) (mul_le_mul_of_nonneg_right (tutelage h ht R) hv.nonneg) -- B not variable
-- R ratio growth on changing root count

def circleP (C R θ:ℝ):= (⌈(1+R+C/θ)⌉₊)
def pieceA (X:Chain)(k i:ℕ)(x:E4)(d:ℝ)(R:ℝ):= (Lattice.box (circleP d R (spanP X k i))).image fun j=>j+arcT X k i x
lemma signed_norm (x:ℤ): ‖(x:ℝ)‖=(x.natAbs:ℝ):= by rw [← norm_natAbs,Real.norm_natCast]
lemma extent_p (h:Spatial g A)(hp:reached g x (spanP X K i) R z)(j:Axis): ((z - arcT X K i x) j).natAbs ≤ circleP A R (spanP X K i):= by
   let α:= spanP X K i; let Y:= arcT X K i x; have he:0 < α:= spanP_pos ..
   obtain ⟨w,hw⟩:= hp
   let v:= stud α x z+α•w.val; have hx:‖v j‖≤ A:=h _ hw j; have ht:|w.val j|≤ R:=w.property j; have hu : |↑((z-Y) j)-(v j/α-w.val j)| ≤ (1/2:ℝ):= by
       have hz:= inBlock X K i x j
       have h': v j=α*z j-x j+α*w.val j:=rfl
       rw [show (↑((z-Y) j):ℝ)-(v j/α-w.val j)=x j/α-Y j from ?_]; · exact abs_le.mpr ⟨hz.1.le,hz.2⟩
       rw [h',Pi.sub_apply,Int.cast_sub]; field_simp; ring
   have hL : (((z-Y) j).natAbs:ℝ)≤ 1+R+A/α:= by
     have hf : |v j/α| ≤ A/α := by rw [abs_div, abs_of_pos he]; exact div_le_div_of_nonneg_right hx he.le -- norm ℝ defeq?
     rw [← signed_norm,Real.norm_eq_abs]; apply (abs_le).2; obtain ⟨hy,hx⟩:= abs_le.mp hu; obtain ⟨ht,hs⟩:=abs_le.mp ht; obtain ⟨hp,hq⟩:= abs_le.mp hf; constructor <;> linarith
   exact Nat.cast_le.mp (hL.trans (Nat.le_ceil _))
lemma nestedP (h:Spatial g A)(hp: reached g x (spanP X K i) R z): z∈ pieceA X K i x A R:= by
    refine mem_image.mpr ⟨z-arcT X K i x,box_test.mpr ⟨?_,?_⟩,sub_add_cancel ..⟩ <;> intro j <;> have h:= extent_p h hp j <;> omega
lemma linkP (h:Spatial g A)(hp:reached g x (spanP X K i) R z): size (z-arcT X K i x)≤ 4*circleP A R (spanP X K i):= by
   unfold Laurent.size; rw [show 4*circleP A R (spanP X K i)=∑ _ : Axis,circleP A R (spanP X K i) by simp [Axis]]
   exact sum_le_sum fun i _=> extent_p h hp i
-- canonical finite sets even if all addresses outside. drop zero roots.
lemma spatialComing (g:Exam D)(hp: HasCompactSupport g.val): ∃ B,0≤ B ∧ Spatial g B:= by
    obtain ⟨M,hM⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hp.isBounded
    exact ⟨max M 0,le_max_right ..,fun t ht i=> (PiLp.norm_apply_le t i).trans (le_trans (by simpa using hM ht) (le_max_left ..))⟩

abbrev Profile (D:ℕ) := {g:Exam D // HasCompactSupport g.val}
lemma reached_finite (g:Profile D) (X:Chain)(k i:ℕ)(x:E4)(R:ℝ): ({z| reached g.val x (spanP X k i) R z}:Set Cover).Finite:= by
    obtain ⟨d,hd,h⟩:=spatialComing g.val g.property; exact (Finset.finite_toSet (pieceA X k i x d R)).subset (fun _ hz=> nestedP h hz)
def blush (g:Profile D)(X:Chain)(k i:ℕ)(x:E4)(R:ℝ):= (reached_finite g X k i x R).toFinset
lemma blush_v {g:Profile D}: z∈blush g X K i x R ↔ reached g.val x (spanP X K i) R z:= Set.Finite.mem_toFinset _
lemma piece_count (k i) : (pieceA X k i x A R).card ≤ (circleP A R (spanP X k i)+circleP A R (spanP X k i)+1)^4:= (card_image_le : _ ≤ (box _).card).trans_eq (Corona.box_size _)
lemma circle_fin {p:ℝ}(h:0≤A)(hp:0≤R)(hv:0<p)(ht:p≤1): p*(circleP A R p) ≤ 2+R+A:= by
    apply le_trans (mul_le_mul_of_nonneg_left (Nat.ceil_lt_add_one (by positivity :0≤1+R+A/p)).le hv.le) _
    calc
      _=p*(2+R)+A:= by field_simp; ring
      _≤2+R+A:= add_le_add_left (mul_le_of_le_one_left (by positivity) ht) _
lemma blush_count {g:Profile D}(h:Spatial g.val A)(hp:0≤A)(hx:0≤R)(ht:spanP X K i≤1):
    (spanP X K i)^4*(↑(blush g X K i x R).card:ℝ) ≤ (2*(2+R+A)+1)^4 := by
   let P:= spanP X K i; have he:0<P:= spanP_pos ..; have hb:(blush g X K i x R).card ≤ _:= (card_le_card (show blush g X K i x R ⊆ pieceA X K i x A R from fun _ ht=>nestedP h (blush_v.mp ht))).trans (piece_count ..)
   refine (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hb) (pow_nonneg he.le 4)).trans ?_
   push_cast; rw [← mul_pow]; apply pow_le_pow_left₀; · unfold circleP; have ht:=spanP_pos X K i; positivity
   nlinarith [circle_fin hp hx he ht]
end tests
end YM.RG08.Plot
