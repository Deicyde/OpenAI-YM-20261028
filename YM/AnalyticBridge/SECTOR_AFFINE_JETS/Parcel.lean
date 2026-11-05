import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Directions
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Point
import YM.Next.EXTRACTION.Basis


/-!
# Matrices on Pointwise costs. Convert marked costs to the E direction convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset

open Filter Function Lattice Wilson RG Precision Pressure Tree
open YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.FreeResolvent (Mark Bundle native Cost)
open YM.FreeResolvent.TestD Matrix
open YM.Push.Uniform (bolt)
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side}
variable {n k : ℕ} {C M K σ a s d t : ℝ}
variable {ι κ : Type} [Fintype ι] [Fintype κ]
    {p : ι → Site c} {q : κ → Site c} {V : Config G c} {B : PriceCoords G c}
    {H J : PriceCoords G c → ι → ℝ} {A : PriceCoords G c → Matrix κ ι ℝ}

/-- Only pointwise per output. -/
def Parcel (B : PriceCoords G c) (p : ι → Site c) (σ : ℝ) (n : ℕ) (H : PriceCoords G c → ι → ℝ) (C : ℝ) :=
  ∀ i, Point B (p i) σ n (fun z => H z i) C

namespace Parcel
lemma smooth (h : Parcel B p σ n H C) : ContDiffAt ℝ n H B := contDiffAt_pi.mpr fun i => (h i).smooth
section
omit [Fintype ι]
lemma mono (h : Parcel B p σ n H C) (hσ : s ≤ σ) (hm : C ≤ M) : Parcel B p s n H M :=
  fun i => (h i).mono hσ hm
lemma glue (h : Parcel B p σ n H C) (he : H =ᶠ[𝓝 B] J) : Parcel B p σ n J C := fun i => (h i).germ
  (he.mono fun _ hx => congr_fun hx i)
lemma nonnegated (h : Parcel B p σ n H C) : Parcel B p σ n (-H) C := fun i => (h i).neg
lemma add (h : Parcel B p σ n H C) (h' : Parcel B p σ n J M) : Parcel B p σ n (H+J) (C+M) := fun i => (h i).add (h' i)

end

/- Embed in dummy Unit column to apply row-rate estimates on
multiplication. We don't assert any Mark.bill on that column. -/
private def col (H : ι → ℝ) : Matrix ι Unit ℝ := Matrix.of fun i _ => H i
private def insertCol : (ι → ℝ) →L[ℝ] Matrix ι Unit ℝ := LinearMap.toContinuousLinearMap
  ({ toFun := col, map_smul' := fun _ _ => rfl,map_add' := fun _ _ => rfl }: (ι → ℝ) →ₗ[ℝ] Matrix ι Unit ℝ)
private def dull (c : Side) (_ : Unit) : Site c := 0
private def enter (H : PriceCoords G c → ι → ℝ) := fun y => Parcel.col (H y)
private lemma col_smooth (h : ContDiffAt ℝ n H B) : ContDiffAt ℝ n (enter H) B :=
  (show ContDiffAt ℝ n ((@insertCol ι _) ∘ H) B from (ContDiffAt.comp (f:=H) (g:=(insertCol : (ι → ℝ) →L[ℝ] Matrix ι Unit ℝ)) B (ContinuousLinearMap.contDiff _).contDiffAt h))
private lemma dummy {l : List (Coord G c)} (h : ContDiffAt ℝ l.length (enter H) B) (i : ι) :
    (marks G c σ).pay l (p i)*(∑ j : Unit, (native c).weight 0 (p i) (dull c j)*|jet bolt (enter H) l B i j|) =
    (marks G c σ).pay l (p i)*‖jet bolt (fun y => H y i) l B‖ := by simp only [Cost.weight_zero,one_mul,Fintype.sum_unique, ← entry bolt l h]; rfl
private lemma rate (h : Parcel B p σ n H C) (l : List (Coord G c)) (hl : l.length ≤ n) :
    Mark.Rates (marks G c σ) (native c) p (dull c) l 0 C (jet bolt (enter H) l B) := by
  constructor; intro i; rw [dummy (smooth_of_le (col_smooth h.smooth) hl)]; exact (h i).bound l hl
private lemma flatten (h : ContDiffAt ℝ n (enter H) B)
    (hp : ∀ l : List (Coord G c), l.length ≤ n →
      Mark.Rates (marks G c σ) (native c) p (dull c) l 0 C (jet bolt (enter H) l B)) : Parcel B p σ n H C := by
  intro i; refine ⟨(evaluate i ()).contDiff.contDiffAt.comp B h,fun l hl => ?_⟩
  have ht := (hp l hl).rows i; rw [dummy (smooth_of_le h hl)] at ht; exact ht
private lemma rate_sum {ι μ θ X τ : Type} [Fintype μ] {P : Mark τ X} {a : ι → X} {b : μ → X} {D : Cost X}
    {T : Finset θ} {l : List τ} {f : θ → Matrix ι μ ℝ} {m : θ → ℝ} (h : ∀ i∈T, Mark.Rates P D a b l σ (m i) (f i)) :
      Mark.Rates P D a b l σ (∑ i∈T, m i) (∑ i∈T, f i) := by
  induction T using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact Mark.Rates.zero le_rfl
  | @insert i T hT ih => rw [Finset.sum_insert hT,Finset.sum_insert hT]; exact (h i (by simp)).add (ih fun i hi => h i (by simp [hi]))
lemma deliver (h : Parcel B p d n H C) (hC : 0 ≤ C) (h' : Polar B q p A n σ M)
    (hm : 0 ≤ M) (hd : 0 ≤ d) (he : d ≤ σ) (ht : n*d ≤ σ) :
    Parcel B q d n (fun y => A y *ᵥ H y) ((2:ℝ)^n * (C*M)) := by
  apply flatten
  all_goals rw [show enter (fun y => A y *ᵥ H y) = fun y => A y * enter H y from rfl]
  · exact prod_smooth h'.smooth (col_smooth h.smooth)
  intro l hl
  rw [jet_mul _ _ (smooth_of_le h'.smooth hl) (smooth_of_le (col_smooth h.smooth) hl)]
  have hh (x : Masks l) := h.rate (hi l x) ((len_high l x).trans hl)
  have hx := h'.toBundle he
  refine Mark.Rates.mono  (rate_sum (m:=fun _=>C*M) ?_) le_rfl ?_
  · intro i _
    have hy := (hx.bound (lo l i) ((len_low l i).trans hl)).row.mul
      (Mark.position_move _ _ hd) zero_le_one (le_refl (0:ℝ))
      (show 0+(hi l i).length*d ≤ σ by
        rw [zero_add]; exact (mul_le_mul_of_nonneg_right (by exact_mod_cast (len_high l i).trans hl) hd).trans ht)
      (fun x => (marks G c d).pay_masks l i x) (hh i) hC
    simpa only [one_pow, one_mul] using hy
  rw [Finset.sum_const,Finset.card_univ,FreeResolvent.TestD.card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  gcongr; norm_num

lemma activated_scale (hH : Parcel (G:=G) 0 p σ n (fun y => H (t • y)) C)
    (hσ : 0<σ) (ht : 0<t) (power : ℕ) (hc : 0 ≤ C) :
    let Q := H ∘ reader G c
    ContDiffAt ℝ n Q 0 ∧ ∀ (o : Site c) (l : List (Directions G c)), l.length ≤ n → Afford t power o l →
      ∀ i : ι, let r := Mark.hill (native c) o power (p i)
      (r^l.length)⁻¹ *|jet id Q l 0 i| ≤ activation G n power σ*C := by
  intro Q
  let H' := fun y => H (t • y); let F := enter H'
  let Z := t⁻¹ • reader G c
  have he : Q=H' ∘ Z := funext fun i => by
    change H _=H (t • t⁻¹ • reader G c i); rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
  have hs : ContDiffAt ℝ n H' (Z 0) := by rw [map_zero]; exact hH.smooth
  have hg : ContDiffAt ℝ n Q 0 := he ▸ hs.comp _ Z.contDiff.contDiffAt
  have hf : ContDiffAt ℝ n F (Z 0) := col_smooth hs
  refine ⟨hg,?_⟩
  intro o l hl ha i r
  let m := Mark.radial (Directions G c) (native c) o power
  have hm : jet id (fun y => col (Q y)) l 0 = jet Z F l 0 := by
    rw [he]; unfold jet
    change iteratedFDeriv ℝ l.length (F ∘ Z) _ _ = _
    rw [Push.Uniform.iter_lin_at (smooth_of_le hf hl),map_zero]; rfl
  have hx (j) (hj : j∈l) (w : Coord G c) : ‖Z j w‖ ≤ 1*Mark.hill (native c) o power (coordRoot w) := by
    have hi := ha _ hj w.1
    have he : |j w.1 w.2| ≤ ‖j w.1‖ := by
      rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ (j w.1) w.2]; simpa using
        abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ w.2) (j w.1)
    rw [one_mul]
    change ‖t⁻¹ • ((j w.1 w.2):ℝ)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le]; calc
      _ ≤ t⁻¹ * (t*_) := mul_le_mul_of_nonneg_left (he.trans hi) (inv_pos.mpr ht).le
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]
  let s := σ/2; have ht' : 0<s := half_pos hσ
  have hp (w : Fin l.length → Coord G c) := hH.rate (List.ofFn w) (by rwa [List.length_ofFn])
  have hEq : (fun i : Coord G c => Pi.single i (1:ℝ))=bolt := by
    funext i j
    simp only [bolt,Pi.single_apply]; congr!
  have hJ := (Mark.meter_rows (ι:=ι) (b:=dull c) (p:=coordRoot (G:=G) (c:=c)) Z (x:=0) (a:=p) (d:=σ) (l:=l) (F:=F) (γ:=0) (fun w => hEq.symm ▸ hp w) hc zero_le_one hx ht' (le_of_eq (by unfold s; ring)) (param_volume G c ht')).rows i
  rw [← hm, Mark.payment] at hJ
  have H1 : jet id (fun y => col (Q y)) l 0=col (jet id Q l 0) := jet_linear _ _ insertCol (smooth_of_le hg hl)
  rw [H1] at hJ
  simp only [col,Matrix.of_apply,Cost.weight_zero,one_mul,Fintype.sum_unique] at hJ
  refine hJ.trans ?_
  rw [← mul_assoc, ← mul_pow]; gcongr
  exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (param_pos ..) (Mark.poly_le _ ht')) hl
end Parcel

lemma polar_compress (h : Polar (G:=G) 0 q p A n σ M) (ht : 0 ≤ t) (hu : t ≤ 1) :
    Polar (G:=G) 0 q p (fun y => A (t • y)) n σ M := by
  let L := t • ContinuousLinearMap.id ℝ (PriceCoords G c)
  have he : ContDiffAt ℝ n A (L 0) := by rw [map_zero]; exact h.smooth
  change Polar _ _ _ (A ∘ L) _ _ _
  refine ⟨he.comp _ L.contDiff.contDiffAt, fun l hl => ?_⟩
  have hj : jet bolt (A ∘ L) l 0 = t^l.length • jet bolt A l 0 := by
    unfold jet
    rw [Push.Uniform.iter_lin_at (smooth_of_le he hl),map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ l.length A _ (fun i => (fun _ => t) i • (bolt ∘ l.get) i) = _
    rw [ContinuousMultilinearMap.map_smul_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [hj]; apply (h.bound l hl).abs_le
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul,abs_mul, abs_of_nonneg (pow_nonneg ht _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ht hu)
end YM.AnalyticBridge.SectorAffine.Offset
