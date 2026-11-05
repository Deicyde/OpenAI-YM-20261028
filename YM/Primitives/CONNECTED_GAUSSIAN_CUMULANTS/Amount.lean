import YM.Next.FOUNDATIONS.SU2
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Expansion

/-!
# Before the geometric and arity prices: no ordering cost left

Take the norm even *inside* each tree. Keep the sin^child rebates for
steps beyond the first. These estimates need smoothness only to the order
used in each term, authenticity of the expansion will need one more order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open MeasureTheory Filter Set Function Finset Marker
open YM.Multi.Vacuum.Gauss Probe Grove Fused Moment Spin Expansion
open scoped Topology BigOperators Interval
variable {V I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq V]
namespace Charge

def cost (T A : Finset V) (n : ℕ) (f : Parent V) (q : Rows V I J) (v : Probes V I) :=
    report T (‖·‖) n A f q v

def contact (q : Rows V I J) (S : V → Finset I) (i j : V) : ℝ :=
  ∑ a∈S i,∑ b∈S j, |crossed (q i a) (q j b)|
omit [Fintype I] [DecidableEq I] [DecidableEq V] in
lemma contact_nn (q : Rows V I J) (S : V → Finset I) (i j : V) : 0 ≤ contact q S i j :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

def beams (T A : Finset V) (f : Parent V) (E : V → V → ℝ) :=
  ∏ j∈(T \ A), E (f j) j

def tags (T A : Finset V) (f : Parent V) (H : V → ℕ → ℝ) :=
  ∏ i∈T, H i (deg T A f i)

def value (T A : Finset V) (f : Parent V) (q : Rows V I J) (S : V → Finset I)
    (H : V → ℕ → ℝ) (w : V → Row I) := beams T A f (contact q S)*tags T A f H*Real.exp (2* due T q w)

lemma switched {T A : Finset V} {f : Parent V} (H : V → ℕ → ℝ) {j : V} (hj : j∈buds T A f) :
    tags T (insert j A) (cut f j) (bill (bill H (f j)) j)=tags T A f H := by
  have he := Buds.roots hj
  have hl := (mem_sdiff.mp (Buds.kids hj)).2
  have ht : f j≠j := fun hw => hl (hw ▸ he)
  apply prod_congr rfl; intro i _
  rw [degrees hj]
  by_cases hi : i=j
  · subst i; simp only [bill,update_self, update_of_ne ht.symm, ↓reduceIte, if_neg ht.symm,add_zero]
  by_cases he : i=f j
  · subst i; simp only [bill,update_of_ne ht,update_self,↓reduceIte, if_neg ht,add_zero]
  simp only [bill, update_of_ne hi,update_of_ne he,if_neg hi,if_neg he,add_zero]

omit [Fintype I] [DecidableEq I] in
lemma rebates (q : Rows V I J) (S : V → Finset I) {T A : Finset V} {f : Parent V} {j : V}
    (hj : j∈buds T A f) {x : ℝ} (hx : x∈Set.Icc (0:ℝ) high) :
    beams T (insert j A) (cut f j) (contact (path A q x) S) =
    Real.sin x ^ ((buds T A f).card - 1) * beams T (insert j A) (cut f j) (contact q S) := by
  let F := buds T A f
  let U := T \ insert j A
  let p := cut f j
  have he i (hi : i∈U) : contact (path A q x) S (p i) i =
      (if i ∈ F then Real.sin x else 1)*contact q S (p i) i := by
    have hl : i∈(T \ A).erase j := (leaves T A j) ▸ hi
    have hy : i ≠ j := ne_of_mem_erase hl
    have hi' := mem_of_mem_erase hl
    have hz : i ∉ A := (mem_sdiff.mp hi').2
    rw [contact,contact]
    simp_rw [clear, abs_mul]; rw [Finset.mul_sum]; refine sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]; refine sum_congr rfl fun b _ => ?_
    by_cases h₀ : f i ∈ A
    · have hb : i∈F:=mem_filter.mpr ⟨hi',h₀⟩
      rw [if_pos hb,discount,if_neg,abs_of_nonneg (sin_pos hx)];
      exact fun h => hz (h.mp (show p i∈A from by simpa only [p,cut,update_of_ne hy] using h₀))
    have hb : i ∉ F := fun H => h₀ (mem_filter.mp H).2
    rw [if_neg hb,discount,if_pos,abs_one]
    change cut f j i ∈ A ↔ _; simp only [cut, update_of_ne hy,h₀,hz]
  have hw : U.filter (· ∈ F)=F.erase j := by
    ext i; apply Iff.intro
    · intro h; rcases mem_filter.mp h with ⟨hi,he⟩
      have h₁ : i∈(T\A).erase j:=(leaves T A j) ▸ hi
      exact mem_erase.mpr ⟨ne_of_mem_erase h₁,he⟩
    intro h; rcases mem_erase.mp h with ⟨hi,he⟩
    refine mem_filter.mpr ⟨?_,he⟩; unfold U; rw [leaves]; exact mem_erase.mpr ⟨hi,Buds.kids he⟩
  change ∏ i∈U,contact (path A q x) S (p i) i = _
  rw [prod_congr rfl he,prod_mul_distrib,prod_ite,hw]
  simp only [prod_const_one,mul_one,prod_const,card_erase_of_mem (show j∈F from hj)]
  rfl

lemma pay_bud {u : ℕ} (hu : 0<u) : (∫ t in 0..high, Real.cos t * Real.sin t^(u-1)) = (u:ℝ)⁻¹ := by
  have hp : 0<(u:ℝ) := Nat.cast_pos.mpr hu
  let f (x : ℝ) := (u:ℝ)⁻¹ * Real.sin x^u
  have he x : HasDerivAt f (Real.cos x * Real.sin x^(u-1)) x := by
    have H := (((Real.hasDerivAt_sin x).pow u).const_mul (u:ℝ)⁻¹)
    convert! H using 1; rw [← mul_assoc,← mul_assoc,inv_mul_cancel₀ hp.ne',one_mul,mul_comm]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => he x) ((by fun_prop : Continuous (fun t => Real.cos t * Real.sin t^(u-1))).intervalIntegrable _ _)]
  simp [f,high,hu.ne']

lemma report_zero (T : Finset V) (n : ℕ) : ∀ {J : Type} [Fintype J] (A f) (q : Rows V I J) (v : Probes V I)
    (i : V), i∈T → v i=0 → cost T A n f q v=0 := by
  induction n with
  | zero =>
    intro J _ A f q v i hi hx; rw [cost,report]; have he x : values T q v x=0 :=
      Finset.prod_eq_zero hi (by rw [hx]; rfl)
    simp_rw [he,norm_zero]; simp
  | succ n ih =>
    intro J _ A f q v i hi hx
    have he {v : Probes V I} (j : V) (a : I) (hx : v i=0) : marked v j a i=0 := by
      by_cases hh : i=j
      · subst j; rw [marked,update_self,hx]; funext x; rw [hit, fderiv_zero]; rfl
      rw [marked,update_of_ne hh,hx]
    rw [cost, report]; refine sum_eq_zero fun j _ => sum_eq_zero fun a _ => sum_eq_zero fun b _ => ?_
    have ht x := ih (insert j A) (cut f j) (path A q x) (marked (marked v (f j) a) j b) i hi (he _ _ (he _ _ hx))
    unfold cost at ht
    simp_rw [ht,mul_zero]; simp

theorem signed (T : Finset V) (n : ℕ) :
    ∀ {J : Type} [Fintype J] (A : Finset V), A ⊆ T → ∀ (f : Parent V), Good T A f →
      ∀ (q : Rows V I J) (v : Probes V I) (w : V → Row I) (H : V → ℕ → ℝ), base q T w → Valid T n v w H →
        ‖report T id n A f q v‖ ≤ cost T A n f q v := by
  induction n with
  | zero => intro J _ A ha f hf q v w H h hx; rw [cost,report,report]; exact norm_integral_le_integral_norm _
  | succ n ih =>
    intro J _ A ha f hf q v w H h hx; rw [cost,report,report]
    apply le_trans (norm_sum_le ..) (sum_le_sum fun j hj => le_trans (norm_sum_le ..) (sum_le_sum fun a _ =>
      le_trans (norm_sum_le ..) (sum_le_sum fun b _ => le_trans (intervalIntegral.norm_integral_le_integral_norm high_pos.le) ?_)))
    let B := insert j A; let p := cut f j; let i := f j; let u := marked (marked v i a) j b; let F := bill (bill H i) j
    have he := Buds.kids hj
    have hh : i∈A := Buds.roots hj
    have hv : B ⊆ T := Finset.insert_subset (mem_sdiff.mp he).1 ha
    have hp : Good T B p:= hf.cut_at he
    have hw : Valid T n u w F := hx.double (by intro hy; exact (mem_sdiff.mp he).2 (hy ▸ hh)) a b
    have hc := report_priceable T B id continuous_id (fun _=>le_rfl) n hp A q u w F hv h hw i j a b
    have hk := report_priceable T B (‖·‖) continuous_norm (fun x=> (norm_norm x).le) n hp A q u w F hv h hw i j a b
    apply intervalIntegral.integral_mono_on high_pos.le hc.norm hk
    intro x _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ih B hv p hp (path A q x) u w F (keeps A q h x) hw)
      (norm_nonneg _)

/-- A real tree bound, not a connected partition count. Pay once per edge.
The recursively integrated terms are absolute terminal moment bounds, with
no subtraction inside the norm. In particular order rebate integrates to
one for each tree even at coincident probes. -/
theorem tree_cost (T : Finset V) (n : ℕ) :
    ∀ {J : Type} [Fintype J] (A : Finset V), A ⊆ T → (T \ A).card=n →
      ∀ f : Parent V, Good T A f →
      ∀ (q : Rows V I J) (v : Probes V I) (S : V → Finset I)
        (w : V → Row I) (H : V → ℕ → ℝ), base q T w → Valid T n v w H →
          (∀ i∈T,Reads (S i) (v i)) →
        cost T A n f q v ≤ value T A f q S H w := by
  induction n with
  | zero =>
    intro J _ A ha hn f hf q v S w H h hx hr
    obtain rfl := Finset.Subset.antisymm ha (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hn))
    rw [cost,report,value,beams,tags]; simpa [deg] using (revenues h hx (Finset.Subset.refl A)).2
  | succ n ih =>
    intro J _ A ha hn f hf q v S w H h hx hr
    let F := buds T A f
    let P := path A q
    let N := value T A f q S H w
    let r := (buds T A f).card
    have he : F.Nonempty := hf.buds (card_pos.mp (hn.symm ▸ Nat.succ_pos _))
    have hu : 0 < r := card_pos.mpr he
    have hp : 0 < (r:ℝ) := Nat.cast_pos.mpr hu
    rw [cost,report]
    apply le_trans _ (show ∑ _j∈F,(r:ℝ)⁻¹*N ≤ N from ?_)
    swap
    · unfold r; simp only [sum_const,nsmul_eq_mul]
      change (r:ℝ)*((r:ℝ)⁻¹*N) ≤ N
      rw [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul]
    refine sum_le_sum fun j hj => ?_
    let B := insert j A; let p := cut f j; let i := f j; let W (a b : I) := marked (marked v i a) j b
    let U (a b : I) (x) := ‖currency q x i a j b‖ * cost T B n p (P x) (W a b)
    let E := bill (bill H i) j
    have he := Buds.kids hj
    obtain ⟨he₁,he₂⟩ := mem_sdiff.mp he
    have hf : Good T B p := hf.cut_at he
    have hy : B ⊆ T := Finset.insert_subset he₁ ha
    have h0 : (T\B).card=n := by unfold B; rw [leaves,card_erase_of_mem he,hn]; simp
    have hh : i∈A := Buds.roots hj
    have hij : i≠j := fun h => he₂ (h ▸ hh)
    have he₃ : i∈T := ha hh
    have hd k (hk : k∈T) := hx.look (Nat.succ_pos _) k hk
    have hv a b : Valid T n (W a b) w E := hx.double hij a b
    have hF a b k (hk : k∈T) : Reads (S k) (W a b k) := by
      unfold W marked
      by_cases he : k=j
      · rw [he,update_self,update_of_ne hij.symm]; exact Reads.hits (hr _ he₁) (hd _ he₁) _
      rw [update_of_ne he]
      by_cases he' : k=i
      · rw [he',update_self]; exact Reads.hits (hr _ he₃) (hd _ he₃) _
      rw [update_of_ne he']; exact hr _ hk
    have hz (a b : I) (ha' : a ∉ S i ∨ b ∉ S j) : U a b=0 := by
      funext x; unfold U; obtain hl|hl := ha'
      · have he : W a b i=0 := by unfold W marked; rw [update_of_ne hij,update_self,Reads.outside (hr _ he₃) (hd _ he₃) a hl]
        rw [report_zero T n _ _ _ _ i he₃ he,mul_zero]; rfl
      have he : W a b j=0 := by unfold W marked; rw [update_self,update_of_ne hij.symm,Reads.outside (hr _ he₁) (hd _ he₁) b hl]
      rw [report_zero T n _ _ _ _ j he₁ he,mul_zero]; rfl
    let M := beams T B p (contact q S)*tags T A f H*Real.exp (2*due T q w)
    have hN : N=contact q S i j * M := by
      unfold N M value beams
      rw [← mul_prod_erase (T \ A) (fun j => contact q S (f j) j) he]
      unfold B; rw [leaves]
      have hx : ∏ k∈(T\A).erase j,contact q S (f k) k=∏ k∈(T\A).erase j,contact q S (p k) k :=
        prod_congr rfl fun k hk => by rw [show p k=f k from update_of_ne (ne_of_mem_erase hk) ..]
      rw [hx]; unfold i; ring
    let c a b := |crossed (q i a) (q j b)|
    have ht a b : (∫ x in 0..high,U a b x) ≤ (r:ℝ)⁻¹ * (c a b*M) := by
      let τ x := Real.cos x * Real.sin x^(r-1)
      have hd : IntervalIntegrable (U a b) volume 0 high :=
        report_priceable T B _ continuous_norm (fun x=> (norm_norm x).le) n hf A q _ w _ hy h (hv a b) i j a b
      have hτ : IntervalIntegrable (fun x => τ x * (c a b*M)) volume 0 high :=
        (show Continuous _ by unfold τ; fun_prop).intervalIntegrable _ _
      apply le_trans _ (Eq.le (show (∫ x in 0..high,τ x * (c a b*M)) = _ from
        (intervalIntegral.integral_mul_const ..).trans (by rw [show (∫ x in 0..high,τ x)=_ from pay_bud hu])))
      apply intervalIntegral.integral_mono_on high_pos.le hd hτ
      intro x hz
      apply le_trans (mul_le_mul_of_nonneg_left (ih B hy h0 p hf (P x) _ S w E (keeps A q h x) (hv a b) (hF a b)) (norm_nonneg _))
      have hx : ‖currency q x i a j b‖=Real.cos x * c a b := by unfold currency c; rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (cos_pos hz)]
      rw [hx,value]
      unfold B p P E; rw [rebates q S hj hz,same_charge,switched H hj]
      exact le_of_eq (by unfold τ r M p B; ring)
    change (∑ a,∑ b,∫ x in 0..high,U a b x) ≤ _
    have h1 (a) : ∑ b, (∫ x in 0..high,U a b x) = ∑ b∈S j,(∫ x in 0..high,U a b x) := by
      symm; refine sum_subset (Finset.subset_univ _) fun b _ hb => ?_
      rw [hz a b (.inr hb)]; simp
    simp_rw [h1]
    rw [← sum_subset (Finset.subset_univ (S i))]
    · apply (sum_le_sum (fun a _ => sum_le_sum (fun b _ => ht a b))).trans
      rw [hN]; unfold contact; simp_rw [Finset.sum_mul,Finset.mul_sum]
      exact le_rfl
    intro a ha' he'; exact sum_eq_zero fun b _ => by rw [hz a b (.inl he')]; simp
end Charge
end YM.Primitives.GCC
