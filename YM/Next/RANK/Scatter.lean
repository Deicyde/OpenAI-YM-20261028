import YM.Next.RANK.EntryWord

/-!
# Anchor currency to point hit

Independent of period and shape; loses one support exponent test. Pay polynomial
volume of native cover. Use also for marked root with bounded multiplicities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Thirst
open Function Filter Lattice Wilson RG Finset Relation Corona
open scoped Classical BigOperators Topology

variable {n : Side} {ι : Type*}

lemma rooms (q : ℕ) (_ : 0<q) (X : Support n) (he : X.Nonempty) : 1≤coverNumber q X := by
  have h := pays X q; have hs:=Finset.card_pos.mpr he
  cases hx : coverNumber q X with
  | zero => rw [hx,zero_mul] at h; omega
  | succ h => omega

lemma book_site {a b : Site n} (q : ℕ) (hq : 0<q) (X : Support n) (ha : a ∈ X) (hb : b ∈ X) :
    separation a b /(8*q) ≤ coverNumber q X := by
  have ht:= extent X q ha hb
  let d:=coverNumber q X
  have hi : 1≤d:= rooms q hq X ⟨_,ha⟩
  have h : separation a b ≤ d*(8*q) := by dsimp only [d] at *; nlinarith only [ht,hi,hq]
  exact (Nat.div_le_div_right h).trans (by rw [Nat.mul_div_cancel]; positivity)

def welter (v : ℕ) : ℝ := ((v+1:ℝ)^4)*Real.exp (-(v:ℝ))

lemma fel : Summable welter := by
  let f:=fun v : ℕ => Real.exp (-((v:ℝ)/2))
  have h : Summable f := by
    have h₀ : |Real.exp (-(1/2:ℝ))| < 1:= by rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_lt_one_iff.mpr (by norm_num)
    refine (summable_geometric_of_abs_lt_one h₀).congr fun i => ?_
    rw [← Real.exp_nat_mul]; unfold f; congr 1; ring
  have ht : ∀ᶠ v in atTop, welter v ≤ f v := by
    have ha : (fun x : ℝ => x^4) =o[atTop] (fun x=> Real.exp (1/2*x)) := isLittleO_pow_exp_pos_mul_atTop _ (by norm_num)
    have hb : Tendsto (fun i : ℕ=> (i+1:ℝ)) atTop atTop := (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have hg := (ha.comp_tendsto hb).def (Real.exp_pos (-1/2))
    filter_upwards [hg] with i hi
    unfold welter; refine (mul_le_mul_of_nonneg_right (show _ ≤ Real.exp (-1/2)*Real.exp (1/2*((i:ℝ)+1)) from ?_) (Real.exp_pos _).le).trans ?_
    · change ‖((i+1:ℝ)^4:ℝ)‖≤_ at hi; simpa only [Function.comp_apply, Real.norm_of_nonneg (by positivity : 0 ≤ (i+1:ℝ)^4), Real.norm_of_nonneg (Real.exp_pos _).le] using! hi
    apply le_of_eq; rw [← Real.exp_add,← Real.exp_add]; unfold f; congr 1; ring
  refine Summable.of_norm_bounded_eventually_nat h <| ht.mono fun i hi => ?_
  rw [Real.norm_of_nonneg (by unfold welter; positivity)]; exact hi

def wilt (q : ℕ) : ℝ := (33*(q:ℝ))^4*∑' i, welter i
lemma wilty (q : ℕ) : 0≤wilt q := mul_nonneg (by positivity) (tsum_nonneg fun i=> by unfold welter; positivity)

lemma range_wilt (b : Site n) (q : ℕ) (hq : 0<q) :
    ∑ i : Site n,Real.exp (-((separation i b/(8*q) : ℕ):ℝ)) ≤ wilt q := by
  let v := 8*q; have hv : 0<v:= Nat.mul_pos (by decide) hq
  let A (i : Site n) : ℕ := separation i b/v
  let f (b : ℕ) := Real.exp (-(b:ℝ))
  let Q : Support n:= univ
  let Y:= Q.image A
  change ∑ i∈Q, f (A i) ≤ _
  let F j := Q.filter fun i=> A i=j
  have h : ∑ i∈ Q,f (A i)=∑ j∈Y, (↑(F j).card:ℝ)*f j := by
    rw [← sum_fiberwise_of_maps_to (f:=fun i => f (A i)) (g:=A) (s:=Q) (t:=Y) (fun i hi => mem_image_of_mem A hi)]
    apply sum_congr rfl; intro i _
    calc
      _ = ∑ _∈F i,f i := by apply sum_congr rfl; intro j hj; rw [(mem_filter.mp hj).2]
      _ = _ := by simp
  have he (j) : (F j).card ≤ ((j+1)*33*q)^4 := by
    let v':=(j+1)*v
    have hh : F j⊆ halo v' {b} := by
      intro i hi; obtain ⟨_,hz⟩:=mem_filter.mp hi
      have hx : separation i b/(8*q)< j+1 := hz.symm ▸ Nat.lt_succ_self j
      rw [Nat.div_lt_iff_lt_mul hv] at hx; exact halo_spec.mpr ⟨_,by simp,(separation_comm b i).trans_le hx.le⟩
    apply ((card_le_card hh).trans (halo_size {b} _)).trans
    rw [card_singleton,one_mul]; gcongr; dsimp [v',v]; nlinarith
  rw [h]; calc
    _ ≤ ∑ j∈Y, (33*(q:ℝ))^4*welter j := by
      refine sum_le_sum fun i hi=>?_ ; apply (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (he i)) (show 0≤f i from (Real.exp_pos _).le)).trans
      dsimp only [welter,f]; push_cast; apply le_of_eq; ring
    _ ≤ _ := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (fel.sum_le_tsum Y (fun i _=> by unfold welter; positivity)) (by positivity)

def debt (q : ℕ) (z : ℝ) (X : Support n) := Real.exp (z* coverNumber q X)
lemma posit (q : ℕ) (z : ℝ) (X : Support n) : 0 < debt q z X:=Real.exp_pos _

lemma add_debt (q : ℕ) (a b : ℝ) (X : Support n) : debt q (a+b) X=debt q a X*debt q b X := by simp only [debt,add_mul,Real.exp_add]
lemma debt_mono (q : ℕ) {a b : ℝ} (h : a≤b) (X : Support n) : debt q a X≤debt q b X:=by unfold debt; gcongr

def pay {ι : Type*} (f : ι→ℝ) (p : ι→Prop) := fun i=> if p i then f i else 0

/-- Counting currency with arbitrary languages (can be valuation from a gauge pencil).
 `Reserve` all unmasked inputs first on their good domains. -/
def Point (X : ι → Support n) (q : ℕ) (E : ι → ℝ) (z : ℝ) (p : ι→Prop) (t : ℝ) := SumBudget (pay (fun i=> E i*debt q z (X i)) p) t
def Incur (X : ι → Support n) (q : ℕ) (E : ι → ℝ) (z : ℝ) (t : ℝ) := ∀ x : Site n,Point X q E z (fun i=>x∈X i) t

lemma circle {ι : Type} (X : ι → Support n) (q : ℕ) (ho : ι→Site n) (hn : ∀ i, ho i ∈ X i) (p : ℝ) (d : ι → ℝ) (hp : 0<q) (hd : ∀ i,0 ≤ d i)
    (r : ℝ) (hr : ∀ s : Site n, Point X q d (p+1) (fun i => ho i=s) r) : Incur X q d p (wilt q * r) := by
  let f i:= d i*debt q (p+1) (X i)
  have hx s i : pay f (fun i => ho i=s) i=if ho i=s then f i else 0 := by unfold pay; split_ifs<;>rfl
  have ht i : 0≤f i:=mul_nonneg (hd _) (posit ..|>.le)
  intro s
  let g:= pay (fun i=> d i*debt q p (X i)) (fun i=> s∈X i)
  let a (x : Site n):=Real.exp (-((separation x s/(8*q):ℕ):ℝ))
  have hf i: 0≤g i:= by unfold g pay; split; exact mul_nonneg (hd _) (posit ..|>.le); exact le_rfl
  have hy : 0≤r:= le_trans (tsum_nonneg (hr s).1) (hr s).2.2
  have he (F : Finset ι) : ∑ i∈F,g i ≤ wilt q*r := by
    calc
      _ ≤ ∑ i∈F,∑ x : Site n,a x*pay f (fun k => ho k=x) i := by
        refine sum_le_sum fun i _=> ?_
        refine le_trans ?_ (single_le_sum (fun x _=> mul_nonneg (show 0≤a x from Real.exp_pos _|>.le) ((hr x).1 i)) (mem_univ (ho i)))
        rw [hx,if_pos rfl]; by_cases hh : s∈X i
        · unfold g pay;simp only [hh,↓reduceIte]; unfold a f; rw [add_debt, mul_left_comm _ (d i), mul_left_comm _ (debt q p _), show debt q 1 (X i)=_ from (show debt q 1 (X i)=Real.exp (1*coverNumber q (X i)) from rfl), one_mul,← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (posit ..|>.le) (Real.one_le_exp ?_)) (hd i)
          have hg : (((separation (ho i) s)/(8*q):ℕ):ℝ)≤coverNumber q (X i) := by exact_mod_cast book_site q hp (X i) (hn i) hh
          linarith only [hg]
        apply le_trans (le_of_eq (show g i = 0 from if_neg hh)); exact mul_nonneg (Real.exp_pos _).le (ht _)
      _ ≤ ∑ x : Site n, a x*r := by
        rw [sum_comm]; refine sum_le_sum fun i _=> ?_; rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (((hr i).2.1.sum_le_tsum F (fun k _=> (hr i).1 k)).trans (hr i).2.2) (Real.exp_pos _).le
      _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (range_wilt s q hp) hy
  have ht:= summable_of_sum_le hf he
  exact ⟨hf,ht,ht.tsum_le_of_sum_le he⟩
end YM.Next.Rank.Thirst
