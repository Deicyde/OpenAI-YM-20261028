import YM.Next.ROTATIONS.Constraints
import YM.Next.ROTATIONS.Dyad

/-!
# Evaluated difference bounds and normalization
-/
noncomputable section
namespace YM.Outer
open Function Set Filter MeasureTheory Measure Complex Boundary Probe Table Row Nodes OS Ward Word
open scoped Topology NNReal ENNReal Matrix.Norms.Frobenius BigOperators ContDiff

private lemma earn_credit (m j k : ℕ) (a : ℝ) (ha : a≤0) (q) : Budget (2*a)
    (fun n => credits m j k hiS (halve (fuel a n) q) - credits m j k hiS (halve (2*fuel a n) q)) := by
  by_cases h : k=0
  · subst k
    simp only [credits,halve, tally_width _ _ (fuel_pos ..),tally_width _ _ (mul_pos (a:=(2:ℝ)) (b:=fuel a _) (by norm_num) (fuel_pos ..)), mul_zero,pow_zero,one_mul,mul_one,sub_self]; exact no_budget _
  have H (c : ℝ) (hp : 0<c) : Budget (2*a) (fun n => credits m j k hiS (halve (c*fuel a n) q)) := by
    let P := width c (liftSun q)
    have ht := credit_budget m j k hiS P a 0
    have he n : halve (c*fuel a n) q=bill a n P := by rw [halve,mul_comm,width_mul]; rfl
    simp_rw [fuel0,mul_one] at ht; simp_rw [he]; refine ht.rise ?_
    have hp : (2:ℝ) ≤ (2*k:ℕ) := by exact_mod_cast (show 2≤2*k by omega)
    rw [sub_zero, mul_comm 2 a]; exact mul_le_mul_of_nonpos_left hp ha
  simpa only [one_mul] using (H 1 (by norm_num)).sub (H 2 (by norm_num))
lemma Budget.of_r {x} {f : ℕ→ℝ} (h : Budget x f) : Budget x (fun n => (f n:ℂ)) := h.reduce <|
    .of_forall fun n => by simp
lemma Budget.reals {x} {f : ℕ→ℂ} (h : Budget x f) : Budget x (fun n => (f n).re) := h.reduce (Eventually.of_forall fun _ => Complex.abs_re_le_norm _)

abbrev tube (w : Axis→ℝ) (f : Grouping) (n) (i) (g : Profile) := update (mails w f n) i g


lemma debris_cost (δ : ℝ) (T : TestMap) (i : Axis) (w : Axis→ℝ) (Q : Quest (update w i 0) i (fun _ => false) δ T) (m a q)
    (ha : a≤0) (f : Grouping) (hf : ∀ j,Ends (f j)) (he : ∀ j,j≠i → Reflects false (f j)) :
    Budget (2*a+δ) (fun n => T (tube w f n i (debris m (fuel a n) q))) := by
  let L n := T.toLinearMap (mails w f n) i
  have H : ∀ g : Profile, Far g → Budget δ (fun n => L n g) := by
    intro g h
    let z := update f i g
    have h' : Budget δ (fun n => T (mails (update w i 0) z n)) := by
      apply Q
      · intro j; by_cases ht:j=i
        · subst j; unfold z; rw [update_self]; exact h.1
        rw [show z j=f j from update_of_ne ht ..]; exact hf _
      · simpa only [z,update_self] using h
      · intro j hj; rw [show z j=f j from update_of_ne hj ..]; exact he _ hj
    refine h'.same (Eventually.of_forall fun n => ?_)
    change T _= T _; congr 1; ext1 j; by_cases h:j=i
    · subst j; simp [ z,bill_zero,mails]
    simp [z,h,mails]
  let g j k := width hiS (menu j k)
  let B n j k := credits m j k hiS (halve (fuel a n) q)-credits m j k hiS (halve (2*fuel a n) q)
  have ht n : debris m (fuel a n) q= ∑ j∈Finset.range m,∑ k∈dish m j,B n j k • g j k := by
    unfold debris bake board B g; simp_rw [sub_smul,Finset.sum_sub_distrib]
  change Budget _ (fun n => L n _)
  simp_rw [ht,_root_.map_sum,map_smul]; refine budget_sum _ _ _ fun j _ => budget_sum _ _ _ fun k _ => ?_
  have hx := (earn_credit m j k a ha q).of_r.prod (H (g j k) ((menu_far ..).width _)); exact hx

/-- Algebraic pin of the gap response. All inputs are real parts. -/
lemma budget_lock (x : ℝ) (a b v V r R f g h : ℕ → ℝ)
    (hv : Budget x (fun n => v n-a n)) (hV : Budget x (fun n => V n-4*b n))
    (hr : Budget x (fun n => r n-v n)) (hR : Budget x (fun n => R n-4*V n))
    (hh : ∀ᶠ n in atTop, 0 ≤ f n ∧ g n ≤ 0 ∧ 0≤ h n)
    (he : Budget x (fun n => f n - (a n-b n)))
    (hu : Budget x (fun n => g n - (v n-V n)))
    (hy : Budget x (fun n => h n - (r n-R n))) : Budget x f := by
  -- derive f≤ finite linear expression by linear combinations (avoid coefficient C normalization)
  let k (i : ℕ) := ( |v i-a i| + |V i-4*b i| + |r i-v i| + |R i-4*V i| + |f i-(a i-b i)| + |g i-(v i-V i)| + |h i-(r i-R i)| )
  have hx (g : ℕ → ℝ) (hp : Budget x g) : Budget x (fun n => |g n|) := hp.reduce <| .of_forall fun n => by simp
  have hz : Budget x k := ((((((hx _ hv).add (hx _ hV)).add (hx _ hr)).add (hx _ hR)).add (hx _ he)).add (hx _ hu)).add (hx _ hy)
  apply (hz.times 100).signed (hh.mono fun i hi => hi.1)
  filter_upwards [hh] with n hn; obtain ⟨h1,h2,h3⟩ := hn; change f n ≤ 100*k n
  unfold k; linarith [le_abs_self (v n-a n),neg_le_abs (v n-a n),le_abs_self (V n-4*b n),neg_le_abs (V n-4*b n),le_abs_self (r n-v n),neg_le_abs (r n-v n),le_abs_self (R n-4*V n),neg_le_abs (R n-4*V n),le_abs_self (f n-(a n-b n)),neg_le_abs (f n-(a n-b n)),le_abs_self (g n-(v n-V n)),neg_le_abs (g n-(v n-V n)),le_abs_self (h n-(r n-R n)),neg_le_abs (h n-(r n-R n))]

private lemma halve_mail (w : Axis→ℝ) (a : ℝ) (f : Grouping) (p i q n) : tube w f n i (halve (p*fuel a n) q)=
    mails (update w i a) (update f i (width p (liftSun q))) n := by
  ext1 j; by_cases h : j=i
  · subst j; unfold tube mails; rw [update_self,update_self, update_self, halve,mul_comm, width_mul];rfl
  simp [tube,mails,h]

private lemma valued (i : Axis) (w : Axis→ℝ) (a : ℝ) (Z C U : TestMap) (hh : U=Pmul 2 i Z+C) (k : ℕ) (p : ℝ) (f : Grouping) (r : ℝ) (hc : Ach (update w i a) r C) :
    Budget r (fun n => (U (tube w f n i (halve (p*fuel a n) (k+1)))).re - (p*fuel a n)^2 * (Z (tube w f n i (halve (p*fuel a n) k))).re) := by
  refine (hc (update f i (width p (liftSun (k+1))))).reals.same (Eventually.of_forall fun n => ?_)
  let F j := tube w f n i (halve (p * fuel a n) j)
  have ht : stepAt 2 (F (k+1)) i= update (mails w f n) i ((p*fuel a n)^2 • halve (p*fuel a n) k) := by
    unfold F stepAt tube halve; rw [update_self,update_idem,pump_width,pumped]
  change _ = (U (F (k+1))).re-(p*fuel a n)^2*(Z (F k)).re
  have he : U (F (k+1)) = Complex.ofReal ((p*fuel a n)^2) * Z (F k)+C (F (k+1)) := by
    rw [hh, _root_.add_apply,Pmul_at,ht,Z.map_update_smul]
    rfl
  rw [he,add_re,re_ofReal_mul]; dsimp only; rw [← halve_mail]; linarith

abbrev Zframe (T : TestMap) (k : ℕ) (a) (w) (f) (i) (n) (g : Profile) := (fuel a n)⁻¹^(2*k) * (T (tube w f n i g)).re
abbrev cabin (T : TestMap) (k a w f i p n) := Zframe T k a w f i n (halve (p*fuel a n) k)
lemma heights (i : Axis) (w) (a) (Z C U : TestMap) (hh : U=Pmul 2 i Z+C) (k : ℕ) (p : ℝ) (f r) (hc : Ach (update w i a) r C) :
    Budget ((-a)*(2*(k+1):ℕ)+r) (fun n => cabin U (k+1) a w f i p n-p^2*cabin Z k a w f i p n) := by
  refine (((budget_inv a).pow (2*(k+1))).prod (valued i w a Z C U hh k p f r hc)).same (Eventually.of_forall fun n => ?_)
  have hp := fuel_pos a n
  dsimp only [cabin,Zframe]
  rw [mul_sub]; congr 1
  rw [mul_add, mul_one,pow_add,inv_pow, inv_pow]; field_simp
abbrev hole (T : TestMap) (m k a w f i n) := Zframe T k a w f i n (gap m (fuel a n) k)
lemma rift (i : Axis) (w) (T : TestMap) (x a) (k : ℕ) (ha : a ≤ 0) (hp : Quest (update w i 0) i (fun _ => false) x T) (f : Grouping) (hf : ∀ j,Ends (f j)) (he : ∀ j,j≠i → Reflects false (f j)) (m) :
    Budget (-a*(2*k:ℕ)+(2*a+x))
      (fun n => hole T m k a w f i n - (cabin T k a w f i 1 n - cabin T k a w f i 2 n)) := by
  have hh := (((budget_inv a).pow (2*k)).prod (debris_cost x T i _ hp m a k ha f hf he).reals).neg
  refine hh.same (.of_forall fun n => ?_)
  dsimp only [hole,Zframe,gap,cabin]
  unfold tube; rw [one_mul,T.map_update_sub,T.map_update_sub,sub_re,sub_re]; ring
end YM.Outer
