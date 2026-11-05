import YM.Bid.Craft
import YM.Corona.Spend
import YM.Laurent.Art
import YM.Next.BOUNDARY.Heights
import YM.Next.EXTRACTION.Relay
import YM.Next.FOUNDATIONS.SU2
import YM.Work.A15
import YM.Work.I01

/-!
# Connected-cover reserves in a many-marker budget (E eqs.1shape, JMmq, JshapeM)

On the actual four-dimensional native tori, at any volume. Address types need
not even be countable. Marker sets are keyed by **name**, not by site. Prices
are nonnegative sums (with summability), not analytic continuations of signed
sums. No claim of any source trajectory / exact gas identity here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Filter Function Lattice RG Wilson Marker Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

namespace Budget
variable {ι α : Type*} {f g : ι → ℝ} {b c : ℝ}

theorem certify (hf : ∀ i, 0 ≤ f i) (h : ∀ t : Finset ι, ∑ i∈t, f i ≤ b) : SumBudget f b :=
  let hs := summable_of_sum_le hf h
  ⟨hf,hs,hs.tsum_le_of_sum_le h⟩

theorem cap (h : SumBudget f b) (s : Finset ι) : ∑ i∈s, f i ≤ b :=
  (h.2.1.sum_le_tsum s fun i _ => h.1 i).trans h.2.2

theorem mono (h : SumBudget f b) (hg : ∀ i, 0 ≤ g i) (he : ∀ i, g i ≤ f i) (hb : b≤c) : SumBudget g c :=
  certify hg fun t => ((sum_le_sum fun i _ => he i).trans (cap h t)).trans hb

theorem scale (h : SumBudget f b) (hc : 0≤c) : SumBudget (fun i => c*f i) (c*b) :=
  certify (fun i => mul_nonneg hc (h.1 i)) fun s => by
    rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (cap h s) hc

theorem plus (h : SumBudget f b) (h' : SumBudget g c) : SumBudget (fun i => f i + g i) (b+c) :=
  certify (fun i => add_nonneg (h.1 i) (h'.1 i)) fun s => by
    rw [sum_add_distrib]; exact add_le_add (cap h s) (cap h' s)

theorem pull_le {g : α → ℝ} {q : ι → α} {p : ι → Prop} (h : SumBudget g b)
    (hf : ∀ i, 0 ≤ f i) (hs : ∀ i, f i ≠ 0 → p i) (hh : Set.InjOn q {i | p i})
    (he : ∀ i, p i → f i ≤ g (q i)) : SumBudget f b := by
  apply certify hf; intro t
  let T := t.filter p
  calc
    _ = ∑ i∈T, f i := Eq.symm <| sum_subset (filter_subset ..) fun i hi hx => by
      by_contra H; exact hx (mem_filter.mpr ⟨hi,hs i H⟩)
    _ ≤ ∑ i∈T, g (q i) := sum_le_sum fun i hi => he i (mem_filter.mp hi).2
    _ = ∑ j∈T.image q, g j := (sum_image (fun _ hj _ hk h => hh (mem_filter.mp hj).2 (mem_filter.mp hk).2 h)).symm
    _ ≤ _ := cap h _

theorem zero (hb : 0 ≤ b) : SumBudget (fun _ : ι => (0 : ℝ)) b := by
  apply certify (by simp); simpa

end Budget

variable {V ι : Type*} {m n : Side}

/-- Marker-rooted cover budget. `f` excludes the displayed exponential, but
can already include all marker tolls and tests on the name set of an address. -/
def Rooted (mode : ι → Finset V) (X : ι → Support n) (M : ℕ) (a : ℝ) (f : ι → ℝ) (c : ℝ) :=
    ∀ s : V, SumBudget (fun i => if s ∈ mode i then Real.exp (a*coverNumber M (X i)) * f i else 0) c

namespace Rooted
variable {M : ℕ} {a b c d : ℝ} {mode : ι → Finset V} {X : ι → Support n} {f g : ι → ℝ}

theorem cap (h : Rooted mode X M a f b) (v : V) (s : Finset ι) (hs : ∀ i∈s, v∈mode i) :
    ∑ i∈s, Real.exp (a*coverNumber M (X i)) * f i ≤ b := by
  refine Eq.trans_le ?_ (Budget.cap (h v) s)
  exact sum_congr rfl (fun i hi => (if_pos (hs i hi)).symm)

theorem mono (h : Rooted mode X M a f b) (hg : ∀ i, 0 ≤ g i) (he : ∀ i, g i ≤ f i) (hd : d ≤ a)
    (hc : b ≤ c) : Rooted mode X M d g c := by
  intro s; refine Budget.mono (h s) (fun i => ?_) (fun i => ?_) hc
  · split <;> first | exact mul_nonneg (Real.exp_pos _).le (hg i) | exact le_rfl
  split_ifs; rotate_left
  · exact le_rfl
  exact mul_le_mul (Real.exp_le_exp.mpr (by gcongr)) (he i) (hg i) (Real.exp_pos _).le

theorem add (h : Rooted mode X M a f b) (hg : Rooted mode X M a g c) : Rooted mode X M a (fun i => f i+g i) (b+c) := by
  intro s
  convert Budget.plus (h s) (hg s) using 1
  funext i; split_ifs <;> ring

end Rooted

/-- At a given projection count all simultaneous markers, including
alternative names and zero inputs. Use separately at each level in use. -/
def Occupancy [Fintype V] (o : V → Site n) (μ : ℕ) := ∀ y : Site n, (univ.filter fun i => o i = y).card ≤ μ

namespace Occupancy
variable [Fintype V] {o : V → Site n} {μ : ℕ}

theorem card (h : Occupancy o μ) (s : Finset V) : s.card ≤ (s.image o).card * μ := by
  classical
  calc
    _ = ∑ y ∈ s.image o, (s.filter fun i => o i = y).card := by
      simp only [card_filter, sum_comm (s := s.image o)]
      rw [show s.card = ∑ _ ∈ s, (1:ℕ) by simp]; refine sum_congr rfl fun i hi => ?_
      simp [show ∃ a∈s, o a=o i from ⟨i,hi,rfl⟩]
    _ ≤ ∑ _ ∈ s.image o, μ := sum_le_sum fun i _ => (card_le_card (filter_subset_filter _ (subset_univ _))).trans (h i)
    _ = _ := by simp

theorem total (h : Occupancy o μ) : Fintype.card V ≤ Fintype.card (Site n)*μ := by
  simpa only [card_univ] using (h.card univ).trans (Nat.mul_le_mul_right _ (card_le_card (subset_univ _)))

theorem of_injective (h : Function.Injective o) : Occupancy o 1 := by
  intro y; apply card_le_one.mpr; intro i hi j hj
  exact h ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)

theorem weighted (h : Occupancy o μ) (f : Site n → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ∑ i, f (o i) ≤ μ * ∑ y, f y := by
  calc
    _ = ∑ i, ∑ y : Site n, if o i = y then f y else 0 := by simp
    _ ≤ ∑ y, μ * f y := by
      rw [sum_comm]
      refine sum_le_sum fun y _ => ?_
      rw [← sum_filter]; simpa using mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ).mpr (h y)) (hf y)
    _ = _ := by rw [mul_sum]

end Occupancy

section Hit
variable [Fintype V] {M : ℕ} {o : V → Site n} {μ : ℕ}

/-- Polynomial independent of period paying marker-root → site-hit at a
reserve of 1 in the native cover exponent. -/
def siteFactor (M : ℕ) : ℝ := Real.exp 1 * (2*(16*(M:ℝ)+9))^4

lemma torus_kernel (x : Site n) :
    ∑ y : Site n, Real.exp (-(separation y x : ℝ) / (4*(M:ℝ)+2)) ≤ (2*(16*(M:ℝ)+9))^4 := by
  let t y := lift (y-x)
  have hi : Injective t := fun y z h => by
    have := congr_arg (wrap n) h
    simpa only [t,wrap_lift, sub_left_inj] using this
  let b := ((4:ℝ)*(4*M+2))⁻¹
  have hp : 0 < b := by unfold b; positivity
  have he (y : Site n) : Laurent.size (t y) ≤ 4*separation y x := by
    calc
      _ ≤ ∑ _i : Axis, separation y x := sum_le_sum fun i _ => component_le _ _
      _ = _ := by simp [Axis]
  have hn := Laurent.Width.compactPay (α:=Axis) b hp
  calc
    _ ≤ ∑ y, Real.exp (-b*Laurent.size (t y)) := sum_le_sum fun i _ => Real.exp_le_exp.mpr (by
      have h : (Laurent.size (t i):ℝ) ≤ 4*(separation i x : ℝ) := by exact_mod_cast he i
      change -_/_ ≤ -((4:ℝ)*(4*M+2))⁻¹*_
      field_simp; linarith)
    _ = ∑ y∈univ.image t, Real.exp (-b*Laurent.size y) := by rw [sum_image hi.injOn]
    _ ≤ (2*((1+b)/b))^(Fintype.card Axis) := Budget.cap hn _
    _ = _ := by simp [Axis,b]; congr 1; field_simp; ring

/-- Eq.JMmq on the native torus. Each positive source vertex has at least
one name anchored in its support. Nothing about the location of that name
relative to other vertices. -/
theorem root_hit {a c : ℝ} {mode : ι → Finset V} {X : ι → Support n} {f : ι → ℝ}
    (hh : Occupancy o μ) (hf : ∀ i, 0 ≤ f i) (hc : 0 ≤ c)
    (pins : ∀ i, 0<f i → ∃ v∈mode i, o v∈X i)
    (cost : Rooted mode X M (a+1) f c) : Ac.Hit X M f a ((μ:ℝ)*siteFactor M*c) := by
  intro x; refine Budget.certify (fun i => ?_) fun s => ?_
  · split
    · exact mul_nonneg (hf _) (Real.exp_pos _).le
    exact le_rfl
  let k (y : Site n) := Real.exp (1-(separation y x : ℝ)/(4*(M:ℝ)+2))
  let p (v : V) (i : ι) := if v ∈ mode i then Real.exp ((a+1)*coverNumber M (X i)) * f i else 0
  calc
    _ ≤ ∑ i∈s, ∑ v, k (o v)*p v i := sum_le_sum fun i _ => by
      by_cases h : x∈X i ∧ 0<f i
      · obtain ⟨v,hv,hw⟩ := pins i h.2
        apply le_trans ?_ (single_le_sum (f:=fun v => k (o v)*p v i)
          (fun v _ => mul_nonneg (Real.exp_pos _).le ((cost v).1 i)) (mem_univ v))
        rw [if_pos h.1,show p v i = _ from if_pos hv,mul_comm (f i),← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (hf i)
        rw [show k (o v)=_ from rfl, ← Real.exp_add, Real.exp_le_exp]
        have he : (separation (o v) x : ℝ) ≤ coverNumber M (X i) * (4*(M:ℝ)+2)+2*(M:ℝ) := by
          exact_mod_cast Corona.extent _ _ hw h.1
        have hp : 0 < (4*(M:ℝ)+2) := by positivity
        field_simp; nlinarith
      have he : (if x∈X i then f i * Real.exp (a*coverNumber M (X i)) else 0) = 0 := by
        by_cases hx : x∈X i
        · simp [le_antisymm (le_of_not_gt (fun hi => h ⟨hx,hi⟩)) (hf i)]
        simp [hx]
      rw [he]; exact sum_nonneg fun v _ => mul_nonneg (Real.exp_pos _).le ((cost v).1 i)
    _ ≤ ∑ v, k (o v)*c := by
      rw [sum_comm]; refine sum_le_sum fun v _ => ?_
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (Budget.cap (cost v) _) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [← sum_mul]
      apply mul_le_mul_of_nonneg_right _ hc
      refine (hh.weighted k fun _ => (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      dsimp [siteFactor,k]
      simp only [sub_eq_add_neg, Real.exp_add,← mul_sum, ← neg_div]
      exact mul_le_mul_of_nonneg_left (torus_kernel x) (Real.exp_pos _).le

end Hit

section Shape
/-- Cost of projecting an entire possibly winding/support-address before
 doing the block integration, subject to the footprint containment test.
 `s` counts output balls in the halo radius, fixed before L. -/
def tilePrice (s : ℕ) : ℕ := ((s+6)+(s+6)+1)^4

theorem projection_reserve (q : Ratio m n) {B M s : ℕ} (hB : 0<B) (hM : M ≤ 2*B)
    {a A : ℝ} (ha : 0≤a) (hL : 20*a*tilePrice s ≤ (q.count.val:ℝ)*A)
    (X : Support n) (Y : Support m) (hY : Y ⊆ halo (s*B) (X.image q.parent)) :
    a*coverNumber B Y ≤ a*tilePrice s + (A/2)*coverNumber M X := by
  have h := (Nat.mul_le_mul_left q.count.val (Corona.cover_mono hY B)).trans (Corona.collapse q X M B hB hM s)
  have he : (q.count.val:ℝ)*coverNumber B Y ≤ ((q.count.val:ℝ) + 10*coverNumber M X) * (tilePrice s : ℝ) := by
    exact_mod_cast h
  have hp : (0:ℝ)<q.count.val := by exact_mod_cast q.count.property
  apply le_of_mul_le_mul_left (a:=(q.count.val:ℝ)) ?_ hp
  nlinarith [mul_le_mul_of_nonneg_left he ha, mul_le_mul_of_nonneg_right hL (coverNumber M X).cast_nonneg (α:=ℝ)]

lemma exp_absorbs (k : ℕ) (a : ℝ) (ha : 0 < a) : ∃ C : ℝ, 1≤C ∧ ∀ s : ℕ,
    (1+(s:ℝ))^k ≤ C * Real.exp (a*s) := by
  -- 1+s ≤ (1+k/a)*exp((a/k)*s) when k>0.
  refine ⟨(1+k/a)^k, one_le_pow₀ (le_add_of_nonneg_right (by positivity)), fun s => ?_⟩
  by_cases hk : k=0
  · simpa [hk] using Real.one_le_exp (mul_nonneg ha.le (Nat.cast_nonneg _))
  have hk' : (0:ℝ)<k := by exact_mod_cast Nat.pos_of_ne_zero hk
  let u := (a/k)*(s:ℝ)
  have hu := Real.add_one_le_exp u
  have hs : (s:ℝ) = (k/a)*u := by unfold u; field_simp
  have he : 1+(s:ℝ) ≤ (1+k/a)*Real.exp u := by
    rw [add_mul,one_mul,hs]; gcongr
    · exact Real.one_le_exp (by unfold u; positivity)
    exact le_trans (by linarith : u ≤ u+1) hu
  apply (pow_le_pow_left₀ (by positivity) he k).trans_eq
  rw [mul_pow, ← Real.exp_nat_mul,show (k:ℝ)*u = a*s by unfold u; field_simp]



end Shape

section Reset
variable [Fintype V] {o : V → Site n} {μ B : ℕ}

/-- For ≥2 distinct geometrically separated locations. Counting multiplicity
at each site, separately for each allowed monomial, not dividing the total
claim count by any factorial. -/
theorem mixed_pack (hB : 8≤B) (hh : Occupancy o μ) (s : Finset V)
    (hr : 2 ≤ (s.image o).card) (hs : (↑(s.image o) : Set (Site n)).Pairwise fun x y => B^2 ≤ separation x y)
    (X : Support n) (hp : s.image o ⊆ X) : B*s.card ≤ 64*coverNumber B X * μ := by
  have h := Work.I01.answer n (Site n) id B hB (s.image o) hs hr X (by simpa using hp)
  exact (Nat.mul_le_mul_left _ (hh.card s)).trans (le_trans (by rw [Nat.mul_assoc] : B*((s.image o).card*μ) ≤ B*(s.image o).card*μ) (Nat.mul_le_mul_right _ h))



omit [Fintype V] in
/-- Pay full repaint on `hot`. If the high-rate tags are too concentrated,
an alternative is to have at least as many discounted tags in this monomial.
In particular a downset can permit pure contact monomials; one should not
then assume all their rates were recovered for free via connectedness. -/
theorem toll_reset [DecidableEq V] {u w : V → ℝ} {D r δ : ℝ} (hot s : Finset V)
    (hu : ∀ v∈s, 0≤u v) (hw : ∀ v∈s, 0≤w v) (hr : 1≤r) (hD : 1≤D)
    (hδ : 0 ≤ δ) (hμ : 0<μ)
    (hi : ∀ v∈s ∩ hot,D*w v ≤ u v*r) (hc : ∀ v∈s\hot,D*w v ≤ u v/r)
    (hg : r ≤ Real.exp (δ*B/(64*μ))) (h : s.Nonempty)
    {X : Support n} (hs : (s∩hot).card ≤ (s\hot).card ∨ B*(s∩hot).card ≤ 64*coverNumber B X * μ) :
    D*(∏ i∈s, w i) ≤ (∏ i∈s, u i)* Real.exp (δ*coverNumber B X) := by
  let R i := if i∈hot then r else r⁻¹
  have hR : (∏ i∈s, R i) ≤ Real.exp (δ*coverNumber B X) := by
    have he : (∏ i∈s, R i) = r^(s∩hot).card * (r⁻¹)^(s\hot).card := by
      dsimp only [R]; rw [prod_ite]; congr 1 <;> (rw [prod_const]; congr 2)
      ext; simp
    rw [he,inv_pow,← div_eq_mul_inv]
    rcases hs with hs | hs
    · exact (div_le_one_of_le₀ (pow_le_pow_right₀ hr hs) (by positivity)).trans (Real.one_le_exp (by positivity))
    apply (div_le_self (by positivity) (one_le_pow₀ hr)).trans
    have hp : (B:ℝ)*(s∩hot).card ≤ 64*(coverNumber B X : ℝ)*μ := by exact_mod_cast hs
    refine (pow_le_pow_left₀ (zero_le_one.trans hr) hg _).trans ?_
    rw [← Real.exp_nat_mul]; apply Real.exp_monotone
    have hμ : (0:ℝ)<μ := by exact_mod_cast hμ
    rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hp hδ]
  calc
    _ ≤ (D^s.card)*(∏ i∈s, w i) := mul_le_mul_of_nonneg_right
      (by nth_rewrite 1 [← pow_one D]; exact pow_le_pow_right₀ hD (card_pos.mpr h)) (prod_nonneg hw)
    _ = ∏ i∈s, D*w i := by rw [prod_mul_distrib,prod_const]
    _ ≤ ∏ i∈s, u i*R i := prod_le_prod (fun i h => mul_nonneg (zero_le_one.trans hD) (hw i h)) (fun i h => by
      by_cases hh : i∈hot
      · simpa only [R,if_pos hh] using! hi i (mem_inter.mpr ⟨h,hh⟩)
      simpa only [R, if_neg hh,div_eq_mul_inv] using! hc i (mem_sdiff.mpr ⟨h,hh⟩))
    _ ≤ _ := by rw [prod_mul_distrib]; exact mul_le_mul_of_nonneg_left hR (prod_nonneg hu)

end Reset
end YM.Extra.Multi
