import YM.SharpGram.Dense.Width

/-!
# Slim portfolios cover

Force W for the price tests (successive exact witness context),
and standby of one previous stage on the second, slim windows (for ANY
calendar produced with these gates). At every sufficiently deep k the
second Wait can operate either at k or at the last position of immediately
preceding stage with `scale k - scale old ≤ log(hatBeta k)`. No estimate
restricted to runs or a subsequence for the spacing. Don't require the UV,
base rank etc W to have those slim windows too. `Wait.engine` unmodified!
Even if the scheduled run is very far from the previous stage's last level,
we can use the latter as Interior. Key is increasing the bottom thresholds to
ensure slim windows grow at rate ≤ 1 in level count even on huge gaps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Dense
open Function Filter Asymptotics Lattice RG Supply Next.Rank Next.Rank.Ship Pert.Dense
open scoped Topology BigOperators
variable {G : Gauge} (hG : G.Simple) {s : Sheet G} {w : Rolls s}
  {θ : Protection w} {H : Delays θ} {Y : Bar H}
  {U V : Wait Y}
set_option quotPrecheck false

def LateEnough (U V : Wait Y) : Prop := Thicker U V ∧
  ∀ j, U.readyHere (j+1) ≤ V.readyHere j ∧ ∀ x : ℝ, V.readyHere j ≤ x → G.slopeConstant ≤ preHat Y x
include hG
lemma loadBoth (W U : Wait Y) : ∃ V, Thicker W V ∧ LateEnough U V := by
  obtain ⟨r,hr⟩ := eventually_atTop.mp ((scheduledHeight hG Y).eventually_ge_atTop G.slopeConstant)
  let V : Wait Y :=
    { readyHere j := max (max (W.readyHere j) (U.readyHere j)) (max (U.readyHere (j+1)) r)
      minLength := max U.minLength W.minLength
      window j s := U.window j s + W.window j s
      sublin j := by simpa only [Nat.cast_add,add_div,zero_add] using (U.sublin j).add (W.sublin j) }
  refine ⟨V,⟨le_max_right ..,fun j => (le_max_left ..).trans (le_max_left ..),fun i j => Nat.le_add_left ..⟩,
    ⟨le_max_left ..,fun j => (le_max_right ..).trans (le_max_left ..),fun i j => Nat.le_add_right ..⟩,
    fun j => ⟨(le_max_left ..).trans (le_max_right ..), fun x h => hr x (((le_max_right ..).trans (le_max_right ..)).trans h)⟩⟩

omit hG
variable {A : Levels G} {m k j : ℕ} (hs : U.window = slim Y) (ha : LateEnough U V) (hV : Paid V A)
local notation "J" => A.clock.J
local notation "P" => A.clock.hatBeta
local notation "S" => A.S.scale
include hV
lemma costSame (k : ℕ) : preHat Y (S k) = P k := by unfold preHat Calendar.hatBeta; rw [hV.bar]
lemma scaleAdd (hm : m ≤ k) (hx : ∀ i, m < i → i≤k → J i=j) :
    S k = S m + (k - m : ℕ) * unitLog w j := by
  induction k, hm using Nat.le_induction with
  | base => simp
  | succ k hm ih =>
    have he : A.S.block k=w.L j := (A.fits.sameFactor k).symm.trans (by rw [hV.lengths, hx (k+1) (by omega) le_rfl])
    rw [Schedule.scale_succ,he,ih (fun i ha hb => hx i ha (by omega)),show k+1-m=k-m+1 from by omega]
    unfold unitLog; push_cast; ring
omit hV in
lemma middleEq (_hm : m ≤ k) (hx : J m=j) (hy : J k=j) (i : ℕ) (he : m ≤ i) (hi : i ≤ k) : J i=j :=
  le_antisymm ( (A.fits.mono hi).trans_eq hy) (hx ▸ A.fits.mono he)
include hs
lemma thinShift (hm : m ≤ k) (hx : J m=j) (hy : J k=j) (hp : G.slopeConstant ≤ P m) :
    U.window j (S k) ≤ U.window j (S m) + (k-m) := by
  let r : ℝ := ((k-m:ℕ) : ℝ)
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have he := scaleAdd hV hm (fun i hi hi' => middleEq hm hx hy i hi.le hi')
  let l := unitLog w j
  have hl : 0 < l := positiveUnit w j
  have h₁ : 1 ≤ P m := (A.fits.delayed _).le
  have hp' : 0 < P k := zero_lt_one.trans (A.fits.delayed _)
  have ht : 0 < P m := zero_lt_one.trans_le h₁
  have hg : P k / P m ≤ 1 + r*l := by
    rw [div_le_iff₀ ht]
    calc
      P k = P m + G.slopeConstant * (r*l) := by
        change A.clock.bar + G.slopeConstant * S k=A.clock.bar+G.slopeConstant*S m+_
        rw [he]; ring
      _ ≤ P m + P m * (r*l) := add_le_add le_rfl (mul_le_mul_of_nonneg_right hp (mul_nonneg hr hl.le))
      _ = _ := by ring
  have hstep := Real.log_le_sub_one_of_pos (div_pos hp' ht)
  rw [Real.log_div hp'.ne' ht.ne'] at hstep
  rw [hs]; unfold slim; rw [costSame hV, costSame hV,← Nat.floor_add_natCast (div_nonneg (Real.log_nonneg h₁) hl.le)]
  apply Nat.floor_le_floor; change Real.log (P k) / l ≤ Real.log (P m) / l + r
  rw [div_le_iff₀ hl, add_mul, div_mul_cancel₀ _ hl.ne']
  linarith only [hg, hstep]
include ha

lemma runToLast (hm : J m+1=J (m+1)) (hj : s.first ≤ J m) : Interior U A m := by
  let j := J m
  obtain ⟨i,hp,hℓ,hb⟩:= hV.run j hj
  have hji : J i = j := hb i (by omega) (by omega)
  have ht : i ≤ m := by by_contra! h; have hF:= A.fits.mono (show m+1 ≤ i from h); unfold j at hji; omega
  let a := V.window j (S i)
  let b := U.window j (S m)
  have hv : G.slopeConstant ≤ P i := costSame hV i ▸ (ha.2 j).2 _ hp
  have hx : b ≤ a + (m-i) := (thinShift hs hV ht hji rfl hv).trans (Nat.add_le_add_right (ha.1.range j (S i)) _)
  change a ≤ i at hℓ
  constructor
  · have ht' : S i ≤ S m := by
      have hC := scaleAdd hV ht (j:=j) (fun r hr he => middleEq ht hji rfl r hr.le he)
      exact hC ▸ le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (positiveUnit w j).le)
    exact (ha.1.ready j).trans (hp.trans ht')
  · change b ≤ m; omega
  intro r hr he; change m-b ≤ r at hr
  rcases le_or_gt i r with hy|hy
  · exact middleEq ht hji rfl r hy he
  exact hb r (show i-a ≤ r by omega) (le_trans hy.le (Nat.le_add_right ..))

lemma withinSpan (hk : s.first < J k) : ∃ m ≤ k, Interior U A m ∧ J k ≤ J m + 1 ∧
    S k ≤ S m + Real.log (P k) := by
  let j := J k
  let n := Nat.find (show ∃ i, J i=j from ⟨k,rfl⟩)
  have hn : n ≤ k := Nat.find_min' (p:=fun i => J i=j) _ rfl
  have he : J n=j:= Nat.find_spec (p:=fun i=> J i=j) _
  have ho : n≠0:=by
    intro ht; rw [ht,hV.firstZero] at he; exact hk.ne he
  let p := n-1
  have hnp : p+1=n:=by unfold p; omega
  have ht : J p < j := by
    apply lt_of_le_of_ne ((A.fits.mono (show p ≤ n by omega)).trans_eq he)
    intro h'; have hv : n ≤ p := Nat.find_min' (p:=fun i=> J i=j) _ h'; omega
  have hop : J p+1=J (p+1):= by
    have hj := A.fits.stepSlow p
    rw [hnp,he] at hj ⊢; omega
  have hs' : s.first ≤ J p := hV.firstZero ▸ A.fits.mono (Nat.zero_le p)
  have hb : 0 < P k := zero_lt_one.trans (A.fits.delayed _)
  have hh := Real.log_nonneg (A.fits.delayed k).le
  let d := U.window j (S k)
  have hf(i) (hi:p < i)(he':i≤k) : J i=j:= middleEq hn he rfl i (by omega) he'
  by_cases hv : p < k - d
  · refine ⟨k, le_rfl,⟨?_,?_,fun i hi h => hf i (lt_of_lt_of_le hv hi) h⟩,Nat.le_succ _,le_add_of_nonneg_right hh⟩
    · obtain ⟨s₀,hh,hz,hU'⟩:= hV.run _ hs'
      have hk' : J s₀ = J p := hU' _ (by omega) (by omega)
      have hy : s₀ ≤ p := by by_contra! h'; have hy := A.fits.mono (show p+1 ≤ s₀ from h'); omega
      have he' (x y : ℕ) (hx : x ≤ y) : S x ≤ S y := by
        induction y, hx using Nat.le_induction with
        | base=> rfl
        | succ i hi h=> rw [Schedule.scale_succ]; exact h.trans (le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (A.S.block i).pos)))
      change U.readyHere j ≤ S k
      rw [← he, ← hnp, ← hop]
      exact (ha.2 _|>.1).trans (hh.trans (he' s₀ k (by omega)))
    change d ≤ k; omega
  refine ⟨p,by omega,runToLast hs ha hV hop hs',?_ , ?_⟩
  · change j ≤ _; rw [hop,hnp,he]
  have hπ : k - d ≤ p := Nat.le_of_not_gt hv
  let l := unitLog w j
  have hl : 0 < l := positiveUnit w j
  have hd : d*l ≤ Real.log (P k) := by
    apply (le_div_iff₀ hl).mp
    unfold d; rw [hs]; unfold slim; rw [costSame hV]; exact Nat.floor_le (div_nonneg hh hl.le)
  rw [scaleAdd hV (le_trans (show p≤n by omega) hn) hf]
  apply add_le_add le_rfl
  refine le_trans ?_ hd
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k-p ≤ d)) hl.le

/-- Mark every k by a predecessor usable by our Interior Wait. -/
lemma nearby : ∃ g : ℕ → ℕ, Tendsto g atTop atTop ∧
    ∀ᶠ k in atTop, g k ≤ k ∧ Interior U A (g k) ∧ S k ≤ S (g k)+Real.log (P k) := by
  have he := A.fits.deep.eventually_gt_atTop s.first
  let g k := if h:s.first < J k then (withinSpan hs ha hV h).choose else k
  have hh : ∀ᶠ k in atTop, g k ≤ k ∧ Interior U A (g k) ∧ J k ≤ J (g k)+1 ∧ S k ≤ S (g k)+Real.log (P k) := by
    refine he.mono fun k h=>?_
    dsimp only [g]; rw [dif_pos h]; exact (withinSpan hs ha hV h).choose_spec
  refine ⟨g, tendsto_atTop.mpr ?_, hh.mono (fun i ⟨h,hV,_,hs⟩ => ⟨h,hV,hs⟩)⟩
  intro m
  filter_upwards [A.fits.deep.eventually_gt_atTop (J m + 1), hh] with i hi ⟨h₁,h₂,h₃,h₄⟩
  by_contra! h; have hn:=A.fits.mono h.le; omega
end YM.SharpGram.Dense
