import YM.Overlay.Supplier
import YM.Shoot.Reach

/-!
# Metering . Stop and budget arithmetic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Stock
open Lattice Wilson RG Marker Cells MeasureTheory Filter Set Function Overlay Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators ENNReal ContDiff
variable {G : Gauge} {C : Family G}

-- log power fit purely schedule may be imposed at stage entrances
structure Tabs (a : Levels G) : Prop where
  grows i : (a.clock.coverSize (i+1))^2 ≤ 2*(a.clock.coverSize i)^2
  cheap : ∀ ε : ℝ, 0<ε → ∀ᶠ i : ℕ in atTop,
      ((a.S.block i).val * ((a.clock.coverSize i:ℝ)^2))^ (4:ℕ)*YM.Vac.fiat G (a.params (i+1)) (a.clock.hatBeta (i+1)) ≤ ε*a.S.scale (i+1)

namespace Tabs
variable (a : Levels G) (s : ℝ)

def opens (i j : ℕ) := i≤j ∧ s*(a.clock.coverSize j:ℝ)^ (2:ℕ) ≤ a.S.a i/a.S.a j

lemma open_later (t : Tabs a) {j k i : ℕ} (h : opens a s i j) (he : j ≤ k) (hs : 0≤s) : opens a s i k := by
  induction k,he using Nat.le_induction with
  | base => exact h
  | succ k hk ih =>
    refine ⟨le_trans ih.1 (Nat.le_succ _),?_⟩
    calc
      _ ≤ s*(2*(a.clock.coverSize k:ℝ)^2) := mul_le_mul_of_nonneg_left (by exact_mod_cast t.grows k) hs
      _ ≤ 2*(a.S.a i/a.S.a k) := by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left ih.2 (by positivity)
      _ ≤ ((a.S.block k).val:ℝ)*(a.S.a i/a.S.a k) := mul_le_mul_of_nonneg_right (by exact_mod_cast (le_trans (show 2 ≤ 3 by decide) (a.S.block_large k))) (by exact (div_pos (a.S.a_pos i) (a.S.a_pos k)).le)
      _ = _ := by rw [a.S.a_step]; field_simp

lemma mayOpen (h : Tabs a) (m : ℕ) : ∃ b, opens a s m b := by
  by_cases hs : 0≤s
  · have hu i : a.S.a (i+1)* (a.clock.coverSize (i+1):ℝ)^ (2:ℕ) ≤
        ((2:ℝ)/3)*(a.S.a i * (a.clock.coverSize i:ℝ)^ (2:ℕ)) := by
      have hb : (a.clock.coverSize (i+1):ℝ)^ (2:ℕ) ≤ 2*(a.clock.coverSize i:ℝ)^ (2:ℕ) := by exact_mod_cast h.grows i
      rw [a.S.a_step]
      have ha := a.S.a_pos i
      apply le_trans (mul_le_mul (b:=a.S.a i/3) ?_ hb (by positivity) (by positivity)) (by ring_nf; rfl)
      gcongr; exact_mod_cast a.S.block_large i
    let f (i : ℕ) := a.S.a i * ((a.clock.coverSize i:ℝ)^ (2:ℕ))
    have hv i : f i ≤ f 0*((2:ℝ)/3)^i := by
      induction i with
      | zero => simp
      | succ i ih => apply (hu i).trans; apply (mul_le_mul_of_nonneg_left ih (by positivity : 0≤(2:ℝ)/3)).trans_eq; ring
    have ht : Tendsto (fun i : ℕ => s*f i) atTop (𝓝 0) := by
      have he : Tendsto f atTop (𝓝 0) := squeeze_zero (fun i => mul_nonneg (a.S.a_pos i).le (sq_nonneg _)) hv (by
        simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (r:= (2:ℝ)/3) (by norm_num) (by norm_num)).const_mul (f 0))
      simpa only [mul_zero] using he.const_mul s
    obtain ⟨i,H,he⟩ := ((eventually_ge_atTop m).and (ht.eventually (ge_mem_nhds
       (a.S.a_pos m)))).exists
    refine ⟨i,H,(le_div_iff₀ (a.S.a_pos _)).2 (le_trans (le_of_eq ?_) (show s*f i≤_ from he))⟩
    unfold f; ring
  refine ⟨m,le_rfl,(mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (by positivity)).trans (div_nonneg (a.S.a_pos m).le (a.S.a_pos m).le)⟩

open scoped Classical in
def chosen (h : Tabs a) (m : ℕ) : ℕ := Nat.find (mayOpen a s h m)
lemma opened (h : Tabs a) (m : ℕ) : opens a s m (chosen a s h m) := by classical exact Nat.find_spec (mayOpen a s h m)
lemma needs (h : Tabs a) {m u} (he : m < chosen a s h m) (hk : chosen a s h m=u+1) :
    a.S.a m/a.S.a u ≤ s * (a.clock.coverSize u:ℝ)^2 := by
  classical
  have ht : ¬ opens a s m u := fun F => by
    have H : chosen a s h m ≤ u := Nat.find_min' (mayOpen a s h m) F
    omega
  exact le_of_not_ge (fun hv => ht ⟨by omega,hv⟩)

lemma expensive (h : Tabs a) (hs : 1 ≤ s) (i : ℕ) (F : ℕ) (hF : chosen a s h i=F+1) :
    a.S.a i / a.S.a (F+1) ≤ s * ((a.S.block F).val * (a.clock.coverSize F:ℝ)^2) := by
  have ht := (opened a s h i).1
  have hh := a.S.a_pos F
  have hg : (3:ℝ)≤ (a.S.block F).val := by exact_mod_cast (a.S.block_large F)
  have hp : 0< ((a.S.block F).val:ℝ) := lt_of_lt_of_le (by norm_num) hg
  have h1 : (1:ℝ) ≤ (a.clock.coverSize F:ℝ) := by exact_mod_cast (a.budget F).B_pos
  rcases eq_or_lt_of_le ht with e|e
  · have hw : a.S.a i=a.S.a (F+1) := congr_arg a.S.a (e.trans hF)
    rw [hw,div_self (a.S.a_pos _).ne']
    exact one_le_mul_of_one_le_of_one_le hs (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ h1))
  rw [a.S.a_step, show a.S.a i / (a.S.a F / (a.S.block F).val)= (a.S.a i/a.S.a F)*(a.S.block F).val by field_simp]
  exact (mul_le_mul_of_nonneg_right (needs a s h e hF) hp.le).trans_eq (by ring)

lemma pay (h : Tabs a) (hs : 1≤s) (e : ℝ) (he : 0<e) :
    ∀ᶠ m : ℕ in atTop,
      let p := chosen a s h m
      (a.S.a m / a.S.a p)^4* Vac.fiat G (a.params p) (a.clock.hatBeta p) ≤ e * a.S.scale p := by
  have hw : ∀ᶠ m : ℕ in atTop, ∀ i ≥ m-1,
      ((a.S.block i).val * ((a.clock.coverSize i:ℝ)^2))^(4:ℕ) * Vac.fiat G (a.params (i+1)) (a.clock.hatBeta (i+1)) ≤
        (e/s^4) * a.S.scale (i+1) := by
    have hn : 0 < s := by linarith
    obtain ⟨j,hj⟩ := eventually_atTop.1 (h.cheap (e/s^4) (by positivity))
    filter_upwards [eventually_gt_atTop j] with i hg k hk using hj _ (by omega)
  filter_upwards [hw,eventually_gt_atTop 0] with i hi hp
  dsimp only
  have hv := (opened a s h i).1
  cases hg : chosen a s h i with
  | zero => omega
  | succ m =>
    have hh := hi m (by omega)
    have hf (q : ℕ) : 0≤Vac.fiat G (a.params q) (a.clock.hatBeta q) := by
      unfold Vac.fiat
      have hu := (a.params q).clip.quadratic_pos
      have hx := (a.params q).paths_pos
      have he := Real.log_pos (a.fits.delayed q)
      positivity
    calc
      _ ≤ (s*((a.S.block m).val*(a.clock.coverSize m:ℝ)^ (2:ℕ)))^(4:ℕ) * Vac.fiat G (a.params (m+1)) (a.clock.hatBeta (m+1)) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (div_nonneg (a.S.a_pos _).le (a.S.a_pos _).le) (expensive a s h hs i m hg) 4) (hf (m+1))
      _ ≤ _ := by
        rw [mul_pow,mul_assoc]
        refine (mul_le_mul_of_nonneg_left hh (show 0 ≤ s^4 by positivity)).trans_eq ?_
        have hn := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hs)
        field_simp
end Tabs

/-- forward supplier. Enough to serve any first stop for construction. -/
structure Fuel (C : Family G) (d : ℕ) (r : ℝ) where
  charge : ℝ
  charge_limit : 1 ≤ charge
  stamps : ℕ → Foot
  slot i : (stamps i).stop=i

namespace Fuel
variable {d : ℕ} {r : ℝ} (F : Fuel C d r)

def ready := ∀ i j, C.ref d ≤ i → Tabs.opens C.path.levels F.charge i j → (F.stamps j).services C d i r

def covers := ∀ ε : ℝ, 0<ε → ∀ᶠ i in atTop,
    let X:=F.stamps i
    X.u+X.c+X.d*X.b-Real.log X.w ≤ ε*C.S.scale i

lemma record (h : G.Simple) (ht : Tabs C.path.levels) (he : F.ready) (hv : F.covers) :
    ∃ X : ℕ → Foot, (∀ i,C.ref d ≤ i → (X i).services C d i r) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i : ℕ in atTop, (X i).bill C i d ≤((d:ℝ)+ε)*C.S.scale i := by
  let p := Tabs.chosen C.path.levels F.charge ht
  refine ⟨fun i => F.stamps (p i),fun i hi => he i (p i) hi (by apply Tabs.opened),?_⟩
  intro ε hε
  let z := min (ε/4) (ε/(4*((d:ℝ)+ε)))
  have h0 : 0<z := by unfold z; positivity
  have hz := ht.pay C.path.levels F.charge F.charge_limit _ h0
  have hp : ∀ i,i ≤ p i := fun i => (Tabs.opened _ _ ht i).1
  have hS : Tendsto p atTop atTop := tendsto_atTop_mono hp tendsto_id
  filter_upwards [hz,hS.eventually (Vac.treasury_stage C.path.levels h), hS.eventually (hv z h0)] with i hi ha hh
  -- gap of scales ← log ratio ≤ price. m_i* always ≥1.
  let r := p i
  let b := C.path.levels
  let u := C.S.a i/C.S.a r
  let B := Vac.fiat G (b.params r) (b.clock.hatBeta r)
  change u^4 * B≤ z*C.S.scale r at hi
  have hs : 1≤u := (one_le_div (C.S.a_pos _)).2 (C.S.strictAnti.antitone (hp i))
  have hB : 1≤B := by
    unfold B Vac.fiat
    have he := (b.params r).paths_pos
    have ha := (b.params r).clip.quadratic_pos
    have hp : 0≤ (Fintype.card PlaqAxes:ℝ)*((b.params r).clip.direct + (b.params r).paths^2) +
      4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log (b.clock.hatBeta r)/2) := by
      have hu := Real.log_pos (b.fits.delayed r)
      positivity
    linarith only [hp,he]
  have hG : C.S.scale r-C.S.scale i=Real.log u := by
    unfold Schedule.scale u; rw [Real.log_div (C.S.a_pos _).ne' (C.S.a_pos _).ne', Real.log_inv,Real.log_inv]; ring
  have hw : C.S.scale r-C.S.scale i≤z*C.S.scale r := by
    rw [hG]
    calc
      _ ≤ u := Real.log_le_self (by linarith)
      _ ≤ u^4 := by
        conv_lhs => rw [← pow_one u]
        exact pow_le_pow_right₀ hs (by norm_num)
      _ ≤ u^4*B := le_mul_of_one_le_right (by positivity) hB
      _ ≤ _ := hi
  have hf := (mul_le_mul_of_nonneg_left ha (show 0 ≤ u^4 from by positivity)).trans hi
  let X := F.stamps r
  change X.u+X.c+X.d*X.b-Real.log X.w≤z*C.S.scale r at hh
  unfold Foot.bill expPrice
  rw [F.slot]
  change u^4 * Vac.treasury C.path.levels r + X.u+X.c+X.d*X.b +_ -Real.log X.w ≤((d:ℝ)+ε)*C.S.scale i
  have H₀ : 0 < (d:ℝ)+ε := by positivity
  have hX := mul_le_mul_of_nonneg_left hw H₀.le
  have hY : z*((d:ℝ)+ε) ≤ ε/4 := by
    apply (mul_le_mul_of_nonneg_right (show z ≤ ε/(4*((d:ℝ)+ε)) from min_le_right ..) H₀.le).trans
    exact le_of_eq (by field_simp)
  have hQ : 0 ≤ C.S.scale r := Shoot.scale_nn b r
  have ht' : u^4*Vac.treasury C.path.levels r ≤ z*C.S.scale r := hf
  change _+_+_+_+(d:ℝ)*C.S.scale r-_≤_
  linarith only [hh,hX, ht', mul_le_mul_of_nonneg_right hY hQ,
    mul_le_mul_of_nonneg_right (show z≤ε/4 from min_le_left ..) hQ, mul_nonneg hε.le hQ]
end Fuel
end YM.Stock
