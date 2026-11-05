import YM.OPE.Columns.Limit

/-!
# Resulting bound in the physical filtration

For each grade, a single footprint in the field quotient of a k-budget vector, along
any further ordered sublimit. Applies to *all* choices of projections eliminating
lower stages. (At weight zero use the estimate for the entire vector.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Columns
open Function Set Filter MeasureTheory Analysis Wilson MergeProof Labels Source
open RG Bid Push.RelayDifference Extraction Next.Extract Dash
open Work.G08 Extra.Histories Next.UVStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {W r D} (T : TableTickets C W r D) {d e k N p : ℕ} (hG : G.Simple)
  {f : Extraction.Order} {A S : Table C.book} {V : DiffPlan S} {M : ℕ → Table C.book} {R : Bin A} {X : DiffPlan S}
  (L : Base C f A M R S V) (h : X.Inclusions S) (he : e<d)
local notation "F" => C.labels.level d
set_option quotPrecheck false
local notation "α" => C.S.a

/-- Cost of transmission down to reference modulo the transported e-plane.
The length-dependent exponent is d-(e+1), *not* d-e. -/
def fare (C : Family G) (k d e : ℕ) : ℝ := gel C.path.levels k * (1+(C.path.levels.params k).columns)*
      (C.S.a (C.ref d) / C.S.a k)^(d-(e+1))
lemma fare_pos (C : Family G) (k d e : ℕ) : 0 < fare C k d e := mul_pos (mul_pos
   (zero_lt_one.trans_le (gel_pos ..)) (add_pos_of_pos_of_nonneg zero_lt_one
   (zero_le_one.trans (C.path.levels.params _).columns_ge))) (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _)

include T he
lemma discounted (hx:C.Makes) (hk:C.ref d ≤ k) (hp:k ≤ N) (x:C.label d) :
    let B := (C.factory d N p).terminal.symm
    ∃ y : C.label d, low F e (B y)=B y ∧ ‖x-y‖ ≤ fare C k d e * quota C d k N p x := by
  intro B
  obtain ⟨a,ha,he⟩ := quotient_issue (p:=p) T hx (B x) he hk hp
  let A:= (C.factory d N p).terminal
  refine ⟨A a, ?_⟩
  dsimp only [B,A]; simp only [LinearEquiv.symm_apply_apply, ha, true_and]
  refine (Size.norm_le F _).trans ?_
  have hb : A (B x-a)= x-A a := by rw [map_sub, LinearEquiv.apply_symm_apply]
  rw [hb] at he; exact he

include T L h he hG
lemma limit_cap (v : Rowe C d) (x : C.label d) {b : Filter Cutoffs} [b.NeBot] {z : ℝ}
    (hp : b ≤ f.fuse) (hk:C.ref d ≤ k)
    (hz : ∀ᶠ i in b, quota C d k i.1 i.2 (v i) ≤ z) (hx : Tendsto v b (𝓝 x)) :
    ∃ y : C.label d, S.project d y ∈ LinearMap.range (X.rise he.le) ∧ ‖x-y‖ ≤ fare C k d e*z := by
  classical
  let y (i : Cutoffs) := if a : k ≤ i.1 then
    Classical.choose (discounted (p:=i.2) T he L.family hk a (v i)) else 0
  have ht (i : Cutoffs) (a : k ≤ i.1) : low F e ((C.factory d i.1 i.2).terminal.symm (y i))=(C.factory d i.1 i.2).terminal.symm (y i) ∧
      ‖v i-y i‖ ≤ fare C k d e* quota C d k i.1 i.2 (v i) := by
    rw [show y i=_ from dif_pos a]
    apply Classical.choose_spec (discounted (p:=i.2) T he L.family hk a (v i))
  have hi := ((cutoff_grows f).eventually_ge_atTop k).filter_mono hp
  have hu : ∀ᶠ i in b, ‖v i - y i‖ ≤ fare C k d e*z := by
    filter_upwards [hi,hz] with i hi hy using ((ht i hi).2.trans (mul_le_mul_of_nonneg_left hy (fare_pos ..).le))
  obtain ⟨l,hl,hn,u,hU⟩:= finite_extract (𝓛:=b) y (‖x‖+1+fare C k d e*z) (by
    filter_upwards [hx.norm.eventually (ge_mem_nhds (lt_add_of_pos_right ‖x‖ zero_lt_one)),hu] with i hi hp
    linarith only [hp,hi,norm_sub_norm_le (y i) (v i),norm_sub_rev (v i) (y i)])
  refine ⟨u, limit_lower T hG L h y u he (hl.trans hp) ((hi.mono fun i hi => (ht i hi).1).filter_mono hl)
      hU, le_of_tendsto (((hx.mono_left hl).sub hU).norm) (hu.filter_mono hl)⟩

omit T h he hG in
lemma whole_origin (x : C.label d) (hk : C.ref d ≤ k) (hN : k ≤ N) : ‖x‖ ≤
    juice C.path.levels k * (C.S.a (C.ref d) / C.S.a k)^d * quota C d k N p x := by
  induction k,hk using Nat.le_induction with
  | base =>
    apply (Size.norm_le F x).trans
    rw [div_self (C.S.a_pos _).ne',one_pow,mul_one,quota]
    rw [show ((C.factory d N p).entries (C.ref d) _).x= x from C.normalized L.family hN x]
    exact le_mul_of_one_le_left (size_nonneg _ _) (juice_pos ..)
  | succ i hi ih =>
    let a := (C.S.a (C.ref d)/C.S.a i)^d; let Fm:= C.path.levels
    let Gm:= (Fm.params (i+1)).columns
    let y:ℝ:= (C.S.block i).val; have hy:0 < y:=by unfold y; positivity
    apply (ih (i.le_succ.trans hN)).trans
    have he : quota C d i N p x ≤ Gm * y^d * quota C d (i+1) N p x :=
      ((L.family.calibrated _ _ _ ((hi.trans i.le_succ).trans hN)).front i hi hN _)
    have ha:0 ≤ a:= pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _
    refine (mul_le_mul_of_nonneg_left he (mul_nonneg (zero_le_one.trans (juice_pos ..)) ha)).trans_eq ?_
    rw [juice_step, show C.S.a (C.ref d) / C.S.a (i+1) = y*(C.S.a (C.ref d) / C.S.a i) by
      rw [Schedule.a_step]; unfold y; field_simp, mul_pow]
    unfold Gm Fm; ring

variable {ι : Type*} {l : Filter ι} {J : ι → ℝ} {v : ι → ℕ} {x : ℝ}
omit T L h hG he in
lemma rescale {S : Schedule} {p : ℕ → ℝ} {a : ℝ} (h : Ribbons.Note S p a)
    (hv : Tendsto v l atTop) (ht : Tendsto (fun i => S.scale (v i)/J i) l (𝓝 x)) :
    RateIs l J (fun i => p (v i)) (a*x) := by
  refine ⟨Eventually.of_forall fun _ => h.pos _,((h.pitch.comp hv).mul ht).congr' ?_⟩
  filter_upwards [(S.divergent.comp hv).eventually_gt_atTop 0] with i hi
  dsimp only [comp_apply] at hi ⊢; simp only [div_eq_mul_inv];
  rw [show _ * (S.scale (v i)*(J i)⁻¹) = Real.log (p (v i)) * ((S.scale (v i))⁻¹ * S.scale (v i)) * (J i)⁻¹ by ring, inv_mul_cancel₀ hi.ne', mul_one]

omit T L h hG he in
lemma juice_rate_seq (C : Family G) (hv : Tendsto v l atTop) (ht : Tendsto (fun i => C.S.scale (v i)/J i) l (𝓝 x)) :
    RateIs l J (fun i => juice C.path.levels (v i)) 0 := by
  have hx := rescale (Ribbons.futon C) hv ht; rw [zero_mul] at hx; exact hx
omit L h hG he in
lemma gel_le (k) : gel C.path.levels k * (C.path.levels.params k).columns ≤
    juice C.path.levels k ^ (3:ℕ) * (C.path.levels.params 0).columns := by
  have hs(i): 2 ≤ (C.path.levels.params i).columns := by
    let j:= C.path.levels.clock.J i
    exact (show 2 ≤ 64*(W.K (j+1))^2 by nlinarith only [W.prices (j+1)]).trans (T.system.costs.cost i)
  induction k with
  | zero=> simp [gel,juice]
  | succ k ih=>
    let H:=C.path.levels; let g:= gel H k; let p:= juice H k ^ (3:ℕ) * (H.params 0).columns
    let s i := (H.params i).columns; let t:= s (k+1)
    have he:1+s k ≤ s k*t:= by nlinarith only [hs k,hs (k+1)]
    have ht:0 ≤ t:=zero_le_one.trans (H.params (k+1)).columns_ge
    have hp:0 ≤ g:=zero_le_one.trans (gel_pos ..)
    rw [gel_step,juice_step]
    calc
       _ ≤ g*((s k*t)*t) * t := mul_le_mul_of_nonneg_right
         (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he ht) hp) ht
       _ = g*s k*t^3 := by ring
       _ ≤ p*t^3 := mul_le_mul_of_nonneg_right ih (pow_nonneg ht _)
       _ = _ := by unfold p t s H; ring

omit L h hG he in
lemma gel_rate_seq (hv : Tendsto v l atTop) (hJ : Tendsto J l atTop) (ht : Tendsto (fun i => C.S.scale (v i)/J i) l (𝓝 x)) :
    RateIs l J (fun i => gel C.path.levels (v i)) 0 := by
  let s:= (C.path.levels.params 0).columns; have hs:0 < s:= zero_lt_one.trans_le (C.path.levels.params 0).columns_ge
  have hp : RateLE l J (fun i => (juice C.path.levels (v i))^3 * s) 0 := by
    simpa only [mul_zero,zero_add] using (((juice_rate_seq C hv ht).power 3).mul (RateIs.const hJ hs)).pays hJ
  apply RateIs.of_sandwich (RateIs.const hJ one_pos) hp (Eventually.of_forall fun i => gel_pos _ (v i)) _ hJ
  refine Eventually.of_forall fun i => ?_
  exact le_trans (le_mul_of_one_le_right (zero_le_one.trans (gel_pos ..)) (C.path.levels.params (v i)).columns_ge)
    (gel_le T _)

omit L h hG he in
lemma fare_rate (hv : Tendsto v l atTop) (hJ : Tendsto J l atTop) (ht : Tendsto (fun i => C.S.scale (v i)/J i) l (𝓝 x)) :
    RateIs l J (fun i => fare C (v i) d e) ((d-(e+1):ℕ)*x) := by
  have hp := gel_rate_seq T hv hJ ht; have hh := rescale (Ribbons.fuNote C) hv ht
  rw [zero_mul] at hh
  unfold fare
  have hu := (hp.mul ((RateIs.const hJ one_pos).add hh hJ)).mul (((RateIs.const hJ (C.S.a_pos (C.ref d))).div
    (rescale (Ribbons.Note.note_a C.S) hv ht)).power (d-(e+1)))
  simpa only [neg_mul,one_mul, zero_sub, max_self,zero_add, neg_neg] using hu
end YM.OPE.Columns
