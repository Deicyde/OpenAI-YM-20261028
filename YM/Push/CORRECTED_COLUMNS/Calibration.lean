import YM.Push.CORRECTED_COLUMNS.Addresses
/-!
# One possible production of the tuned lifts from calibration estimates

First, physical x from the actual
normalized history. No supposition of uniform-in-N bounds; fixed k bounds
proved from Based. Then calibration gate: IF produce the near-identity
read (scaled Wick answer in x-basis, cf. 13189) from these singleton data,
construct precisely the primary combination for the determinant tests in
these units. No progress on the analytic expansion at smaller threshold
*giving* those reads here. Parametrize on the map, so use with the one that
will be proven usable for the remaining Value estimates. Separate H-cost
of taking such combinations (columns are real, require only star at this
interface); no mixing estimates inferred.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Issue
open Cells Labels Source RG Lattice Wilson MeasureTheory Function
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {k m N p d : ℕ}

def primary (C : Family G) {d} (v : C.label d) (m N p : ℕ) :=
    ((C.S.a m : ℂ)^d)⁻¹ • (chunk C v m N p).x

theorem charge (h : C.Makes) (d) {m} (hm : C.ref d ≤ m) : ∃ D : ℝ, 0<D ∧ ∀ (N p : ℕ), m ≤ N →
    ∀ v : C.label d, ‖v‖ ≤ D*‖primary C v m N p‖ ∧ ‖primary C v m N p‖ ≤ D*‖v‖ := by
  let F := C.labels.level d
  let s := F.coeffSize
  have he u (hr : C.ref d ≤ u) : ∃ A : ℝ, 0<A ∧ ∀ (N p : ℕ), u≤N → ∀ v : C.label d,
      s v≤ A*s (chunk C v u N p).x ∧ s (chunk C v u N p).x≤A*s v := by
    induction u,hr using Nat.le_induction with
    | base =>
      refine ⟨1,one_pos,fun N p hp v => ?_⟩
      have ht : (chunk C v (C.ref d) N p).x=v := C.normalized h hp v
      rw [ht,one_mul]; exact ⟨le_rfl,le_rfl⟩
    | succ i hi ih =>
      obtain ⟨A,hA,H⟩ := ih
      let R := (C.path.levels.params (i+1)).columns
      let L : ℝ := (C.S.block i).val
      have hr : 0 < R := zero_lt_one.trans_le (C.path.levels.params (i+1)).columns_ge
      have hl : 1 ≤ L := Nat.one_le_cast.mpr (C.S.block i).property
      have he : 0 < L := by linarith
      refine ⟨A*(R*L^d),by positivity,fun N p hp v => ?_⟩
      have hn : i≤N := Nat.le_succ i |>.trans hp
      have ht := H N p hn v
      have hu := h.calibrated d N p (hi.trans hn)
      let w := s (chunk C v i N p).x
      let z := s (chunk C v (i+1) N p).x
      have he : w ≤ (R*L^d)*z := hu.front _ hi hp ((C.factory d N p).terminal.symm v)
      have hb : z≤R*w := hu.back _ hi hp ((C.factory d N p).terminal.symm v)
      refine ⟨ht.1.trans ((mul_le_mul_of_nonneg_left he hA.le).trans_eq ?_), hb.trans ?_⟩
      · rw [← mul_assoc]
      apply (mul_le_mul_of_nonneg_left ht.2 hr.le).trans
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => norm_nonneg (v i) : 0≤s v)
      rw [← mul_assoc,mul_comm R]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hl)
  let J := (Fintype.card F.Index:ℝ)
  have hj : 0<J := Nat.cast_pos.mpr Fintype.card_pos
  have hs (v : C.label d) : ‖v‖≤s v ∧ s v≤J*‖v‖ := by
    refine ⟨(pi_norm_le_iff_of_nonneg (show 0 ≤ s v from Finset.sum_nonneg fun j _ => norm_nonneg (v j))).2
      fun j => Finset.single_le_sum (fun i _ => norm_nonneg (v i)) (Finset.mem_univ j),?_⟩
    simpa only [J,s,Frame.coeffSize,F,nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G:=fun _ : (C.labels.level d).Index => ℂ) v
  obtain ⟨A,hA,H⟩ := he m hm
  let w := (((C.S.a m:ℂ)^d)⁻¹)
  let K := ‖w‖
  have hk : 0<K := norm_pos_iff.mpr (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (C.S.a_pos _).ne')))
  refine ⟨max (A*J/K) (K*A*J),lt_of_lt_of_le (by positivity) (le_max_left ..),fun N p hp v => ?_⟩
  let u := (chunk C v m N p).x
  have ht := H N p hp v
  have hr : ‖primary C v m N p‖=K*‖u‖ := norm_smul ..
  constructor
  · apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ (K*A*J)) (norm_nonneg _))
    apply (hs v).1.trans (ht.1.trans ((mul_le_mul_of_nonneg_left (hs u).2 hA.le).trans (le_of_eq ?_)))
    rw [hr]; field_simp
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_right (A*J/K) _) (norm_nonneg v))
  rw [hr]; apply (mul_le_mul_of_nonneg_left ((hs u).1.trans (ht.2.trans (mul_le_mul_of_nonneg_left (hs v).2 hA.le))) hk.le).trans
  exact le_of_eq (by ring)

lemma primary_unit (h : C.Makes) (d) {m N p} (hk : C.ref d ≤ m) (hn : m ≤ N) :
    primary C (C.refUnit d) m N p=(C.labels.level d).e0 := by
  let F := C.labels.level d
  let T := C.factory d N p; let v := unitVec F C.path N
  have H := h.calibrated d N p (hk.trans hn)
  have hu : T.terminal.symm (C.refUnit d)=v := by
    apply T.terminal.injective; rw [T.terminal.apply_symm_apply]
    exact (H.unit_coord _ le_rfl (hk.trans hn)).symm.trans (H.reads _)
  unfold primary chunk; rw [hu,H.unit_coord m hk hn]
  unfold unitVec; rw [smul_smul,inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast (C.S.a_pos _).ne')), one_smul]

-- Finite-dimensional readout problem at each N,p. `Analyzed` estimates,
-- not construction. X-basis relative closeness BEFORE g/t weights.
structure Analyzed (C : Family G) (d m N p : ℕ) (E : C.label d →ₗ[ℂ] C.label d) : Prop where
  near v : ‖E v-primary C v m N p‖ ≤ ‖primary C v m N p‖/2
  real v : star (E v)=E (star v)
  unit : E (C.refUnit d)=(C.labels.level d).e0

lemma estimates {E : C.label d →ₗ[ℂ] C.label d} (e : Analyzed C d m N p E) (v : C.label d) :
    ‖primary C v m N p‖ ≤ 2*‖E v‖ ∧ ‖E v‖ ≤ 2*‖primary C v m N p‖ := by
  constructor
  · have he := norm_le_norm_sub_add (primary C v m N p) (E v); rw [norm_sub_rev] at he
    linarith [e.near v]
  have he := norm_le_norm_sub_add (E v) (primary C v m N p); linarith [e.near v,norm_nonneg (primary C v m N p)]

lemma unique_ (h : C.Makes) (hr : C.ref d ≤ m) {E : C.label d →ₗ[ℂ] C.label d}
    (he : Analyzed C d m N p E) (hp : m ≤ N) : Bijective E := by
  obtain ⟨D,hD,hv⟩ := charge h _ hr
  have H : LinearMap.ker E=⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hvv
    have hx := estimates he v
    rw [LinearMap.mem_ker.mp hvv,norm_zero, mul_zero] at hx
    apply norm_le_zero_iff.mp ((hv N p hp v).1.trans (by nlinarith only [hx.1,hD]))
  have H' := LinearMap.ker_eq_bot.mp H
  exact ⟨H',LinearMap.surjective_of_injective H'⟩

section
variable {S : Table C.book} (X : Columns C S d) (B : Series C)



-- Degrees: `grades` (weight,factors) in unscaled radial basis of F.
-- t/g power (inverse of final test's g/t normalization).
def desired (B : Series C) (v : (Maxwell.standard C.labels).Ref d) (k N p : ℕ) : C.label d :=
    let m := B.depth k
    let β := C.path.β N p m
    let q := (C.path.levels.budget m).threshold/(Real.sqrt β)⁻¹
    fun i => (((B.inversePitch k ^ ((C.labels.level d).grades i).1 * q ^ ((C.labels.level d).grades i).2):ℝ):ℂ)*v i

lemma desired_unit (k N p) : desired (d:=d) B (C.labels.level d).e0 k N p=(C.labels.level d).e0 := by
  ext i; by_cases hi : i=0 <;> simp [desired,Frame.e0,Pi.single_apply,hi,Frame.zero_degree]

lemma cost (h : C.Makes) (k : ℕ) (v : (Maxwell.standard C.labels).Ref d) :
    ∃ A : ℝ, 0 < A ∧ ∀ N p : ℕ, B.depth k ≤ N → ‖desired B v k N p‖ ≤ A := by
  let m := B.depth k
  let F := C.labels.level d
  let J := (2*C.path.levels.clock.hatBeta m)
  let f (g : ℝ) i := |B.inversePitch k| ^(F.grades i).1 * (Real.sqrt g) ^(F.grades i).2 * ‖v i‖
  let u := 1+ ∑ i, f J i
  have he (x i) : 0 ≤ f x i := by dsimp only [f]; positivity
  have hx : 0 < u := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => he _ i)
  refine ⟨u,hx,fun N p hN => ?_⟩
  apply (pi_norm_le_iff_of_nonneg hx.le).2
  intro i
  let β := C.path.β N p m
  have hβ : β ≤ J := (h.wilson.represents _ _ _ hN).band.2
  let q := (C.path.levels.budget m).threshold
  have hq : q ≤ 1 := (C.path.levels.budget m).threshold_le
  have hs : 0 < q := (C.path.levels.budget m).threshold_pos
  have hj : |q/(Real.sqrt β)⁻¹| ≤ Real.sqrt J := by
    rw [div_eq_mul_inv,inv_inv,abs_mul,abs_of_pos hs,abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) hq).trans (Real.sqrt_le_sqrt hβ)
  apply le_trans (b:=f J i) ?_ ((Finset.single_le_sum (fun i _=>he J i) (Finset.mem_univ _)).trans
    (le_add_of_nonneg_left zero_le_one))
  change ‖(↑(((B.inversePitch k)^((C.labels.level d).grades i).1) * ((q/(Real.sqrt β)⁻¹) ^ ((C.labels.level d).grades i).2)) : ℂ)*((show (C.labels.level d).Coeff from v) i)‖ ≤ _
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_pow]
  unfold f
  gcongr


end
end YM.Push.Corrected.Issue
