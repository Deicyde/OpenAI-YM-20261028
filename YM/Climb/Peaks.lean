import YM.Climb.Tests

/-!
# Kernel comparison concentration consumer from finite snapshots
-/
set_option autoImplicit false
noncomputable section
namespace YM.Climb
open Filter Set Function Analysis Table Maxwell Spin
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable {M R : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]

lemma survive (P : Submodule ℝ M) (F : M→L[ℝ] R) (Y : ℕ → M→L[ℝ] R) (h : Tendsto Y atTop (𝓝 F)) (x : M) (_hp : x∈P)
    (he : x≠0) (hx : ∀ y∈ P,F y=0 ↔ ∃ c : ℝ, y=c • x) :
    ∀ᶠ i in atTop,∀ y∈ P,Y i y=0 → y ≠ 0 → ∀ z∈ P,Y i z=0 → ∃ c : ℝ,z=c • y := by
  obtain ⟨ℓ,hℓ⟩ := Module.Projective.exists_dual_ne_zero ℝ he
  let L := ℓ.toContinuousLinearMap
  let A (g : M→L[ℝ] R) := (g.prod L).comp P.subtypeL
  have hh : Injective (A F) := by
    apply (LinearMap.ker_eq_bot (f := (A F).toLinearMap)).mp
    apply LinearMap.ker_eq_bot'.mpr; intro u hu
    have ha := congr_arg Prod.fst hu
    have ht := congr_arg Prod.snd hu
    obtain ⟨c,hc⟩ := (hx u u.property).mp ha
    change ℓ u.val=0 at ht; rw [hc,map_smul,smul_eq_mul,mul_eq_zero] at ht
    exact Subtype.ext (hc.trans (by rw [ht.resolve_right hℓ]; exact zero_smul ..))
  have hu : Continuous A := by
    have hc : Continuous (fun g : M→L[ℝ] R => g.prod L) := by
      let μ : (M→L[ℝ] R) →ₗ[ℝ] (M →L[ℝ] R × ℝ) := {
        toFun p := p.prod 0
        map_add' u w := by ext y <;> simp
        map_smul' a p := by ext y <;> simp }
      let v := (0 : M→L[ℝ] R).prod L
      suffices he : (fun g : M→L[ℝ] R => g.prod L) = (fun g : M→L[ℝ] R => μ g + v) by rw [he]; exact μ.continuous_of_finiteDimensional.add continuous_const
      funext g; ext j <;> simp [μ,v]
    exact hc.clm_comp continuous_const
  filter_upwards [(hu.continuousAt.tendsto.comp h).eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hh)] with i Hi
  intro y hy hw hN z hz hZ
  let u : P := ⟨y,hy⟩
  let v : P := ⟨z,hz⟩
  let a := A (Y i)
  change Injective a at Hi
  have hp : a u=(0,L y) := Prod.ext hw rfl
  have hv : a v=(0,L z) := Prod.ext hZ rfl
  have ht : L y≠0 := by
    intro h
    rw [h] at hp
    exact hN (congr_arg Subtype.val (Hi (hp.trans (map_zero a).symm)))
  let b := L z/L y
  have hb : v=b • u := by apply Hi; rw [map_smul,hv,hp]; exact Prod.ext (smul_zero ..).symm (div_mul_cancel₀ _ ht |>.symm)
  exact ⟨b, congr_arg Subtype.val hb⟩

variable {G : Gauge} {L : Register G} {S : Table L} {d : ℕ}

/-- Matrix row zero all jets for each d. -/
def transverse (X : Parts S) := ∀ (d : ℕ) (s : Scene S d), s.lens (leaves X d)=0

-- FD norm conventions
example : NormedSpace ℝ ((Bel L).Field d) := inferInstance
example : FiniteDimensional ℂ ((Bel L).Field d) := inferInstance
-- bridge use Tower.Value types with TC
instance fds {G : Gauge} {L : Register G} {S : Table L} {d e} : FiniteDimensional ℝ (Matrix d e S) :=
  Module.Finite.trans ℂ _

lemma fixed_kernel (P : Select L d) {V : Scaling S} {h a} (Z : Subs P V)
    (W : DiffPlan S) (K : DiffPlan (Bel L)) (hx : V.Align W K h a (d+1)) (H : Ens P K a) (X Y : Parts S)
    (hp : ColorLaw X W h) (hq : ColorLaw Y W h) (he : leaves X d ≠ 0) (hu : Tendsto Z.moves atTop (𝓝 P.reads))
    (hw : ∀ᶠ i in atTop, Z.moves i (V.aisle i d (leaves X d))=0 ∧ Z.moves i (V.aisle i d (leaves Y d))=0) :
    ∃ c : ℝ, leaves Y d=c • leaves X d := by
  have hx' : ∀ᶠ i in atTop,∀ y ∈ Colors K a d, Z.moves i y=0 → y ≠ 0 → ∀ z∈ Colors K a d,Z.moves i z=0 → ∃ c : ℝ,z=c • y :=
    survive (M:=V0 L d) (R:=Fin P.m→ℂ) (Colors K a d) P.reads Z.moves hu (leaves K.deriv d) H.vec H.nz  (fun x hx => H.identifies x hx)
  obtain ⟨i,hi,hX,hY⟩ := (hx'.and hw).exists
  let T := V.aisle i d
  have ht : T (leaves X d) ∈ Colors K a d := V.toColor hx (hp.sight _) (Nat.lt_succ_self _) i
  obtain ⟨c,hc⟩ := hi _ ht hX (show T (leaves X d)≠0 from fun e => he (V.aisle_ext i d (e.trans T.map_zero.symm))) _
    (V.toColor hx (hq.sight _) (Nat.lt_succ_self _) i) hY
  exact ⟨c,V.aisle_ext i d (hc.trans (map_smul T _ _).symm)⟩

/-- Each d uses one setup of P.Selections, enough rows with rescaling. ColorLaw Persists. -/

def concentrated (W : DiffPlan S) (K : DiffPlan (Bel L)) (H : S.RealSpin) (a : (Bel L).RealSpin) (p : Parts S) (d : ℕ) :=
    ∃ (V : Scaling S) (P : Select L d) (s : Subs P V), V.Align W K H a (d+1) ∧ Ens P K a ∧
      Tendsto s.moves atTop (𝓝 P.reads) ∧
        ∀ᶠ i in atTop, s.moves i (V.aisle i d (leaves W.deriv d))=0 ∧ s.moves i (V.aisle i d (leaves p d))=0

lemma over_peak (W : DiffPlan S) (h : S.Hierarchy) (hp : W.Inclusions S) {X Y : Parts S} (hx : ColorLaw X W h.spin)
    (hy : ColorLaw Y W h.spin) {d D} (hw : d ≤ D) (c : ℝ) (he : leaves Y D=c • leaves X D) : leaves Y d=c • leaves X d := by
  ext1 i; ext1 u
  apply W.inject h.laws.toSymmetric hp (Nat.succ_le_succ hw)
  have hL := congr_arg (fun g : Vector D S => g i (W.rise hw u)) he
  change Y D i (W.rise hw u)=c • X D i (W.rise hw u) at hL
  rw [hx.incl _ D hw,hy.incl _ D hw] at hL
  change _= W.rise _ (c • X d i u)
  have ht := (W.rise (Nat.succ_le_succ hw)).restrictScalars ℝ |>.map_smul c (X d i u)
  exact hL.trans ht.symm

lemma extends_form (W : DiffPlan S) (K : DiffPlan (Bel L)) (H : S.Hierarchy) {a} (P : Parts S) (hw : W.Inclusions S) (hv : ColorLaw W.deriv W H.spin) (he : ColorLaw P W H.spin)
    (hp : ∃ D,∀ d≥D, concentrated W K H.spin a P d ∧ leaves W.deriv d≠0 ∧ leaves P d≠0) : ∃ c : ℝ, c≠0 ∧ ∀ d, leaves P d=c • leaves W.deriv d := by
  obtain ⟨D, hD⟩ := hp
  have hh d (h : D≤d) : ∃ c : ℝ, c≠0 ∧ leaves P d=c • leaves W.deriv d := by
    obtain ⟨⟨V,Y,Z,H1,H2,H3,H4⟩,H5,H6⟩ := hD d h
    obtain ⟨c,hc⟩ := fixed_kernel Y Z _ _ H1 H2 _ _ hv he H5 H3 H4
    exact ⟨c,fun e => H6 (hc.trans (by subst c; ext j k; simp)),hc⟩
  obtain ⟨c,hc,Ht⟩ := hh D le_rfl
  refine ⟨c,hc,fun d => ?_⟩
  rcases le_total D d with h|h
  · obtain ⟨p,ht,hp⟩ := hh d h
    have he' : p=c := (smul_left_injective ℝ (hD D le_rfl).2.1) ((over_peak W H hw hv he h p hp).symm.trans Ht)
    exact he' ▸ hp
  exact over_peak W H hw hv he h c Ht
end YM.Climb
