import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Tariffs
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Transit

/-!
# Common-chart estimates with explicit atomic inputs

Full K and hard indicators as in
Story.

Positive-order score/multiplier E inputs, on actual partial change
of variables: see `Admission`/`Deposit`.

Quantitative hypotheses on the
kernel & INDIVIDUAL overlaps before multiplying/returning to a single C;
speeds & relative exponential budgets can be issued even at a corner.

A
component may be very big; no multiplying a uniform polynomial in that
size for every occurrence.

Need earn `f` at full support incl footprint of
variant and pay K-hit bonus separately.

Doesn't infer any BudgetPoint from
derivative estimates inside the integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction.Story
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss Pressure Bid Tree YM.Push.SectorMeasure YM.Push.LogIdentity
open Component Arrival Desk Stamp Jets Toll
open scoped Topology BigOperators Classical MatrixOrder Tags ContDiff
variable {G : Gauge} {n g : Side} {S : StepData n g} {V I : Type}
variable {s : Setting G S} {F : Arrival.Flock V G g} {B : Brush V G n} (T : Story s F B I) (P : BudgetPoint)

structure Book where
  pins i (U : Config G n) (hu : Healthy P.threshold (B.u i).zone U) : Cabin (T.bath (Sum.inl i))

def bonus (κ : ℝ) : Fruit → ℝ := Sum.elim (fun _=>1) (fun _=>κ)

abbrev height (i : Fruit) := Toll.volume T.A P i

def salary (R K H : ℝ) (l : ℕ) (f : I → ℝ) (i : Fruit) := Toll.transferPrice P R K H l * T.A.feast f (Toll.level P l) P.B i

/-- An earlier field target. At a fixed chosen Book, root spectral bound
on full arguments when eligible; common appointment choices for hard
coordinates in each unforced coefficient. The size bound permits many
positions per site at fixed L, but pays genuine total cost H. -/
structure Admission (Y : Book T P) (K H : ℝ) : Prop where
  coverage i θ U : openTo (B:=B) P U i → Ceiling ((T.bath i).cov U θ) K
  count i : 1+(Fintype.card (T.bath i).Line:ℝ) ≤ H*(1+height T P i)
  pins i U (h : Healthy P.threshold (B.u i).zone U) : Nonempty ((Y.pins i U h).Around (fun U => T.raw U (Sum.inl i)) U P.order)
  ink i U : openTo (B:=B) P U i → Measurable (uncurry (T.raw U i))
  warm i U : openTo (B:=B) P U i → Measurable (uncurry ((T.bath i).warm U))

variable [Fintype V]

def note (i : Fruit) (ζ : V → ℂ) := Stamp.beat (calls B i) ζ

def column (i : Fruit) (ζ : V → ℂ) (θ : (T.bath i).tag) (z : (T.bath i).Play) (U : Config G n) :=
    Stamp.beat (calls B i) ζ * T.raw U i θ z

def coded (i : Fruit) (ζ : V → ℂ) (θ : (T.bath i).tag) (z : (T.bath i).Play) (j : I) (U : Config G n) :=
    Stamp.beat (T.A.hue j) ζ * T.factor i j θ z U

def shifted (i : Fruit) (C : Cabin (T.bath i)) (ζ : V→ℂ) (p : C.State) (j : I) (U : Config G n) :=
    T.coded i ζ p.1 (C.retrace p U) j U

lemma arrives_in (i : Fruit) (ζ : V→ℂ) (θ z U) : T.column i ζ θ z U = ∏ j∈T.A.bud i, T.coded i ζ θ z j U := by
  unfold column coded raw; rw [T.A.full i,Stamp.beat_pile,prod_mul_distrib]

/-- Jointly applicable, after charging the input literals by actual
amounts at ζ. A single Pool for every invocation inside each conditional
component, including pre-appointed distinct trigger nodes. Estimates only
needed when a term might contribute. Kernel score is the *pinned marginal
kernel*, not a fresh Gaussian multiplier fit at each factor (and separate
from ratio & Jacobian & counterterm letters in `factor`). -/
structure Deposit (Y : Book T P) (R K κ : ℝ) (l : ℕ) (ζ : V → ℂ) (f : I → ℝ) : Prop where
  soft i U (h : Healthy P.threshold (B.u i).zone U) (θ : (T.bath (Sum.inl i)).tag) :
      let a : Fruit := Sum.inl i
      let c := Y.pins i U h
      ∃ p : Pool I (T.bath a).Line, p.Funded (T.A.bud a) K (bonus κ a) f ∧ ∀ z : (T.bath a).Play,
        let x := c.pickUp θ U z
        z ∈ c.pin.trace (c.shift θ U) → (∃ v : List (Directions G n), v.length ≤ P.order ∧ (∀ A∈v,P.dirBound (B.u i).anchor A) ∧
          note (B:=B) a ζ * leftDerivs (c.cross (fun W => T.raw W a) x) v U ≠ 0) →
          let r:=Toll.pace R (height T P a) l z
          p.occurring (T.A.bud a) z ∧
            Band P.order (P.dirBound (B.u i).anchor) U r (c.rate x U) (fun W => (c.rate x W:ℂ)) ∧
              ∀ j∈T.A.bud a,∃ x₀∈ ends B a, Band P.order (P.dirBound x₀) U r (p.meter z j) (T.shifted a c ζ x j)
  hard i U (θ : (T.bath (Sum.inr i)).tag) : let a : Fruit := Sum.inr i
      ∃ p : Pool I (T.bath a).Line,p.Funded (T.A.bud a) K (bonus κ a) f ∧ ∀ z : (T.bath a).Play,
        T.column a ζ θ z U≠0 → p.occurring (T.A.bud a) z ∧ ∀ j∈T.A.bud a, ‖T.coded a ζ θ z j U‖ ≤ p.meter z j

namespace Book
variable {T P} {Y : Book T P}
lemma unwind (i : Fruit) (U : Config G n) (c : Cabin (T.bath i)) (h : c.Around (fun W => T.raw W i) U P.order)
    (v : List (Directions G n)) (hv : v.length ≤ P.order) (θ) (ζ : V→ℂ) :
    Measurable (c.post (fun W => T.raw W i) (note (B:=B) i ζ) U v θ) := by
  let m := c.shift θ U; let w := c.copy θ U; let C := (T.bath i).cov U θ; let z := (CFC.sqrt C *ᵥ ·)
  let x u := c.pickUp θ U (z u)
  have hx : Measurable x := measurable_const.prodMk ((c.pin.fetch_meas m w).comp (measurable_matVec _))
  exact ((h.clean.fee_meas m (C:=C)).comp (measurable_matVec _)).smul (((h.packed v hv).comp hx).const_mul _)

private lemma shifted_eq {i U} {c : Cabin (T.bath i)} (h : c.Around (fun W => T.raw W i) U P.order) (x : c.State) {v ζ}
    (hv : v.length ≤ P.order) (he : note (B:=B) i ζ * leftDerivs (c.cross (fun W => T.raw W i) x) v U ≠ 0) :
    note (B:=B) i ζ * leftDerivs (c.cross (fun W => T.raw W i) x) v U =
      leftDerivs ((fun W => (c.rate x W:ℂ)) * ∏ j∈T.A.bud i, T.shifted i c ζ x j) v U := by
  rw [← scaled_left]; apply Jets.agrees _ v
  filter_upwards [h.reheated hv he] with V hV
  rw [hV, Pi.mul_apply,Finset.prod_apply]; exact congrArg _ (T.arrives_in i ζ _ _ V)

private lemma release_bound {R K κ : ℝ} {l ζ f} {i : ℕ} (d : Deposit T P Y R K κ l ζ f) {U : Config G n}
    (hR : 1≤R) (he : Healthy P.threshold (B.u i).zone U) (v : List (Directions G n)) (θ : (T.bath (Sum.inl i)).tag) :
    let a : Fruit:=Sum.inl i; let C := (T.bath a).cov U θ; let c:=Y.pins i U he
    C.PosDef → c.Around (fun W => T.raw W a) U P.order → v.length ≤ P.order → (∀ D∈v,P.dirBound (B.u i).anchor D) →
    ∃ p : Pool I (T.bath a).Line, p.Funded (T.A.bud a) K (bonus κ a) f ∧ ∀ y,
      let z := CFC.sqrt C *ᵥ y
      let u := c.post (fun W => T.raw W a) (note (B:=B) a ζ) U v θ y
      u≠0 → ‖u‖ ≤ (Toll.velocity P R)^P.order * (1+height T P a)^Toll.order P l * (1+squares z)^degree P l *
        ∏ i∈T.A.bud a,p.meter z i ∧ p.occurring (T.A.bud a) z := by
  intro a C c hc h hv hV
  obtain ⟨p,hp,hf⟩:=d.soft i U he θ
  refine ⟨p,hp,?_⟩; intro y z u hx
  let x := c.pickUp θ U z; let t:=c.pin.faceFee C (c.shift θ U) z
  let g := note (B:=B) a ζ * leftDerivs (c.cross (fun W => T.raw W a) x) v U
  have hu : u=t • g := rfl
  have hi : z∈c.pin.trace (c.shift θ U) := Classical.byContradiction fun he' => hx (by rw [hu, show t=0 from if_neg he',zero_smul])
  have hg : g≠0 := by intro h; exact hx (by rw [hu,h,smul_zero])
  obtain ⟨hE,hQ,hg'⟩:=hf z hi ⟨v,hv,hV,hg⟩
  refine ⟨?_,hE⟩
  have hJ := Toll.stretched T.A P z a (B.u i).anchor U R l hR ((B.u i).origin) _ _ _ _ hQ hg' v hv hV
  have ht := h.clean.reimbursed hc (c.copy θ U) hi
  rw [hu,norm_smul_of_nonneg (h.clean.coins_pos hc _ _)]
  exact (mul_le_mul_of_nonneg_left ((congrArg (‖·‖) (shifted_eq h x hv hg)).trans_le hJ) (h.clean.coins_pos hc _ _)).trans_eq (by rw [←mul_assoc, show t*c.rate x U = 1 from ht,one_mul])
variable {R K H κ : ℝ} (hR : 1≤R) (hK : 0≤K) (hH : 1≤H) {l ζ f} (ad : T.Admission P Y K H)
    {Q : Rep G g} (census : T.Census Q P) (d : Deposit T P Y R K κ l ζ f)

include d ad hR hK hH in
private lemma soft_budget {U : Config G n} (i : ℕ) (he : Healthy P.threshold (B.u i).zone U) (v : List (Directions G n))
    (θ : (T.bath (Sum.inl i)).tag) :
    let a : Fruit:=Sum.inl i; let c:=Y.pins i U he
    c.Around (fun W => T.raw W a) U P.order → ((T.bath a).cov U θ).PosDef → v.length ≤ P.order → (∀ D∈v,P.dirBound (B.u i).anchor D) →
    let u := c.post (fun W => T.raw W a) (note (B:=B) a ζ) U v θ
    Integrable u (standard _) ∧ (∫ y, ‖u y‖ ∂standard _) ≤ T.salary P R K H l f a := by
  intro a c h hc hv hV u
  obtain ⟨pool,hP,hp⟩:= release_bound d hR he v θ hc h hv hV
  have hm : 0≤ (velocity P R)^P.order := pow_nonneg ((velocity_one _ hR).trans' zero_le_one) _
  have he' := hP.joint (volume_pos T.A P a) hm hK hH (ad.count a) hc (ad.coverage _ θ U he) _ _ u
    (unwind a U c h v hv θ ζ) hp
  refine ⟨he'.1,he'.2.trans_eq ?_⟩
  rw [show bonus κ a = 1 from rfl, one_mul,salary,Pasture.feast,transferPrice,level,Toll.volume]; unfold a; ring

include d ad hR hK hH census in
lemma soft_prices {U : Config G n} (i : ℕ) (he : Healthy P.threshold (B.u i).zone U) (v : List (Directions G n)) (hv : v.length ≤ P.order)
    (hV : ∀ D∈v,P.dirBound (B.u i).anchor D) : ‖leftDerivs ((B.u i).stamp.tell ζ) v U‖ ≤ T.salary P R K H l f (.inl i) := by
  let a : Fruit := .inl i; obtain ⟨h⟩:= ad.pins i U he
  have hh x := soft_budget hR hK hH ad d i he v x h (census.positive _ a _ he) hv hV
  have hv := h.charged v hv (note (B:=B) a ζ)
  have heq : (B.u i).stamp.tell ζ =ᶠ[𝓝 U] note (B:=B) a ζ • (fun W => (T.bath a).readout W (T.raw W a)) := by
    filter_upwards [census.soft _ U he] with W hw; exact congrArg (note (B:=B) a ζ * ·) hw
  rw [Jets.agrees heq v,hv]
  simpa only [a,probReal_univ,mul_one] using (norm_integral_le_of_norm_le_const (μ:=(T.bath a).bill) (Eventually.of_forall fun x =>
    (norm_integral_le_integral_norm _).trans (hh x).2))

include d ad hR hK hH census in
private lemma singleAt {U : Config G n} (a : Fruit) (he : openTo (B:=B) P U a) (θ : (T.bath a).tag) :
    let u (z) := T.column a ζ θ ((T.bath a).warm U θ z) U
    Integrable u (standard _) ∧ (∫ y, ‖u y‖ ∂standard _) ≤ bonus κ a * T.salary P R K H l f a := by
  intro u
  have hu : Measurable u := measurable_const.mul ((ad.ink a U he).comp (measurable_const.prodMk (measurable_matVec _)))
  obtain i|i:=a
  · obtain ⟨h⟩:=ad.pins i U he
    have hv:=soft_budget hR hK hH ad d i he [] θ h (census.positive U _ _ he) (Nat.zero_le _) (by simp)
    have he (y) : ‖u y‖ = _ := (norm_mul ..).trans (h.norm_vacuum θ y (note (B:=B) (.inl i) ζ)).symm
    simp_rw [he,show bonus κ (.inl i)=1 from rfl,one_mul]
    exact ⟨hv.1.mono hu.aestronglyMeasurable (Eventually.of_forall fun i => (he i).le), hv.2⟩
  let a : Fruit := .inr i; obtain ⟨pool,hP,hp⟩:=d.hard i U θ
  have hm : 1≤ (velocity P R)^P.order := one_le_pow₀ (velocity_one _ hR)
  have hd := volume_pos T.A P a
  have hh := hP.joint hd (hm.trans' zero_le_one) hK hH (ad.count a) (census.positive U a θ he)
    (ad.coverage _ θ _ he) (Toll.order P l) (degree P l) u hu (by
      intro y hy z; have hz : 0≤squares z:=Schur.sumSq_nn _
      obtain ⟨hE,hv⟩:=hp z hy
      refine ⟨?_,hE⟩
      calc
        _ = ∏ j∈T.A.bud a,‖T.coded a ζ θ z j U‖ := by unfold u; rw [T.arrives_in,norm_prod]; rfl
        _ ≤ ∏ j∈T.A.bud a,pool.meter z j := prod_le_prod (fun j _ => norm_nonneg _) hv
        _ ≤ _ := by
          have h1 := one_le_mul_of_one_le_of_one_le hm (one_le_pow₀ (by linarith : 1 ≤ 1+Toll.volume T.A P a) (n:=Toll.order P l))
          exact le_mul_of_one_le_left (prod_nonneg (hP.positive z)) (one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ (by linarith))))
  refine ⟨hh.1,hh.2.trans_eq ?_⟩
  rw [salary,Pasture.feast,transferPrice,level,Toll.volume]; unfold a; ring

include d ad hR hK hH census in
lemma hard_prices (U : Config G n) (i : ℕ) : ‖(B.d i).tell ζ U‖ ≤ κ*T.salary P R K H l f (.inr i) := by
  let a : Fruit:=.inr i
  rw [Stamp.tells,census.hard i U, Bath.readout, ← integral_const_mul]; unfold Bath.sectionAt; simp_rw [← integral_const_mul]
  exact (norm_integral_le_of_norm_le_const (Eventually.of_forall fun θ => (norm_integral_le_integral_norm _).trans
    (singleAt hR hK hH ad census d a (U:=U) trivial θ).2)).trans_eq (by rw [probReal_univ,mul_one]; rfl)

include d ad hR hK hH census in
theorem costs (hZ : ∀ i, ζ i ≠ 0) {t r : ℝ} (hr : 0≤r) (ht : 0≤t) (hB : Cluster.siteUnit P.B*t ≤ 1)
    (hf : Ac.Hit T.A.sites P.B f (r+2) t) (hk : 0≤κ) (U : Config G n) :
    (∀ i, openTo (B:=B) P U i → (T.bath i).Usable U (T.raw U i)) ∧ Summable (T.weighing ζ P U) := by
  let X (i : Fruit) := T.bath i
  have hx i (hi : openTo (B:=B) P U i) := singleAt hR hK hH ad census d _ hi
  have he (i : Fruit) : note (B:=B) i ζ ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hZ _))
  have hu (i) (h : openTo (B:=B) P U i) : (X i).Usable U (T.raw U i) := by
    let g (p : (X i).tag × (X i).Play) := T.raw U i p.1 ((X i).warm U p.1 p.2)
    let c:= note (B:=B) i ζ
    have hg : Measurable g := (ad.ink i U h).comp (measurable_fst.prodMk (ad.warm i U h))
    have hw θ := hx i h θ
    have hl θ : Integrable (fun y => c*g (θ,y)) (standard _) := (hw θ).1
    refine ⟨ad.ink i U h,fun θ => (integrable_smul_iff (he i) _).mp (hl θ), (integrable_smul_iff (μ:=(X i).law) (he i) g).mp ?_⟩
    apply (integrable_prod_iff (hg.const_mul c).aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hl, ?_⟩
    apply Integrable.of_bound (C:=bonus κ i * T.salary P R K H l f i)
      (StronglyMeasurable.integral_prod_right (ν:=standard _) (f:=Function.curry (fun p => ‖c * g p‖))
        (hg.const_mul c |>.norm.stronglyMeasurable)).aestronglyMeasurable
    exact Eventually.of_forall fun θ => (Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)).le.trans (hw θ).2
  refine ⟨hu,?_⟩
  have hl := (Absolute.burden T.A.origin hf).1
  have hs i : 0≤T.salary P R K H l f i := mul_nonneg (transfer_pos P R K H l hR hK hH) (T.A.feast_nn hl ..)
  have hh := Absolute.account (X:=ends B) (fun i => ?_) (T.A.places (level P l) P.B hr ht hB hf) hr
  swap
  · obtain i|i:=i
    · exact ⟨(B.u i).anchor,(B.u i).origin⟩
    exact (B.pack i).property.1.mono (B.pack i).property.2
  refine ((hh.mul_left (transferPrice P R K H l)).mul_left (1+κ)).of_nonneg_of_le ?_ fun i => ?_
  · intro i; unfold weighing; split; exact mul_nonneg (norm_nonneg _) (Bath.mass_pos ..); rfl
  unfold weighing; change _ ≤ (1+κ)*(salary ..)
  split
  · rename_i he
    have hi : bonus κ i ≤ 1+κ := by cases i <;> unfold bonus <;> simp [hk]
    apply le_trans _ (mul_le_mul_of_nonneg_right hi (hs i))
    rw [Bath.mass,Bath.readout,← integral_const_mul]; unfold Bath.sectionAt; simp_rw [← integral_const_mul,← norm_mul]
    apply (integral_mono_of_nonneg (Eventually.of_forall fun _=>integral_nonneg (fun _=>norm_nonneg (_*_))) (integrable_const _)
      (Eventually.of_forall fun θ => (hx i he θ).2)).trans_eq
    simp
  exact mul_nonneg (by positivity) (hs i)

include d ad hR hK hH census in
theorem product_cost {t r u : ℝ} (hr : 0≤r) (ht : 0≤t) (hB : Cluster.siteUnit P.B*t ≤ 1)
    (hf : Ac.Hit T.A.sites P.B f (r+2) t) (hb : Toll.transferPrice P R K H l*(Pasture.sizeTax (Toll.level P l)*(Real.exp t-1)) ≤ u) :
    T.A.ProductCost P ζ u r κ := by
  have hl := (Absolute.burden T.A.origin hf).1
  have he := transfer_pos P R K H l hR hK hH
  exact ⟨hr,Toll.level P l,Toll.transferPrice P R K H l,t,f,he,ht,hB,hb,hf,fun i => ⟨mul_nonneg he (T.A.feast_nn hl ..),
    fun _ he v hv hV => soft_prices hR hK hH ad census d i he v hv hV⟩, fun i U => hard_prices hR hK hH ad census d U i⟩
end Book
end YM.ProofPorts.CommonComplexProduction.Story
