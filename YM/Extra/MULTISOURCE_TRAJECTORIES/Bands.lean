import YM.Extra.MULTISOURCE_TRAJECTORIES.Gather
import YM.Next.FOUNDATIONS.Regular
import YM.Next.FOUNDATIONS.SU2
import YM.Work.H03
/-!
# Active Bands from complete unmasked layers via exact attachment

Padding off-range addresses must still mention a nonempty allowed selection;
only use this representation with at least one marker in the alphabet. It
includes the degree-zero coefficient for the same Rep, without changing its
activities or scalar. Coincident markers if allowed still use distinct keys.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories
open Lattice Wilson RG Overlay Marker Function Finset MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section Code
variable {α M : Type*} [Countable α]

def pin (x : α) := (Countable.exists_injective_nat α).choose x
lemma pin_injective : Injective (pin : α → ℕ) := (Countable.exists_injective_nat α).choose_spec

def unpin (f : α → M) (blank : M) (i : ℕ) := Function.extend pin f (fun _ => blank) i
@[simp] lemma unpin_pin (f : α → M) (blank : M) (i : α) : unpin f blank (pin i) = f i :=
  pin_injective.extend_apply ..
lemma unpin_blank (f : α → M) (blank : M) {i : ℕ} (hi : i ∉ Set.range (pin : α → ℕ)) :
    unpin f blank i = blank := extend_apply' _ _ _ hi
end Code

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V} {P : Rep G n}

namespace Layers
variable {α : Type*} (X : Layers P R α)

def routed (i : ℕ) (c : X.Component) : Config G n → ℂ := if X.slot (Sum.inr c)=i then X.entry c else 0

section Encoding
variable [Countable α] [Nonempty V]

def bands : Bands R P where
  origins := X.origins
  units := X.units
  support := unpin X.region univ
  rays := unpin X.tag (R.fire (Classical.arbitrary V))
  H := unpin X.H 0
  marks _ := unpin X.stamp (R.fire (Classical.arbitrary V))
  entries i := unpin (X.routed i) 0

@[simp] lemma tagged_pin (U : Config G n) (i : ℕ) (c : X.Component) :
    X.bands.tagged i (pin c) U = if X.slot (.inr c)=i then X.cargo U (.inr c) else 0 := by
  simp only [Bands.tagged,bands,unpin_pin,routed,cargo,Sum.elim_inr]; split <;> simp

lemma tagged_blank (U : Config G n) (i : ℕ) {j : ℕ} (h : j ∉ Set.range (pin : X.Component → ℕ)) :
    X.bands.tagged i j U=0 := by
  simp [Bands.tagged,bands,unpin_blank _ _ h]

@[simp] lemma ray_pin (i : α) (U : Config G n) :
    X.bands.ray (pin i) U = Poly.send (X.tag i) (masked P.p.threshold (X.region i) (X.H i) U) := by
  simp only [Bands.ray,bands,unpin_pin]

lemma ray_blank {i : ℕ} (h : i ∉ Set.range (pin : α → ℕ)) (U : Config G n) :
    X.bands.ray i U=0 := by
  simp [Bands.ray,bands,unpin_blank X.H _ h,masked]

lemma each_eq {δ κ : ℝ} [Fintype α] (H : P.activities.Valid P.p δ κ) (U : Config G n) (i : ℕ) :
    X.bands.each i U = ∑' c : {c : X.Choice // X.slot c=i}, X.cargo U c.val := by
  have hs := (Poly.budgeted (fun _ : V => zero_lt_one (α:=ℝ)) (X.cargo_series H U) (fun _ => le_rfl)).1
  let f : X.Choice → Poly R := {c | X.slot c=i}.indicator (X.cargo U)
  change _ = ∑' c : ↥({c : X.Choice | X.slot c=i} : Set _), X.cargo U c.val
  rw [_root_.tsum_subtype]
  change _ = ∑' c,f c
  have H1 : HasSum (f ∘ Sum.inl) (Poly.send R.quiet (P.activities.K i U : ℂ)) := by
    convert hasSum_ite_eq i (Poly.send R.quiet (P.activities.K i U : ℂ)) using 1
    funext j; by_cases he : j=i <;> simp [f,comp_apply,he,Set.indicator,cargo]
  have heq : f ∘ Sum.inr = fun c : X.Component => X.bands.tagged i (pin c) U := by
    funext c; by_cases h : X.slot (.inr c)=i <;> simp [f,Set.indicator,h]
  have H2 : Summable (fun c : X.Component => X.bands.tagged i (pin c) U) := by
    rw [← heq]; exact (hs.indicator {c | X.slot c=i}).comp_injective Sum.inr_injective
  have HE : (∑' c : X.Component,X.bands.tagged i (pin c) U) = ∑' j,X.bands.tagged i j U :=
    pin_injective.tsum_eq (f:=fun j => X.bands.tagged i j U) (fun j hj => by by_contra hn; exact hj (X.tagged_blank U i hn))
  have H2' : HasSum (f ∘ Sum.inr) (∑' j,X.bands.tagged i j U) := by
    rw [← HE,heq]; exact H2.hasSum
  exact (H1.sum H2').tsum_eq.symm
end Encoding

private lemma healthy_final (s : Support n) : UsesFinal (G:=G) P.p.threshold s (Healthy P.p.threshold s) := by
  intro U W _ h
  simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,h]

lemma reads (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) (l : Letter α) :
    UsesFinal P.p.threshold (X.area l) (fun U => X.weight U l) := by
  cases l with
  | inl i => exact fun U W h he => congrArg Complex.ofReal (hK.reads i U W h he)
  | inr i =>
    change UsesFinal P.p.threshold (X.region i) (X.residual i)
    intro U W ha hf
    rw [residual, residual,healthy_final (P:=P) _ U W ha hf,(hX.regular i).sites U W ha]

lemma borel (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) (l : Letter α) : Measurable (fun U => X.weight U l) := by
  cases l with
  | inl i => exact Complex.continuous_ofReal.measurable.comp (hK.meas i)
  | inr i => exact Measurable.ite (healthy_closed P.p.threshold (X.region i)).measurableSet measurable_const (hX.regular i).borel

lemma symmetric (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) (l : Letter α) : GaugeInvariant (fun U => X.weight U l) := by
  cases l with
  | inl i => exact fun t U => congrArg Complex.ofReal (hK.sym i t U)
  | inr i => intro t U; simp [weight,residual,Healthy,(hX.regular i).symmetry t U]

lemma stamp_nonempty (hX : X.Anchored) (c : X.Component) : (X.stamp c).val.Nonempty := by
  obtain ⟨i,hi⟩ := c.property.mark
  exact (hX.proper i).mono (subset_biUnion_of_mem (fun i => (X.tag i).val) hi)

lemma stamp_home (h : Aperture P) (hX : X.Anchored) (c : X.Component) {s} (hs : s∈(X.stamp c).val) :
    X.origins s∈ (P.activities.forced (X.slot (.inr c))).support := by
  rw [← X.skin_slot _ h]; obtain ⟨i,hi,he⟩ := mem_biUnion.mp hs
  exact mem_biUnion.mpr ⟨Sum.inr i,mem_toRight.mp hi,hX.home i s he⟩

lemma entry_reads (h : Aperture P) (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) (c : X.Component) :
    UsesFinal P.p.threshold (P.activities.forced (X.slot (.inr c))).support (X.entry c) := by
  intro U W ha hf
  rw [entry,entry,Work.H03.eligible_reads _ _ (hK.reads_test _) U W ha hf]; congr 1
  apply prod_congr rfl; intro i hi
  apply Work.H03.reads_larger _ (X.reads hX hK i) U W ha hf
  rw [← X.skin_slot _ h]; exact subset_biUnion_of_mem X.area hi

lemma entry_meas (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) (c : X.Component) :
    Measurable (X.entry c) := by
  unfold entry
  exact Measurable.ite (Work.H03.eligible_measurable _ _ (hK.meas_test _))
    (Finset.measurable_fun_prod _ fun l _ => X.borel hX hK l) measurable_const

lemma entry_gauge (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) (c : X.Component) : GaugeInvariant (X.entry c) := by
  intro t U
  simp only [entry, Work.H03.eligible_gauge _ _ t U (hK.symtest ..), show ∀ l, X.weight (gauge t U) l = _ from fun l => X.symmetric hX hK l t U]

private lemma regular_zero (p : BudgetPoint) : p.Regular (n:=n) univ (0 : Config G n → ℂ) := by
  simpa using (Next.Foundations.regular_bound_sum (P:=p) (G:=G) (o:=(0:Site n)) (s:=univ)
    (∅ : Finset ℕ) (fun _ => 0) (fun _ => 0) (by simp)).1

lemma active [Countable α] [Nonempty V] (h : Aperture P) (hX : X.Ready) (hK : P.activities.ForcedFamily P.p) :
    X.bands.Active := by
  constructor
  · intro i; by_cases he : i∈Set.range (pin (α:=α))
    · obtain ⟨a,rfl⟩ := he; simpa only [bands,unpin_pin] using hX.proper a
    simp [bands,unpin_blank _ _ he,Census.fire]
  · intro i j; by_cases he : i∈Set.range (pin (α:=α))
    · obtain ⟨a,rfl⟩ := he; simpa only [bands,unpin_pin] using hX.home a j
    simp [bands,unpin_blank _ _ he]
  · intro i; by_cases he : i∈Set.range (pin (α:=α))
    · obtain ⟨a,rfl⟩ := he; simpa only [bands,unpin_pin] using hX.regular a
    rw [bands]; simp only [unpin_blank _ _ he]; exact regular_zero _
  · intro i j; by_cases hj : j∈Set.range (pin (α:=X.Component))
    · obtain ⟨a,rfl⟩ := hj; simpa only [bands,unpin_pin] using X.stamp_nonempty hX.toAnchored a
    simp [bands,unpin_blank _ _ hj,Census.fire]
  · intro i j; by_cases hj : j∈Set.range (pin (α:=X.Component))
    · obtain ⟨c,rfl⟩ := hj; by_cases he : X.slot (.inr c)=i
      · subst i; intro _ s; simpa only [bands,unpin_pin] using (fun hs => X.stamp_home h hX.toAnchored c (s:=s) hs)
      simp [bands,routed,he]
    simp [bands,unpin_blank _ _ hj]
  · intro i j; by_cases hj : j∈Set.range (pin (α:=X.Component))
    · obtain ⟨c,rfl⟩ := hj; simp only [bands,unpin_pin,routed]
      split
      next he => subst i; exact X.entry_reads h hX hK c
      exact fun _ _ _ _ => rfl
    simp only [bands,unpin_blank _ _ hj]; exact fun _ _ _ _ => rfl
  · intro i j U; by_cases hj : j∈Set.range (pin (α:=X.Component))
    · obtain ⟨c,rfl⟩ := hj; simp only [bands,unpin_pin,routed]
      split
      next he => subst i; unfold entry; split <;> simp [*]
      simp
    simp [bands,unpin_blank _ _ hj]
  · intro i j; by_cases hj : j∈Set.range (pin (α:=X.Component))
    · obtain ⟨c,rfl⟩ := hj; simp only [bands,unpin_pin,routed]; split
      · exact X.entry_meas hX hK c
      exact measurable_const
    rw [bands]; simp only [unpin_blank _ _ hj]; exact measurable_const
  intro i j; by_cases hj : j∈Set.range (pin (α:=X.Component))
  · obtain ⟨c,rfl⟩ := hj; simp only [bands,unpin_pin,routed]; split
    · exact X.entry_gauge hX hK c
    exact fun _ _ => rfl
  simp only [bands,unpin_blank _ _ hj]; exact fun _ _ => rfl

section Physical
variable [Fintype α] [Nonempty V] [Fintype V]

def logPart (U : Config G n) := (∑ i,Poly.send (R.fire i) (X.units i)) + ∑ i,Poly.send (X.tag i) (X.H i U)

lemma extra_pass (hX : X.Anchored) (U : Config G n) : Poly.pass (X.bands.extra U) *
    (∏ i, (1+Poly.send (X.tag i) (X.residual i U))) = Poly.pass (X.logPart U) := by
  rw [← pass_sum univ X.tag (fun i _ => hX.proper i)]
  have he : X.bands.extra U = (∑ i, Poly.send (R.fire i) (X.units i)) +
      ∑ i,Poly.send (X.tag i) (masked P.p.threshold (X.region i) (X.H i) U) := by
    unfold Bands.extra; rw [← pin_injective.tsum_eq (fun j hj => by by_contra hn; exact hj (X.ray_blank hn U)),tsum_fintype]; simp [bands,Bands.ray]
  have hq (f : α → ℂ) : (∑ i,Poly.send (X.tag i) (f i)).part R.quiet=0 := by
    rw [Poly.part_sum]; apply sum_eq_zero; intro i _
    rw [Poly.part_send]; exact if_neg (fun (h : R.quiet = X.tag i) => (hX.proper i).ne_empty (congrArg Subtype.val h.symm))
  rw [he, ← pass_add _ (hq (fun i => X.residual i U))]
  · congr 1
    rw [add_assoc, ← sum_add_distrib,logPart]; congr 1
    apply sum_congr rfl
    intro i _
    unfold residual; split
    next h => rw [masked_eq _ _ _ _ h,Poly.send_zero,add_zero]
    next h => rw [masked_ne _ _ _ _ h,Poly.send_zero,zero_add]
  · rw [Poly.part_plus,hq,add_zero,Poly.part_sum]; exact sum_eq_zero fun i _ => by simp [(R.fire_hot i).symm]

theorem exact_density [DecidableEq α] (h : Aperture P) (hx : X.Anchored) {δ κ : ℝ}
    (H : P.activities.Valid P.p δ κ) (U : Config G n) :
    X.bands.density U = (P.eval U : ℂ) • Poly.pass (X.logPart U) := by
  have hw (_ : V) : (0:ℝ)<1 := zero_lt_one
  have hc := X.cargo_series H U
  have hg := X.merged h hx H U
  have he := Packets.repack X.slot (P.activities.admissible P.p U) (X.cargo U) hg.summable (Poly.budgeted hw hc (fun _ => le_rfl)).1
  change HasSum _ (∑' s, X.gathered U s) at he
  rw [hg.tsum_eq] at he
  simp_rw [← X.each_eq H U] at he
  unfold Bands.density Bands.cluster Bands.packet
  rw [he.tsum_eq,Rep.eval,Complex.ofReal_mul,mul_smul]; congr 1
  rw [mul_left_comm,X.extra_pass hx U,← Poly.product_bead]; rfl
end Physical
end Layers
end YM.Extra.Trajectories
