import YM.SectorNext.VACUUM_NORMALIZATION.Bulk

/-!
# Scalar expulsion after first integrated gas

Takes literally the organized  fstgas (assembly from sector
integrals a SEPARATE upstream obligation). One additional attaching Mayer
address on every complete output support (not one per meeting with a
compulsory packet, nor multiplied again over flags). Prepares subsequent
connectivity-based K reconstruction; doesn't claim all derivative
bounds on E or that the addresses have already been merged. All
*selected* terms still have true inventory coverage etc here. Uniform
price on the forced ratio sum IN THIS normalization with native
radius/exponents. This doesn't charge large-field packets before the
assembly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.ReLog
open Lattice RG Wilson Finset Filter
open scoped Matrix.Norms.Frobenius Classical BigOperators Topology
variable {ι : Type*} {G : Gauge} {n : Side} (X : ι → Support n) (b : BudgetPoint)
  (E : ι → Config G n → ℝ) (d : Activities G n)

local notation "spots" => Leaf (Site n)

def pad (Q : Finset ℕ) := Q.biUnion fun i => (d.forced i).support

def clips (Q : Finset ℕ) := (univ:Finset (Support n)).filter fun i => ¬ Disjoint i (pad d Q)

/-- Exact first gas, organized with forced family selected first (distinct
addresses as always). No flagged uniform reference stipulated. Require
an actual assembly hypothesis equating this with terms from the Haar
integrals when applied. -/
def first (V : Config G n) := ∑' Q : Finset ℕ, d.gasOccurrence b Q V * fumes X (herald X b E V) (univ\pad d Q)

/-- One address i with transformed value, even if covers holes and meets
several d's. Overlap eligibility retained using Spent.skins of the VERY
same d occurrences (no query of a different label realization). -/
def attaches (i : spots) (V : Config G n) := Real.exp (locked X b E i V + adjust X b E i V) - 1

def remains (Q : Finset ℕ) (V : Config G n) := d.gasOccurrence b Q V * ∏ i∈clips d Q,(1+attaches X b E i V)

private lemma accounted_flag (V : Config G n) (Q : Finset ℕ) (h : d.gasOccurrence b Q V≠0) : flags b.threshold V ⊆ pad d Q := by
  have ha : d.admissible b V Q := by
    by_contra he; exact h (by simp [Activities.gasOccurrence,he])
  rw [←ha.2]; intro i hh; obtain ⟨j,hj,hk⟩ := mem_biUnion.mp hh
  exact mem_biUnion.mpr ⟨j,hj,(d.forced j).inventory_sup hk⟩
lemma at_zero (i : spots) : locked X b E i 1 = raw X E i 1 := masked_eq _ _ _ _ (by
  unfold Healthy; apply Finset.disjoint_left.mpr
  intro t _ ht; obtain ⟨p,-,hp⟩ := (flags_spec ..).mp ht; simp [faceValue,square,travel] at hp; exact hp.not_ge b.threshold_pos.le)

/-- Reassembled per selected Q. Therefore reconstructs under `tsum`, even
before proving bounds. -/
theorem billing {v : ι→ℝ} (t : Tags X b E v) (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v)
    (V : Config G n) (Q : Finset ℕ) :
    let g := d.gasOccurrence b Q V
    g*fumes X (herald X b E V) (univ\pad d Q) =
      Real.exp (-(∑ i : spots,raw X E i 1) - ∑ i : spots,devalue X b E i V) * remains X b E d Q V := by
  intro g
  let c := clips d Q
  obtain ⟨-,-,-,H⟩ := intake X t M h
  let Z := fumes X (herald X b E V)
  have he := (H V (pad d Q)).2.2
  have hp := (H V univ).2.1
  have hz : (univ:spots).powerset = Finset.univ := by ext; simp
  rw [hz] at hp
  by_cases hh : g=0
  · change _ = _ * (g * _); simp [hh]
  have hx : ∑ i : spots, adjust X b E i V = ∑ i∈c, adjust X b E i V := by
    symm; apply Finset.sum_subset (subset_univ ..)
    intro i _ hi
    have hs : Disjoint i (pad d Q) := by
      by_contra e; exact hi (mem_filter.mpr ⟨mem_univ _,e⟩)
    rw [adjust,if_pos (show Healthy _ i V from Disjoint.mono_right (accounted_flag b d V Q hh) hs)]
  have ht := sum_congr (s₁ := (univ:Finset spots)) (s₂:=univ) rfl (fun i _ => adjustment X b E i V)
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_neg_distrib, Finset.sum_neg_distrib,hx] at ht
  change g*Z _=_
  change Z (univ\pad d Q)=Z univ * Real.exp (∑ i∈c,locked X b E i V) ∧ _ at he
  change Z (univ:spots)=_ at hp
  rw [he.1,hp,ht]
  have ha : ∀ i, 1+attaches X b E i V = Real.exp _ := fun i=>show _=Real.exp (locked X b E i V+adjust X b E i V) by unfold attaches; ring
  change _ = _ * (g*∏ i∈c,_)
  simp_rw [ha,Real.exp_add,Finset.prod_mul_distrib,←Real.exp_sum]; ring_nf


lemma total_reassemble {v : ι→ℝ} (t : Tags X b E v) (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v) (V : Config G n) :
    first X b E d V = Real.exp (-(∑ i : spots,raw X E i 1) - ∑ i : spots,devalue X b E i V) * ∑' Q, remains X b E d Q V := by
  unfold first; simp_rw [show ∀ Q, d.gasOccurrence b Q V*fumes X (herald X b E V) (univ\pad d Q) = _ from fun Q => billing X b E d t M h V Q]; rw [tsum_mul_left]








-- Even the Mayer terms, with common envelope *before* fields.
lemma safe_attachment {v : ι→ℝ} (t : Tags X b E v) (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v) :
    let g := ceiling (fumes X (-v))
    (∀ i : spots, 0≤g i) ∧
      (∀ V i, |attaches X b E i V| ≤ 2*g i) ∧ (∀ x : Site n,
        ∑ i∈(univ:Finset (Support n)).filter (fun i=>x∈i),native M A i*g i ≤ a) := by
  intro g
  obtain ⟨h₁,h₂,h₃,-⟩ := intake X t M h
  have hg (i : spots) : 0 ≤ g i := (abs_nonneg _).trans (h₂ (1:Config G n) i)
  refine ⟨hg,fun V i => ?_,h₃⟩
  let r := locked X b E i V + adjust X b E i V
  have hr : |r| ≤ g i ∧ |r|≤1 := by
    by_cases h0 : i=(∅:spots)
    · subst i
      rw [show r=0 by unfold r; rw [h₁]; unfold adjust; simp [Healthy]]
      simp only [abs_zero]; exact ⟨hg _,zero_le_one⟩
    have he : |r| ≤ g i := by
      by_cases H : Healthy b.threshold i V
      · unfold r adjust; rw [if_pos H,add_zero]; exact h₂ _ _
      unfold r adjust locked; rw [if_neg H,masked_ne _ _ _ _ H,zero_add,← at_zero X b E i]; exact h₂ _ _
    have hk : 1 ≤ roof M := by unfold roof; norm_cast; apply one_le_pow₀; omega
    have hw : a ≤ 1 := (le_mul_of_one_le_right h.pos hk).trans h.wires
    obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have hy := single_le_sum (f:=fun i => native M A i*g i) (s:= (univ:Finset (Support n)).filter fun i=>x∈i)
      (fun j hj=>mul_nonneg (Real.exp_pos _).le (hg j)) (mem_filter.mpr ⟨mem_univ _,hx⟩)
    have hl := (le_mul_of_one_le_left (hg i) (native_rate M h.nonnegative |>.pos i)).trans (hy.trans ((h₃ x).trans hw))
    exact ⟨he,he.trans hl⟩
  apply (Real.abs_exp_sub_one_le hr.2).trans; gcongr; exact hr.1

-- hit of correction at *Q-skin*, pay once per hit
lemma gust {v : ι→ℝ} (t : Tags X b E v) (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v)
    (Q : Finset ℕ) (V : Config G n) :
    ∑ i ∈ clips d Q, |attaches X b E i V| ≤ 2* a * (pad d Q).card := by
  let g := ceiling (fumes X (-v))
  obtain ⟨hg,hr,hl⟩ := safe_attachment X b E t M h
  let u := fun i=> native M A i*g i
  have h0 i : 0≤u i := by have he : 0 ≤ g i := hg _; unfold u native; positivity
  calc
    _ ≤ ∑ i∈clips d Q,(2:ℝ)* ∑ x∈pad d Q,if x∈i then u i else 0 := by
      refine sum_le_sum fun i hi=> (hr _ _).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (le_mul_of_one_le_left (hg i) (native_rate M h.nonnegative|>.pos i)).trans
      obtain ⟨x,h₁,h₂⟩ := Finset.not_disjoint_iff.mp (mem_filter.mp hi).2
      have hx := single_le_sum (f:=fun x=>if x∈i then u i else 0) (fun j _=>by split; exact h0 _; rfl) h₂
      rw [if_pos h₁] at hx; exact hx
    _ ≤ _ := by
      rw [← Finset.mul_sum,sum_comm,mul_assoc, mul_comm a]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [← nsmul_eq_mul, ← sum_const]
      apply sum_le_sum; intro x _; apply le_trans _ (hl x)
      rw [← Finset.sum_filter]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (subset_univ _)) fun i _ _=> h0 _












/-- Fstgas at trivial output field. Needed for reading v' already at
first-gas stage, before the later exact Hessian and indicator moves. -/
theorem first_flat {v : ι→ℝ} (t : Tags X b E v) (M : ℕ) {A a δ : ℝ} (h : Fund X M A a δ v) :
    first X b E d 1 = Real.exp (-∑ i : Leaf (Site n),raw X E i 1) := by
  let Z := fumes X (herald X b E 1)
  obtain ⟨-,-,-,H⟩ := intake X t M h
  have he := (H (1:Config G n) univ).2.1
  change Z _ = _ at he
  have hz : (univ:spots).powerset = Finset.univ := by ext i; simp
  simp_rw [at_zero,hz] at he
  rw [←he,first,tsum_eq_single ∅]
  · have h0 : d.gasOccurrence b ∅ (1:Config G n)=1 := by
      unfold Activities.gasOccurrence; rw [if_pos]
      · exact prod_empty
      have hh : flags b.threshold (1:Config G n)=∅ := eq_empty_iff_forall_notMem.mpr fun i hi => by
        obtain ⟨p,-,hp⟩ := (flags_spec ..).mp hi; simp [faceValue,square,travel] at hp; exact hp.not_ge b.threshold_pos.le
      simp [Activities.admissible,hh]
    simp [h0,pad,Z]
  intro i hi
  have h0 : d.gasOccurrence b i (1:Config G n)=0 := by
    unfold Activities.gasOccurrence; apply if_neg
    intro h; obtain ⟨j,hj⟩ := nonempty_iff_ne_empty.mpr hi; obtain ⟨x,hx⟩ := (d.forced j).inventory_ne
    have ht : x∈flags b.threshold (1:Config G n) := h.2 ▸ mem_biUnion.mpr ⟨j,hj,hx⟩
    obtain ⟨p,-,hp⟩ := (flags_spec ..).mp ht; simp [faceValue,square,travel] at hp; exact hp.not_ge b.threshold_pos.le
  rw [h0,zero_mul]

end YM.SectorNext.Vacuum.ReLog
