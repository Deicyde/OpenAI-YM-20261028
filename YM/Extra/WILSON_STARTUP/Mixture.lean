import YM.Extra.WILSON_STARTUP.Cylinder
import YM.Extra.WILSON_STARTUP.LinearMarkers
import YM.Next.FOUNDATIONS.Split


/-!
# Initialization of a simultaneous-marker cutoff overlay

Square-zero, distinct address tags even for equal coefficients. Allowed
selections include every singleton and are downward closed. Actual mask tests
on each support and full Hᵛ, side independent of potential conflicts. If a
probe fails its good test, add it exactly once inside the unique packet(s),
with the same scalar in each mode-product. No stationarity, β or recursion
assumed from its Lane packaging. Uses `Wide` when product not zero.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Mixture
open Function Filter RG Lattice Wilson Ovens Marker LinearMarkers Finset Overlay Source Padded Labels
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {d : ℕ} {F : Frame G d}

variable (R : Census V) (S : SectionData F) (o : V → Site n) (P : Rep G n) (v : V → F.Coeff)

abbrev Positive (R : Census V) := {i : R.Mode // i.val.Nonempty}
scoped instance : Nonempty (Positive R) := Nonempty.map (fun v : V => ⟨R.fire v,Finset.singleton_nonempty v⟩) inferInstance

def test (i : V) (j : ℕ) := Mark.guard P (S.footprint (o i)) j

def entire (U : Config G n) (i : V) := Mark.realMaskFree S (o i) P (v i) U
def free (U : Config G n) (i : V) := Mark.probe S (o i) P (v i) U
def works (i : V) := masked P.p.threshold (S.footprint (o i)) (Mark.probe S (o i) P (v i))
def diffuse (U : Config G n) : V → ℂ := (fun i => v i 0) + (fun i => works S o P v i U)

def measured (j : ℕ) (U : Config G n) (i : V) : ℂ := if test S o P i j then free S o P v U i else 0

def parcel (j : ℕ) (i : Positive R) (U : Config G n) : ℂ := (P.activities.K j U:ℂ) * ∏ l∈i.val.val,measured S o P v j U l

def overlay : Bands R P where
  origins := o
  units := fun i => v i 0
  support := fun i => S.footprint (o (name V i))
  rays := fun i => R.fire (name V i)
  H := fun i => if fixed V i then Mark.probe S (o (name V i)) P (v (name V i)) else 0
  marks := fun _ j => (name (Positive R) j).val
  entries := fun i j => if fixed (Positive R) j then parcel R S o P v i (name (Positive R) j) else 0

variable {R S o P v}

omit [Fintype V] [Nonempty V] in
lemma parcel_ne {j : ℕ} {i : Positive R} (U : Config G n) (h : parcel R S o P v j i U ≠ 0) : P.activities.K j U ≠ 0 ∧
    ∀ l∈i.val.val,¬ Disjoint (S.footprint (o l)) (P.activities.forced j).inventory ∧ S.footprint (o l) ⊆ (P.activities.forced j).support := by
  refine ⟨fun he => h (by simp [parcel,he]),fun l hl => of_not_not fun hj => h ?_⟩
  unfold parcel; rw [prod_eq_zero hl (if_neg hj),mul_zero]

theorem active {A : Hol G} (h : S.Sound A) {w : ℝ} (hs : Bid.Credit S P.p.order P.p.power w)
    (hf : P.activities.ForcedFamily P.p) : (overlay R S o P v).Active := by
  have ho (i : V) : o i ∈ S.footprint (o i) := mem_image.mpr ⟨0,h.anchored,by simp⟩
  have ht {i j} {U : Config G n} (hp : (overlay R S o P v).entries i j U ≠ 0) := parcel_ne (j:=i) (U:=U) (i:=name (Positive R) j) (S:=S) (P:=P) (o:=o) (v:=v) (by
    dsimp only [overlay] at hp; split at hp
    · exact hp
    exact (hp rfl).elim)
  constructor
  · intro _; exact singleton_nonempty _
  · intro i j hj; exact (Finset.mem_singleton.mp hj).symm ▸ ho _
  · intro i; dsimp [overlay]; split
    · exact (Next.Foundations.combination_bound _ _ hs _).1
    exact ⟨fun _ _ _ => rfl,measurable_const,fun _ _ => rfl,fun _ _ => contDiffAt_const,
      fun _ _ a _ he => Next.Foundations.left_has (f:=0) a he contDiffAt_const⟩
  · intro i j; exact (name (Positive R) j).2
  · intro i j hj l hl
    obtain ⟨U,hU⟩ := not_forall.mp (mt funext hj); exact ((ht hU).2 l hl).2 (ho _)
  · intro i j U W he hw; dsimp only [overlay]; split
    · unfold parcel; rw [hf.reads i U W he hw]; congr 1
      apply Finset.prod_congr rfl; intro l hl
      unfold measured; split
      next hg => exact S.placed_local _ _ U W (agrees_mono he (coe_subset.mpr hg.2))
      rfl
    rfl
  · exact fun i j U he => hf.permit _ _ (ht he).1
  · intro i j; dsimp [overlay]; split
    · refine Measurable.mul (Complex.continuous_ofReal.measurable.comp (hf.meas i)) (Finset.measurable_fun_prod _ fun l _ => ?_)
      dsimp only [measured]; split
      · exact (S.continuous_places ..).measurable
      exact measurable_const
    exact measurable_const
  intro i j k U; dsimp only [overlay]; split
  · unfold parcel; rw [hf.sym i k U]; congr 1; refine Finset.prod_congr rfl fun l _ => ?_; unfold measured; split
    · exact S.placed_invariant h (o l) _ k U
    rfl
  rfl

theorem extra (U : Config G n) : (overlay R S o P v).extra U = linear R (diffuse S o P v U) := by
  unfold Bands.extra diffuse; rw [linear_add]; congr 1
  apply totals (α:=V)
  intro i; simp only [Bands.ray,overlay]; split
  · rfl
  rw [show masked _ _ (0:Config G n → ℂ) U=0 from ?_, Poly.send_zero]
  by_cases ht : Healthy P.p.threshold (S.footprint (o (name V i))) U
  · exact masked_eq _ _ _ _ ht
  exact masked_ne _ _ _ _ ht

theorem each (j : ℕ) (U : Config G n) : (overlay R S o P v).each j U = (P.activities.K j U:ℂ) • ∏ i : V,factor R (measured S o P v j U) i := by
  unfold Bands.each; rw [totals (α:=Positive R) (g:=fun l => Poly.send l.val (parcel R S o P v j l U)) (fun k => ?_)]; swap
  · simp only [Bands.tagged, overlay]; split <;> first | rfl | exact Poly.send_zero _
  ext y
  rw [Poly.part_smul,across,Poly.part_plus,Poly.part_sum, Poly.part_send]; simp only [Poly.part_send]
  by_cases h : y=R.quiet
  · subst y; rw [if_pos rfl]; simp only [show ∀ (i : Positive R),R.quiet ≠ i.val from
      fun i he => (i.property.ne_empty (congr_arg (fun p : R.Mode => p.val) he.symm)), ↓reduceIte,Finset.sum_const_zero,add_zero]; rw [Census.quiet]; simp
  rw [if_neg h,zero_add,Finset.sum_eq_single (⟨y, Finset.nonempty_iff_ne_empty.mpr (by intro he; exact h (Subtype.ext he))⟩ : Positive R)]
  · rw [if_pos rfl]; rfl
  · intro i _ hi; rw [if_neg]; exact fun he => hi (Subtype.ext he.symm)
  simp

theorem packet (h : Wide P) (ht : ∀ i,Mark.Tight P.p (S.footprint (o i))) (U : Config G n) (s : Finset ℕ) :
    (overlay R S o P v).packet s U = (P.activities.gasOccurrence P.p s U : ℂ) • ∏ i : V, factor R
      (fun i => Mark.unseen S (o i) P (v i) U) i := by
  unfold Bands.packet Activities.gasOccurrence; split <;> rename_i hs
  · simp_rw [Complex.ofReal_prod,each, Finset.prod_smul,Finset.prod_comm (s:=s) (t:=Finset.univ)]
    by_cases hk : (∏ i∈s,(P.activities.K i U:ℂ)) = 0
    · simp [hk]
    have hP := Finset.prod_ne_zero_iff.mp hk
    congr 1; apply Finset.prod_congr rfl; intro i _
    unfold factor monomial
    by_cases hh : Healthy P.p.threshold (S.footprint (o i)) U
    · have hz (j) (hj : j∈s) : ¬ test S o P i j := fun ht => ht.1 (Finset.disjoint_of_subset_right (fun x hx =>
        hs.2 ▸ Finset.mem_biUnion.mpr ⟨j,hj,hx⟩) hh)
      simp only [Mark.unseen,hh,if_true,Poly.send_zero,add_zero]; exact prod_eq_one fun j hj => by simp [measured,hz j hj]
    obtain ⟨j,hj,he⟩ := Mark.pack h (ht i) s hs hh fun j hj H => hP j hj (by simp [H])
    rw [prod_eq_single_of_mem j hj.1 fun k hk hne => ?_]; swap
    · simp [measured,show ¬ test S o P i k from fun H => hne (he _ ⟨hk,H⟩)]
    simp [Mark.unseen,hh,measured,(show test S o P i j from hj.2),free]
  simp

theorem density (h : Wide P) (ht : ∀ i,Mark.Tight P.p (S.footprint (o i))) {A : Hol G} (hA : S.Sound A) {δ w : ℝ}
    (hP : P.activities.Valid P.p δ w) (U : Config G n) :
    (overlay R S o P v).density U = (P.eval U:ℂ) • ∏ i : V,factor R (entire S o P v U) i := by
  have hs := Complex.ofRealCLM.summable ((Activities.gasSeries hP).summable U)
  change Summable (fun s : Finset ℕ => (P.activities.gasOccurrence P.p s U : ℂ)) at hs
  unfold Bands.density Bands.cluster
  simp_rw [packet h ht U,Summable.tsum_smul_const hs,← Complex.ofReal_tsum, extra U,passing,mul_smul_comm,← Finset.prod_mul_distrib,combine]
  simp_rw [Rep.eval,Complex.ofReal_mul,← smul_smul]; congr 2
  suffices diffuse S o P v U + (fun i => Mark.unseen S (o i) P (v i) U) = entire S o P v U by rw [this]
  funext i
  have he j : (Mark.entry S (o i) P (v i)).maskedTerm P j U=0 := by
    by_cases h : Healthy P.p.threshold ({o i}:Support n) U; exact masked_eq _ _ _ _ h; exact masked_ne _ _ _ _ h
  have ht := Mark.bulk_match S hA (o i) P (v i) U
  simp only [Source.Coefficient.exponentialEntry,he,tsum_zero,add_zero] at ht
  exact ht
end YM.WilsonStartup.Mixture
