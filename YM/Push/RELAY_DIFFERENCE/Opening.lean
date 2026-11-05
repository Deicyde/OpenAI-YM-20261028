import YM.Next.FOUNDATIONS.Split
import YM.Push.RELAY_DIFFERENCE.AttachmentBounds
import YM.Push.RELAY_DIFFERENCE.RawTop
import YM.Work.B16

/-!
# Wdff etc in the SAME labelled one-body Jma representation

Perform E initial canonical splitting, retaining mask costs using the Slots.
This is only birth, not propagation. Here is a reusable result at one chosen
top. All estimates at N in the common clock with technical orders, including
support-exponent cost explicitly. No continuity/analyticity claims through
flag borders. All pieces include gauge origins and derivative threshold price.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference.Opening
open Function Set Filter MeasureTheory Extraction Extraction.Lease Wilson RG Lattice Cells Marker Overlay Stock Bid Mix Source Labels
  Next.Foundations Attach
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {C : Family G} {N p d : ℕ} {W : Worth} {f : Extraction.Order} {F : Trial C}

section Billing
/-- The finite frame's full-group threshold cost. -/
def seats (C : Family G) (d i : ℕ) := let F := C.labels.level d; let p := C.path.levels.budget i
    ∑ j : F.Index, p.threshold⁻¹ ^ (F.grades j).2

lemma sits (C : Family G) (d i : ℕ) (x : C.label d) :
    let F := C.labels.level d
    F.coeffSize (F.scaled (C.path.levels.budget i).threshold⁻¹ x) ≤ seats C d i * F.coeffSize x := by
  let F := C.labels.level d; let B := C.path.levels.budget i
  let w (j : F.Index) : ℝ := B.threshold⁻¹ ^ (F.grades j).2
  have hp (j) : 0 ≤ w j := pow_nonneg (inv_pos.mpr B.threshold_pos).le _
  intro F
  unfold Frame.coeffSize; rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [F.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (hp a)]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ a)) (norm_nonneg _)
lemma seats_nonneg (C : Family G) (d i : ℕ) : 0 ≤ seats C d i :=
  Finset.sum_nonneg fun _ _ => pow_nonneg (inv_pos.mpr (C.path.levels.budget i).threshold_pos).le _
lemma seats_slow (K : G.Simple) : Slow C f (fun i => seats C d i.1) := by
  let F := C.labels.level d
  exact Slow.sum (C:=C) (Finset.univ (α:=F.Index)) _ fun j _ => (threshold_price K (f:=f) (C:=C)).pow (F.grades j).2

/-- Remainder bill at this top (regular mass + support-weighted
attachment with denominator discount absorbed). `D` inventory of a
whole anchor germ, includes canonical footprint. -/
def badCost (C : Family G) (d i : ℕ) (usd score b : ℝ) := b + 2*usd*(seats C d i)*score

def regCost (C : Family G) (i : ℕ) (score c : ℝ) := c + (C.path.levels.params i).columns*score

def ceilingCost (C : Family G) (d i p : ℕ) (D : Support (C.side i p)) (usd score c b : ℝ) :=
    let B := C.path.levels.budget i
    B.mass D (regCost C i score c) + B.mass D (badCost C d i usd score b) * D.card * Real.exp D.card

end Billing

section Pc
variable {n : Side}

lemma proper_gap (B : BudgetPoint) (X : Support n) (u : Config G n → ℂ) (h : B.Regular X u) :
    Slots.Proper X (u-masked B.threshold X u) B.threshold := by
  classical
  refine ⟨fun U V ha hh => ?_, fun t V => ?_, h.borel.sub (masked_measurable _ _ _ h.borel)⟩
  · have he : Healthy B.threshold X U ↔ Healthy B.threshold X V := by
      unfold Healthy
      -- use `hh` literal equality (whole flag sets not tested)
      simp only [Finset.disjoint_iff_inter_eq_empty,hh]
    have hv := h.sites U V ha
    by_cases hx:Healthy B.threshold X U
    · simp [hx,he.mp hx]
    simp only [Pi.sub_apply,masked_ne _ _ _ _ hx, hv,masked_ne _ _ _ _ (mt he.mpr hx)]
  have he : flags B.threshold (gauge t V)=flags B.threshold V := by simp
  have hp : Healthy B.threshold X (gauge t V) ↔ Healthy B.threshold X V := by simp [Healthy]
  by_cases hv:Healthy B.threshold X V
  · simp only [Pi.sub_apply,masked_eq _ _ _ _ hv,masked_eq _ _ _ _ (hp.mpr hv)]
    exact Eq.trans (sub_self _) (sub_self _).symm
  simp only [Pi.sub_apply,masked_ne _ _ _ _ hv,masked_ne _ _ _ _ (mt hp.mp hv)]; rw [h.symmetry t V]

/-- Entry with exactly one regular address (address 0). Stencil uniform
also for the unused regular addresses. -/
def kickoff {F : Labels.Frame G d} (x : F.Coeff) (D : Support n) (g : Config G n → ℂ)
    (A : ℕ → Config G n → ℂ) : Coefficient F n where
  x := x
  support _ := D
  regular i := if i=0 then g else 0
  forced := A

lemma masks {F : Labels.Frame G d} (x : F.Coeff) (D : Support n) (g : Config G n → ℂ) (A) (R : Rep G n) (U) :
    let P := kickoff x D g A
    (∑' i, P.maskedTerm R i U)=masked R.p.threshold D g U := by
  intro P
  rw [tsum_eq_single 0]
  · simp [P,Coefficient.maskedTerm,kickoff]
  intro i hi
  by_cases hx : Healthy R.p.threshold D U <;> simp [P,hx,Coefficient.maskedTerm,kickoff,hi]
end Pc

/-- Birth tool in the current trajectory only. At engineering weight d,
prepare u (physical factor included). `score` will be upper bound for
coordinates |x_N|. Concretely any `proj*c` according to `price_of_readout`.
True support-exponent and budget costs at actual stage i. Needs Slots on
D, *already on C.path*.
-/
theorem opens (h : C.Makes) (i d p : ℕ) (hh : C.ref d ≤ i) {c b usd score : ℝ} (hd : 1 ≤ usd)
    (paid : ∀ (v : C.label d) (n : Side) (o : Site n) (U), ‖(C.localSection d).places v o U‖ ≤ usd*(C.labels.level d).coeffSize v)
    (D : Support (C.side i p)) (o : Site (C.side i p)) (u : Config G (C.side i p) → ℂ)
    (slots : Slots D (C.path.rep i p i))
    (he : (C.localSection d).footprint o ⊆ D) (hc : clothed (C.path.levels.budget i) D o u c b)
    (credit : ∀ z : Label G d, Reads C.params o D z u →
        let B := C.path.levels.budget i; let F := C.labels.level d
        F.coeffSize (F.scaled B.threshold (F.coords z)) ≤ score) :
    let H := C.path.rep i p i
    let F := C.labels.level d
    ∃ P : Coefficient F (C.side i p), P.Format o C.params H ∧
      P.density o (C.localSection d) H = (fun U => (bare (C.beta i p) U : ℂ)*u U) ∧
      F.coeffSize P.x ≤ score ∧ P.remBound o H
        (Real.sqrt (C.path.levels.clock.forcedAllowance i)) (ceilingCost C d i p D usd score c b) := by
  classical
  let B := C.path.levels.budget i
  intro R F
  let X := C.localSection d
  let V := C.path.levels
  obtain ⟨hr,ht,hb,hB⟩ := hc
  obtain ⟨z,hz,-⟩ := exists_read C.params d o B (Nat.le_of_succ_le ((h.stages d).2 i hh).1) hr
  let x := F.scaled B.threshold (F.coords z)
  let A := X.footprint o
  let q := B.threshold
  have hx : F.coeffSize x ≤ score := credit z hz
  let v := F.scaled q⁻¹ x
  have hv : v=F.coords z := by
    simpa only [x, v, inv_inv] using
      F.scaled_inv (show q⁻¹≠0 from inv_ne_zero B.threshold_pos.ne') (F.coords z)
  let g := X.places v o
  let ξ := X.places (F.scaled q⁻¹ (F.core x)) o
  have hg := section_bounds C d i p h hh o x
  have hξ := section_bounds C d i p h hh o (F.core x)
  -- Residual u-g null in raw region. Wrapping allowed in this lemma (D
  -- contains the FOOTPRINT, which itself is nonwrapping).
  let y := u-g
  have hy : y 1=0 ∧ (Nonwrapping D o → C.params.PiVanish d o y) := by
    have hw := placed_reads X o (h.places _ i p hh) (h.sections _) v
    rw [show F.coords.symm v = z from hv ▸ F.coords.symm_apply_apply _] at hw
    have hj : Reads C.params o D z g := by
      unfold Reads
      split
      · rw [Reads, if_pos (nonwrapping_placement X o (h.places _ i p hh))] at hw
        exact hw
      next hq =>
        rw [Reads, if_neg hq] at hz
        unfold g
        rw [hz, hv,hz, map_smul,F.coords_unit]
        simp only [SectionData.places,X.eval_linear.map_smul, show X.evaluate F.e0=1 from (h.sections _).unit]
        simp
    apply (reads_null_iff C.params d o D _).1
    exact sub_self z ▸ reads_sub hz hj
  let a := (C.path.levels.params i).columns
  have hm : B.Regular D g := regular_larger hg.1 he
  have hs : B.Regular D y := regular_sub hr hm
  have hg' (U) : g U=x 0+ξ U := by
    have hw : x=x 0 • F.e0 + F.core x := by
      ext1 j; by_cases e:j=0
      · subst j; simp [Frame.e0,Frame.core]
      simp [Frame.e0,Frame.core,e]
    calc
      g U = X.evaluate (F.scaled q⁻¹ (x 0 • F.e0 + F.core x)) (expandAt o U) := congr_arg (fun v => X.places (F.scaled _ v) o U) hw
      _ = _ := by
        rw [map_add,map_smul,F.scaled_unit, X.eval_linear.map_add,X.eval_linear.map_smul,
          show X.evaluate F.e0=1 from (h.sections _).unit]; simp; rfl
  let bad := y - masked q D y + (ξ - masked q A ξ)
  have hw : ∀ U,Healthy q D U → bad U=0 := by
    intro U hp; unfold bad; simp only [Pi.add_apply,Pi.sub_apply,masked_eq _ _ _ _ hp,
        masked_eq _ _ _ _ (show Healthy q A U from Finset.disjoint_of_subset_left he hp),sub_self,add_zero]
  let Y := badCost C d i usd score b
  let Z := usd*seats C d i*score
  have hC : 0 ≤ usd := zero_le_one.trans hd
  have hZ (v : F.Coeff) (hv : F.coeffSize v ≤ score) U :
      ‖X.places (F.scaled q⁻¹ v) o U‖ ≤ Z := by
    refine (paid _ _ _ _).trans ((mul_le_mul_of_nonneg_left (sits C d i v) hC).trans ?_)
    rw [←mul_assoc]; exact mul_le_mul_of_nonneg_left hv (mul_nonneg hC (seats_nonneg ..))
  have h₀ : 0 ≤ Y := add_nonneg hb (mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hC) (seats_nonneg ..)) ((coeff_pos F x).trans hx))
  have hY (U) : ‖bad U‖ ≤ Y := by
    have he (X : Support _) (v : Config G (C.side i p) → ℂ) : ‖(v-masked q X v) U‖ ≤ ‖v U‖ := by
      by_cases h : Healthy q X U <;> simp [h]
    apply (norm_add_le ..).trans
    apply (add_le_add ((he _ y).trans (norm_sub_le ..)) (he _ ξ)).trans
    apply (add_le_add (add_le_add (hB U) (hZ x hx U)) (hZ (F.core x) ((core_price F x).trans hx) U)).trans_eq
    unfold Y Z badCost; ring
  let w := V.clock.forcedAllowance i
  let κ := Real.sqrt w
  have hv' : R.p=B := (h.wilson.represents i p i le_rfl).vac
  have hz : q=R.p.threshold := by rw [hv']
  have hr' := (h.wilson.represents i p i le_rfl).good.labels
  have ho : o∈D := he (Finset.mem_image.mpr ⟨0,(h.sections _).anchored,by simp⟩)
  let t := slots.out bad
  let P := kickoff x D y t
  have hc : Slots.Proper D bad R.p.threshold := by
    have hA := proper_gap B D y hs; have hD := proper_gap B A ξ hξ.1
    rw [hv']; refine ⟨?_,?_,hA.measurable.add hD.measurable⟩
    · exact fun U V ha hb => congr_arg₂ (· + ·) (hA.local_ U V ha hb) (uses_larger hD.local_ he U V ha hb)
    exact fun t U => congr_arg₂ (· + ·) (hA.gauge t U) (hD.gauge t U)
  have hj := fun l => slots.precise hc hr' o ho l
  refine ⟨P,?_,?_,hx,?_⟩
  · refine ⟨?_,fun _ => ho,?_,?_, fun l => (hj l).2.2.2.2,fun l => (hj l).2.2.2.1, fun l => (hj l).1,
      fun l => (hj l).2.1, fun l => (hj l).2.2.1⟩
    · intro l
      change R.p.Regular D _; rw [hv']
      by_cases H:l=0
      · rwa [show P.regular l=y by simp [P,kickoff,H]]
      rw [show P.regular l=0 by simp [P,kickoff,H]]; simpa using regular_smul 0 hs
    · intro l; by_cases h:l=0 <;> simp [P,kickoff,h,hy.1]
    intro l hh; by_cases H:l=0
    · rw [show P.regular l=y by simp [P,kickoff,H]]; exact hy.2 hh
    rw [show P.regular l=0 by simp [P,kickoff,H]]
    exact fun J => ⟨contDiffAt_const,fun k hk => by change iteratedDeriv k (0:ℝ→ℂ) 0 = 0; simp⟩
  · funext U
    have he : (∑' l, P.marked R l U)=(R.activities.gas R.p U : ℂ)*bad U :=
      realizes slots rfl ⟨_,ho⟩ (fun w => hw U (hz.symm ▸ w))
    have ht : (P.exponentialEntry o X R U) + bad U = u U := by
      rw [Coefficient.exponentialEntry, show (∑' l,P.maskedTerm R l U)=_ from masks ..,hv']
      change x 0 + masked q A ξ U + masked q D y U + ((y U - _) + (ξ U - _)) = u U
      rw [show y U = u U - (x 0 + ξ U) from congr_arg (u U-·) (hg' U)]; abel
    have hv : R.eval U=bare (C.beta i p) U := congr_fun (h.wilson.starts i p).2 _
    calc
      P.density o X R U = (R.eval U:ℂ)*(P.exponentialEntry o X R U + bad U) := by
        unfold Coefficient.density Rep.eval
        rw [he,Complex.ofReal_mul]; ring
      _ = _ := by rw [hv, ht]
  have hp : 0 < w := Real.exp_pos _
  have hL : w ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))
  have hκ : 0 < κ := Real.sqrt_pos.2 hp
  let M := regCost C i score c
  have hc : B.supBounds o D y M := by
    have he := bound_sub hr hm ht (bound_larger hg.2 he)
    have ht : c+a * F.coeffSize x ≤ M := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hx (zero_le_one.trans (V.params i).columns_ge)) _
    exact ⟨he.1.trans ht,fun i hi l hl hg => (he.2 i hi l hl hg).trans ht⟩
  let a := B.mass D M
  let b := B.mass D Y * D.card * Real.exp D.card
  have hp' : 0 ≤ B.mass D Y := mul_nonneg (Real.exp_pos _).le h₀
  have hu : 0 ≤ B.mass D M := mul_nonneg (Real.exp_pos _).le hc.1
  have hh : 0 ≤ b := by unfold b; positivity
  refine ⟨a,b,hu,hh,le_rfl,hκ,?_,?_⟩
  · refine ⟨fun j => if j=0 then M else 0, ?_,fun j => ?_⟩
    · have he : (fun j => R.p.mass (P.support j) (if j=0 then M else 0)) = Pi.single 0 a := by
        funext j; by_cases H:j=0; simp [H,a,BudgetPoint.mass,P,kickoff,hv']; simp [H,BudgetPoint.mass]
      rw [he]
      have hh : 0 ≤ a := hu
      exact ⟨fun j => by by_cases h:j=0 <;> simp [h,hh], (hasSum_pi_single _ _).summable, by simp⟩
    · rw [hv']; by_cases H:j=0
      · simpa [P, kickoff,H] using hc
      simpa [P,kickoff,H] using bound_smul 0 hc
  obtain ⟨K,hq,hK⟩ := slots.hitbill h₀ hY hp.le hr'.boundK
  refine ⟨K, ⟨hK.1,hK.2.1,hK.2.2.trans ?_⟩,hq⟩
  rw [hv']
  change B.mass D Y*(D.card*w)*Real.exp (D.card*w) ≤ κ*b
  have hy : D.card*w ≤ (D.card:ℝ) := mul_le_of_le_one_right (Nat.cast_nonneg _) hL
  have hz : w ≤ κ := by nlinarith only [hκ,hp,Real.sq_sqrt hp.le,hL]
  unfold b
  calc
    _ ≤ B.mass D Y * (D.card*κ) * Real.exp (D.card:ℝ) := by gcongr
    _ = _ := by ring
end YM.Push.RelayDifference.Opening
