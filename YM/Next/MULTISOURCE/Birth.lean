import YM.Bid.Fuels
import YM.Next.MULTISOURCE.Loading
import YM.Next.MULTISOURCE.Merger


/-!
# Simultaneous *physical* initialization

One standard shape (literal cylinders, with reference linear coordinates at the
origin via the same readout, in application). Split every cylinder into unit,
masked principal and its complement. Marked variation representation
on that exact vacuum (aggregate form), all powers simultaneously. No
assumption that singleton already carried a forced representative in these
names. Propagation gate later needs to respect the corresponding singles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi

open RG Wilson Lattice Function Finset Marker Filter MeasureTheory Couples
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side}

structure Vessel (G : Gauge) (n : Side) where
  siteSet : Support n
  tall : ℂ
  seen : Config G n → ℂ

namespace Vessel
variable (C : Vessel G n) (P : Rep G n)
def full (U : Config G n) := C.tall+C.seen U
def cheek (U : Config G n) := C.tall+masked P.p.threshold C.siteSet C.seen U
def tail (U : Config G n) := C.full U-C.cheek P U
def birth : Pulse G n := ⟨C.cheek P, ballast C.siteSet P (C.tail P)⟩

structure Check (o : Site n) (m : ℕ) (r c : ℝ) : Prop where
  centered : o ∈ C.siteSet
  few : C.siteSet.card ≤ m
  paid : ‖C.tall‖ ≤ c
  pus : Banked P.p 2 {o} (masked P.p.threshold C.siteSet C.seen) c
  rate : 0 ≤ r ∧ ∀ U, ‖C.tail P U‖ ≤ r
  weight : Weight P.p C.siteSet (C.tail P)
  loan : liftFee m * (burn P.p 2 C.siteSet * r) ≤ c

lemma tail_weight (hh : LocalOn C.siteSet C.seen) (he : Measurable C.seen) (hf : GaugeInvariant C.seen) :
    Weight P.p C.siteSet (C.tail P) := by
  unfold tail cheek full
  constructor
  · exact (measurable_const.add he).sub
      (measurable_const.add (masked_measurable _ _ _ he))
  · intro t U; simp only [hf t U]; simp [masked, Set.indicator, Healthy,hf t U]
  · intro U V h hg
    dsimp only
    rw [hh U V h]
    have hv : Healthy P.p.threshold C.siteSet U ↔ Healthy P.p.threshold C.siteSet V := by
      unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,hg, Finset.disjoint_iff_inter_eq_empty]
    by_cases e : Healthy P.p.threshold C.siteSet V
    · rw [masked_eq _ _ _ _ (hv.mpr e), hh U V h,masked_eq _ _ _ _ e]
    rw [masked_ne _ _ _ _ (mt hv.mp e), masked_ne _ _ _ _ e]
  intro U hu
  by_cases e : Healthy P.p.threshold C.siteSet U
  · exact False.elim (hu (by rw [masked_eq _ _ _ _ e]; ring))
  exact Finset.not_disjoint_iff.mp e
end Vessel

variable {V : Type} [Fintype V] [DecidableEq V] (P : Rep G n)

def prepare (R : Census V) (C : V → Vessel G n) (i : Hot R) : Pulse G n :=
    (soloTable (fun j => (C j).cheek P) i, payload (fun j => (C j).siteSet) P (fun j => (C j).tail P) i.sites)

lemma first_prepare (C : V → Vessel G n) {δ κ : ℝ} (h : P.activities.Valid P.p δ κ)
    (hf : ∀ i, Weight P.p (C i).siteSet ((C i).tail P)) (R : Census V) (s : R.Mode) (U : Config G n) :
    (many P R (prepare P R C) U).part s = (P.eval U:ℂ) * ∏ i∈s.val,(C i).full U := by
  let f i := (C i).siteSet
  let g (i : V) := (C i).tail P
  let F := track (R:=R) P g U
  let D := flags P.p.threshold U
  have he : (∑ x∈ Pack.clears D, ∏ y∈x,(Poly.send R.quiet (incumbent P U y) +
      lit R (fun i => (prepare P R C i).2 y U))) =
      Poly.bead R (P.activities.gas P.p U) * ∏ i, (1+Poly.send (R.fire i) (g i U)) := by
    simp_rw [prepare, ← till_eq _ _ _ _ _ _ h]; rw [real_book _ _ h]
    have hk i (hi : F (.inr i)≠0) : ∃ v∈f i,v∈ D := by
      apply (hf i).needs; intro e; exact hi (by change Poly.send _ (g i U)=0; rw [show g i U=0 from e, Poly.send_zero])
    simp only [map_prod,map_sum]
    exact together f F D hk
  have hg : many P R (prepare P R C) U=(P.eval U:ℂ) • ∏ i : V, (1+Poly.send (R.fire i) ((C i).full U)) := by
    unfold many composeAt
    rw [show Pack.clears _ = Pack.clears D from rfl, he,
      mul_left_comm _ (Poly.bead R _),Poly.product_bead]
    simp only [prepare, solo_sum]
    change (↑(Real.exp (P.exponent U)):ℂ) • ((↑(P.activities.gas P.p U):ℂ) •
      ((Poly.pass (lambda R (fun i => (C i).cheek P U)))*_)) = _
    rw [smul_smul, ← Complex.ofReal_mul, ← Rep.eval]
    refine congrArg (fun x => (P.eval U:ℂ) • x) ?_
    rw [show Poly.pass (lambda R (fun i => (C i).cheek P U)) = ∏ i : V,(1+Poly.send (R.fire i) ((C i).cheek P U)) from
      pass_sum_send (Finset.univ) (Hot.one R) _, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [show (C i).full U = (C i).cheek P U+g i U from (by unfold g Vessel.tail; ring),send_add,
      add_mul,one_mul,mul_add, send_noProd (x:=R.fire i) (y:=R.fire i) (by
        rintro ⟨t,ht⟩; exact Finset.disjoint_left.mp ht.1 (mem_singleton_self i) (mem_singleton_self i)),
      mul_one,add_zero]
    ring
  rw [hg, Poly.part_smul, polynomial]

lemma birth_copy (C : V → Vessel G n) (R : Census V) (i : V) : prepare P R C (Hot.one R i)=(C i).birth P := by
  apply Prod.ext
  · unfold prepare; dsimp only; rw [soloTable_one]; rfl
  funext j u; change payload _ _ _ _ _ _=_; rw [Hot.sites_one,single_payload]; rfl

-- price for startup
set_option maxHeartbeats 450000 in
lemma seed_credit (C : V → Vessel G n) (R : Census V) (o : V → Site n) {κ : ℝ} {p b : V → ℝ} (T : Hot R) {m : ℕ}
    (h : ∀ i,(C i).Check P (o i) m (b i) (p i)) {δ v : ℝ} (H : P.activities.Valid P.p δ v)
    (hK : 0 < κ) (hk : κ ≤ 1) (hp : Mint P 2 κ) :
    Credit P.p 2 κ (T.sites.image o) (prepare P R C T) (∏ i∈T.sites,p i) := by
  let f i := (C i).siteSet
  let g i := (C i).tail P
  have hs : 0 ≤ ∏ i∈ T.sites,p i := prod_nonneg fun i _ => (norm_nonneg _).trans (h i).paid
  obtain ⟨a,ha,he⟩ := merge_bound P f T.sites T.property (by norm_num) hK.le hk hp m (fun i => (h i).few)
    g b (fun i => (h i).rate.1) (fun i => (h i).rate.2)
  unfold prepare
  refine ⟨T.property.image o,by norm_num,hK,hs,?_,a,?_,?_⟩
  · dsimp only
    by_cases HH : 2 ≤ T.sites.card
    · rw [soloTable_not _ _ HH]
      exact ⟨0,0,funext fun x => by simp,fun _ => rfl,(norm_zero).le.trans hs,(Banked.zero ..).enlarge hs⟩
    have h1 : 0<T.sites.card := Finset.card_pos.mpr T.property
    obtain ⟨i,hI⟩ := Hot.one_of_card (x:=T) (by omega)
    -- not use equality `birth_copy`, cost uses entry in preparation here
    subst T
    rw [soloTable_one,Hot.sites_one, image_singleton,prod_singleton]
    exact ⟨(C i).tall,_,rfl,fun H => by simp at H,(h i).paid,(h i).pus⟩
  · apply ha.trans; apply mul_le_mul_of_nonneg_left _ hK.le
    exact prod_le_prod (fun i _ => mul_nonneg (lift_pos _).le (mul_nonneg (burn_pos ..).le (h i).rate.1))
      fun i _ => (h i).loan
  intro i; exact ⟨pay_legible P f g T.sites i H.forced (fun i => (h i).weight), zone_of_payload P f g T.sites o
    (fun i => (h i).centered) i,he i⟩

end YM.Multi
