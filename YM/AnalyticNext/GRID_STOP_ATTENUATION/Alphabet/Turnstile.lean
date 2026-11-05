import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Sequence
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Gate


set_option warningAsError false

/-!
# Commercial use: signed prescription over actual marked queries at a step

Can even get a different choice of first coarse pulse from the one needed
for continuing the Physical paid comparison, but with strong enough
support rents, structure of error such as the null letters exhibited
here, and reserves in that solution's OTHER coefficients. Then it
suffices to fund Applications at the higher price. No promises that the
physical provenance actually can use this weakening (depends on doing
PSREC and stability together, corrected common-support entries, ...); NOT
asserting every tangent-kernel discrepancy is repairable at these costs or
that the direction/cap already pays these additional epigraphs. In sharp
contrast to `Alphabet.inadequate` at uniform base asks. Compare  and
19038. All observables, support covers, order, weighting and periods same
through this rewrite.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Alphabet
open RG Marker Wilson Lattice Multi Stepwise Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
variable {G : Gauge} {n : Side} (P : Rep G n)

-- Enrollment on `Z` alphabet of primitive responses. Include the
-- identification of real positions even when variables are *Hot* groups.
omit [Fintype V] in
def tents (o : V → Site n) (i : Hot R) := i.sites.image o
omit [Fintype V] in
lemma spots (o : V → Site n) (x : Hot (parts R)) : covers (tents o) x=(unionOfHot x).sites.image o := by
  unfold covers tents; rw [show (unionOfHot x).sites=x.sites.biUnion Hot.sites from rfl]; rw [Finset.biUnion_image]
omit [Fintype V] in
lemma ticket (r : ℝ) (x : Hot (parts R)) : Poly.toll (fun v : Hot R => r^v.sites.card) x.val = r^(unionOfHot x).sites.card := by
  unfold Poly.toll
  rw [show (unionOfHot x).sites=x.sites.biUnion Hot.sites from rfl]
  rw [card_biUnion (parts_wise x.val), ←prod_pow_eq_pow_sum] 

omit [Fintype V] in
private lemma partition (x : Hot (parts R)) : 2≤(unionOfHot x).sites.card ∨ ∃ i : V,x=Multi.Step.polyse R i := by
  by_cases he : 2≤(unionOfHot x).sites.card
  · exact Or.inl he
  right
  have hp : (unionOfHot x).sites.card=1 := by
    have : 0 < (unionOfHot x).sites.card := Finset.card_pos.mpr ((show Finset.Nonempty _ from (unionOfHot x).property))
    omega
  obtain ⟨i,hi⟩ := Hot.one_of_card hp
  refine ⟨i,?_⟩
  have h : x ∈ blocksOf R (Hot.one R i) := (hu_chooses ..).mpr hi.symm
  rw [singleton_blocks] at h; exact mem_singleton.mp h

variable {C : Family G} {i N p : ℕ} (H : C.Makes) (he : i≤N) {b w κ' : ℝ} {D : Foci R G (C.side (i+1) p)}
variable {o : V→Site (C.side i p)} {M : V→Pulse G (C.side i p)}
include H he

omit [Fintype V] in
/-- One step benefit at normalized perturbations. Inputs M = some
prescription known to be achievable; output M' committed at given cost,
possibly another choice of Pack. No horizon. Doesn't handle general
changes in presentation or detached regular deposits. -/
-- at b0, ask for high reserve on singles as well. Mint at reserve 2 includes all
-- incumbent expenses. Can license multiple expansions at each response (including
-- winding) with capacity given before scheduling by each tag.
theorem transplant (b0 : ℝ) (hb0 : 0<b0) (hT : UnitTest R C i N p o D M b0)
    (hM : ∀ i₀, Multi.Credit (C.path.rep N p i).p 2 (money C.path.levels i) {o i₀} (M i₀) b0)
    (hQ : Mint (C.path.rep N p i) 2 κ')
    (L : List (Attempt G (C.side i p) (Hot R))) (hL : ∀ t∈L,t.eligible (C.path.rep N p i) (tents o) 2 (money C.path.levels i) κ')
    (_h : b0≤b) (hh : ∀ x : Hot R, b0^x.sites.card+debt L x ≤ b^x.sites.card)
    {M' : V→Pulse G (C.side i p)} (hH : ∀ x,M' x=M x+acts (C.path.rep N p i) L (Hot.one R x)) :
    UnitTest R C i N p o D M' b := by
  let S := C.path.levels.clock.op i p
  let P := C.path.rep N p i; let Q := C.path.rep N p (i+1); let δ := money C.path.levels i
  obtain ⟨Z,HZ,hZ⟩ := hT
  let f := tents (R:=R) o
  let k (b : ℝ) (x : Hot R) := b^x.sites.card
  have hg (x : Hot (parts R)) : Multi.Credit P.p 2 δ (covers f x) (Z x) (Poly.toll (k b0) x.val) := by
    rw [ticket,spots]
    rcases partition x with hx|⟨x,rfl⟩
    · simpa using (hZ _ hx).2
    rw [HZ,Multi.Step.polyse,unionOfHot_one,Hot.sites_one,Finset.card_singleton,image_singleton]; simp only [pow_one]; exact hM _
  have hF := (H.wilson.represents N p i he).good
  let T := changed P L Z
  refine ⟨T,fun x => (changed_one P L Z _).trans (by rw [HZ x,hH]),fun q hq => ⟨?_,?_⟩⟩
  · funext W
    have hz := congrArg (fun p : Config G (C.side i p) → Poly (parts R) => (p W).part q.val) (changed_many P L Z)
    change (many P (parts R) T W).part q.val=(many P (parts R) Z W).part q.val at hz
    have hx : tangent P (Z q)= defect S P Q Z D q := (hZ q hq).1
    rw [jet_account P T hF.labels q,jet_account P Z hF.labels q,hx] at hz
    unfold defect at hz ⊢; rw [sub_add_cancel] at hz; exact eq_sub_of_add_eq hz
  let K := k b0+debt L
  have hp := changed_credit P f L Z (fun x => x.property.image o) hF hQ hL (k b0)
    (fun i => pow_pos hb0 _) hg q
  rw [spots] at hp
  apply hp.expand
  have hK x : 0≤debt L x := List.sum_nonneg (fun i hi => by
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hi; exact Attempt.nonneg _ _ t (hL _ ht) x)
  refine (le_trans (b:=Poly.toll (k b) q.val) (Finset.prod_le_prod (fun i _ => add_nonneg (pow_nonneg hb0.le _) (hK i))
    (fun i _ => hh i)) ?_)
  rw [ticket]; simp only [prod_const_one,mul_one,le_refl]

end YM.AnalyticNext.GridStop.Alphabet
