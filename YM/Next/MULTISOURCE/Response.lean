import YM.Bid.Fuels
import YM.Next.MULTISOURCE.First
import YM.Next.MULTISOURCE.Measure
import YM.Next.MULTISOURCE.Shards


/-!
# From response estimates *at vacuum*, one step only

The missing analytic susceptibility estimate at RG producer is of type
`Raw at every q` on one step. It involves no multipoint path. Price of a
single **linear** activity variation realizing a given function (component
left after removing products of proper subresponses, at a *fixed* coarse
field, no division by vacuum density). Function requested for one set of root
directions at a time. Varying only the unnormalized vacuum, squarefree
coefficient, fixed histories. Must supply same responses to proper subsets for
use in this formula. No price limit on the jointly summed array of all subsets
is assumed! This is the local analytic/jet estimate the block integration will
have to be able to supply (cf. JM step in E); not asserting its truth. It's
reasonable to try it not on an arbitrary vacuum, but in continuation of the
specific representations at RAdvances/RPaper. Factor `b` may cost
post-block polynomial(s); we prove what recovery is needed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Lattice Marker Function MeasureTheory Filter Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {G : Gauge}

/- The price request uses exactly known lower responses. -/
section
variable {c f : Side} (S : StepData c f) (P : Rep G c) (Q : Rep G f) (Z : Hot (parts R) → Pulse G c)
    (D : Hot R → Pulse G f)

def ProperSum (Z : Hot R → Pulse G c) (q : Hot R) (U : Config G c) :=
    ∑ A∈(shards R q.val).erase ((parts R).fire q), jet P (parts R) Z A U

def defect (q : Hot (parts R)) (U : Config G c) :=
    S.push Q.beta (jet Q (parts R) D q.val) U - ProperSum P Z q U

/-- Primitive local estimate, pointwise in root-set; no sum over root positions
or directions, no rescaling. `Credit` pays the true derivative order and needs
some exponent reserve *on output*. Application in this file assumes nothing here
for union-cardinality one. -/
def Raw (b κ : ℝ) (k : Hot R → ℝ) (o : V → Site c) (q : Hot (parts R)) :=
    tangent P (Z q) = defect S P Q Z D q ∧ Credit P.p 2 κ
      ((unionOfHot q).sites.image o) (Z q) (b^(unionOfHot q).sites.card * ∏ t∈q.sites, k t)

omit [Fintype V] in
/-- Proper means proper: `ProperSum` never needs the response for `q`. -/
lemma proper_inputs (Z Z' : Hot R → Pulse G c) (q : Hot R)
    (H : ∀ i : Hot R, i.sites ⊂ q.sites → Z i=Z' i) :
    ProperSum P Z q=ProperSum P Z' q := by
  funext U; apply sum_congr rfl; intro i hi
  refine congr_fun (jet_inputs _ _ _ i fun t ht => H t ?_) U
  obtain ⟨hn,hq⟩ := mem_erase.mp hi
  have he : i.val.biUnion Hot.sites=q.sites := congrArg Subtype.val ((chooses ..).mp hq)
  refine Finset.ssubset_iff_subset_ne.mpr ⟨he ▸ Finset.subset_biUnion_of_mem Hot.sites ht,?_⟩
  intro hv; apply hn
  obtain rfl := Hot.eq_of_sites hv
  refine Subtype.ext (Finset.eq_singleton_iff_unique_mem.mpr ⟨ht,?_⟩)
  intro p hp; by_contra hh
  obtain ⟨y,hy⟩ := p.property
  have h' : y∈ t.sites := he ▸ Finset.mem_biUnion.mpr ⟨p,hp,hy⟩
  exact Finset.disjoint_left.mp (parts_wise i hp ht hh) hy h'

lemma jet_account (Z : Hot R → Pulse G c) {δ rho : ℝ} (h : P.activities.Valid P.p δ rho) (q : Hot R) (U : Config G c) :
    (many P R Z U).part q.val = tangent P (Z q) U + ProperSum P Z q U := by
  unfold ProperSum; rw [allJets]; conv_rhs => lhs; rw [← first_jet P h Z (parts R)]
  exact (add_sum_erase _ _ ((chooses ..).mpr (unionOf_single _))).symm

lemma account_lives (r : R.Mode) (L : (Hot R → ℝ)) (t X : ℝ) (u : Hot R → Support f)
    {δ σ C Λ μ rho v : ℝ} (h : P.activities.Valid P.p δ rho) (hh : Q.Lawful σ C Λ μ v)
    (he : ∀ i, Credit Q.p t X (u i) (D i) (L i)) (hb : S.IsKernel Q.beta G)
    (hv : P.eval=S.push Q.beta Q.eval) (J : ∀ i : V,tangent P (Z (Hot.one _ (Hot.one R i))) =
      S.push Q.beta (tangent Q (D (Hot.one R i))))
    (hr : ∀ i : Hot (parts R), 2 ≤ (unionOfHot i).sites.card → tangent P (Z i) = defect S P Q Z D i) :
    (fun U => (many P R (foldRows Z) U).part r) = S.push Q.beta (fun x => (many Q R D x).part r) := by
  have hV (j : (parts R).Mode) (U : Config G c) :
      (many P (parts R) Z U).part j = S.push Q.beta (jet Q (parts R) D j) U := by
    by_cases e : j.val.Nonempty
    · let k : Hot (parts R) := ⟨j,e⟩
      change (many P (parts R) Z U).part k.val=_
      by_cases ht : 2 ≤ (unionOfHot k).sites.card
      · rw [jet_account P Z h k, hr k ht]; unfold defect; ring
      obtain ⟨x,hx⟩ := Hot.one_of_card (x:= unionOfHot k) (by have hp : 0 < (unionOfHot k).sites.card := Finset.card_pos.mpr (unionOfHot k).property; omega)
      have hy : Hot.one (parts R) (Hot.one R x)=k := by
        have hm : k∈blocksOf R (Hot.one R x) := (hu_chooses ..).mpr hx.symm
        rw [singleton_blocks] at hm; exact (mem_singleton.mp hm).symm
      have hg : j=(parts R).fire (Hot.one R x) := congrArg Subtype.val hy.symm
      rw [← hy,hg,first_jet _ hh.labels]
      exact (firstMany _ h Z (Hot.one R x) U).trans (congrFun (J x) U)
    rw [show j=(parts R).quiet from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp e)]
    have hw : ∀ x : Config G f, jet Q (parts R) D (parts R).quiet x=(Q.eval x:ℂ) :=
      fun U ↦ floor_part Q U hh.labels _ _ (lambda_quiet _) fun _ => lambda_quiet _
    have hx : (many P (parts R) Z U).part (parts R).quiet=(P.eval U:ℂ) :=
      floor_part _ _ h _ _ (part_lit_quiet _) fun _ => part_lit_quiet _
    rw [hx,hv, funext hw]
    unfold StepData.push; rw [← integral_complex_ofReal]
    simp [Complex.real_smul]
  funext U
  rw [← fold_many P Z U,substituted]
  simp_rw [hV,allJets]
  unfold StepData.push
  have he' (i) := StepData.push_slice hb U (jet Q (parts R) D i) (evaluate_int Q hh D he i)
  simp_rw [Finset.smul_sum]
  exact (integral_finsetSum (shards R r) (fun i _ => he' i)).symm
end

end YM.Multi
