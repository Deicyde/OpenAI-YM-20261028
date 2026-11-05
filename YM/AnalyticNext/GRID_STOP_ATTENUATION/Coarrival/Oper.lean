import YM.AnalyticNext.GRID_STOP_ATTENUATION.Coarrival.Open
import YM.Next.EXTRACTION.Stages

set_option warningAsError false

/-!
# Locked dictionary for primary analysis, single common step operator

Need ATTENUATION & relative errors on the *ordinary* costed input
rays+germs at the vacuum. Include an augmented priced path step if
δ>0; independent of later k radius. Unit carried exactly, not
assuming arbitrary o outputs or choosing their prescriptions yet.
No assumption of payment on a comparison; DECISIVE compatibility with
our pre-existing calibrated factory's labels is made explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Coarrival
open Function Filter MeasureTheory RG Marker Wilson Lattice Source Bid Labels Multi Stock Multi.Couples Finset
open Push.GridApprox Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {m d p N : ℕ}
variable {n : Side} {o : Site n} {F : Frame G d}

def lead {F : Frame G d} (a : F.Coeff) : Wire F n := (a,0,0)
def lag {F : Frame G d} (a : Wire F n) : Wire F n := (0,a.2)

private lemma lead_lag {F : Frame G d} (a : Wire F n) : lead a.1+lag a=a := by
  ext1
  · exact add_zero _
  ext1
  · exact zero_add _
  exact zero_add _

variable {Ω : Hol G} {X : ℕ → Support n} {P : Rep G n} {κ b u : ℝ} {A B : Wire F n}
private lemma wired_add (h : (address X A).Format o Ω P) (H : (address X B).Format o Ω P)
    (he : (address X A).remBound o P κ b) (hf : (address X B).remBound o P κ u) :
    (address X (A+B)).remBound o P κ (b+u) := by
  obtain ⟨a₁,b₁,h₁,h₁',hA,hκ,⟨f,hSet,h₁F⟩,⟨g,hg,hg'⟩⟩:=he
  obtain ⟨a₂,b₂,h₂,h₂',hB,-,⟨f',hf',h₂F⟩,⟨k,hk,hk'⟩⟩:=hf 
  refine ⟨a₁+a₂,b₁+b₂,add_nonneg h₁ h₂,add_nonneg h₁' h₂',by linarith,hκ,⟨f+f',?_,fun i => Next.Foundations.bound_add
     (h.smooth i) (H.smooth i) (h₁F i) (h₂F i)⟩,g+k,?_,fun i => ⟨add_nonneg (hg' i).1 (hk' i).1,fun U => (norm_add_le ..).trans
      (add_le_add ((hg' i).2 U) ((hk' i).2 U))⟩⟩
  · simpa only [address,BudgetPoint.mass,Pi.add_apply,mul_add] using add_budget hSet hf'
  simpa only [BudgetPoint.mass,Pi.add_apply,mul_add] using add_budget hg hk





/-- Data for submitting each individual step of the descent.
`B/core` & inverse and margin currencies are the Worth receipts
made before testing. Programs even on ill-formed values can be
abstractly algebraic -- only need equivariance and physical estimates
on admissible common inputs, and of course equality with the given
factory. Postulate x and remainder prices separately for x input and
for r input: no recurrences in this contract.
-/
def tariff (C : Family G) {d N p i : ℕ} (X : ℕ→Support (C.side i p)) (z : Wire (C.labels.level d) (C.side i p)) (u : ℝ) :=
    (address X z).remBound 0 (C.path.rep N p i) (money C.path.levels i) u

def enroll (C : Family G) {d N p i : ℕ} (X : ℕ→Support (C.side i p)) (z : Wire (C.labels.level d) (C.side i p)) :=
    (address X z).Format 0 C.params (C.path.rep N p i)

structure Adjacent (C : Family G) (W : Worth) (N p d : ℕ)
    (X : (i : ℕ) → ℕ → Support (C.side i p)) (r : ℝ) (i : ℕ) where
  hr : 0 ≤ r
  travel : Wire (C.labels.level d) (C.side (i+1) p) →ₗ[ℂ] Wire (C.labels.level d) (C.side i p)
  diagonal : (C.labels.level d).Coeff ≃ₗ[ℂ] (C.labels.level d).Coeff
  worth : ∀ x : (C.labels.level d).Coeff, let V := W.K (C.path.levels.clock.J (i+1)); let F := C.labels.level d
                                        F.coeffSize (diagonal x) ≤ V * F.coeffSize x ∧ F.coeffSize (diagonal.symm x) ≤ V * F.coeffSize x ∧ F.core (diagonal x)=diagonal (F.core x)
  basis : ∀ x : (C.labels.level d).Coeff, let L := C.S.block i; let F := C.labels.level d; let y := Bid.vowel F L x
                                             let k := (travel (lead x)); let P := C.path.rep N p i
                                             (address (X i) k).Format 0 C.params P ∧ F.coeffSize (k.1 - diagonal y) ≤ barunit L * F.coeffSize (F.core x) ∧
                                             (address (X i) k).remBound 0 (Pair.funds P r hr) (money C.path.levels i) (W.K (C.path.levels.clock.J (i+1))* F.coeffSize (F.core y))
  tails : ∀ u z, z=lag z →  enroll C (N:=N) (i:=i+1) (X (i+1)) z → tariff C (N:=N) (i:=i+1) (X (i+1)) z u →
             let L := C.S.block i; let F := C.labels.level d; let k := travel z; let P := C.path.rep N p i
             (address (X i) k).Format 0 C.params P ∧ F.coeffSize k.1≤barunit L * u ∧
             (address (X i) k).remBound 0 (Pair.funds P r hr) (money C.path.levels i) (barunit L * u)
  -- need full exact denotations & output format. Even if only uses calibrated or other physical estimates: make J witness.
  conveys : ∀ z : Wire (C.labels.level d) (C.side (i+1) p),enroll C (N:=N) (i:=i+1) (X (i+1)) z → (∃ u,tariff C (N:=N) (i:=i+1) (X (i+1)) z u) →
             let P := C.path.rep N p i; let Q := C.path.rep N p (i+1); let k := address (X i) (travel z); let S := C.localSection d
             k.Format 0 C.params P ∧ k.density 0 S P = ((C.S.block i).val:ℂ)^d • (C.path.levels.clock.op i p).push Q.beta ((address (X (i+1)) z).density 0 S Q)
  -- unit pass at wire level. Follows from a canonical rule fixing units
  -- EXACTLY. separately test because remBound zero only means zero on good domains.
  constant : travel (lead (unitVec (C.labels.level d) C.path (i+1))) = lead (unitVec _ C.path i)

variable {W : Worth} {r : ℝ} {X : (i : ℕ) → ℕ → Support (C.side i p)} {i : ℕ}
namespace Adjacent
variable (J : Adjacent C W N p d X r i)

def cost (z : Wire (C.labels.level d) (C.side (i+1) p)) (a : ℝ) :=
    let F := C.labels.level d; let L := C.S.block i;W.K (C.path.levels.clock.J (i+1)) * F.coeffSize (F.core (Bid.vowel F L z.1))+barunit L*a -- J unused

include J
lemma levied (z : Wire (C.labels.level d) (C.side (i+1) p)) {a : ℝ} (he : enroll C (X (i+1)) z (N:=N) (i:=i+1)) (hf : tariff C (X (i+1)) z a (N:=N) (i:=i+1)) :
    let V := C.path.rep N p i; let k := J.travel z; let c := cost (C:=C) (i:=i) (W:=W) z a
    (address (X i) k).remBound 0 (Pair.funds V r J.hr) (money C.path.levels i) c ∧
    Bid.direction C.path W i (C.labels.level d) k.1 z.1 c a := by
  intro V k c
  have ha : 0≤a := by obtain ⟨e,u,hE,hU,h,-⟩:=hf; exact (add_nonneg hE hU).trans h
  obtain ⟨hb,hb',hB⟩ := J.basis z.1
  have hl : enroll C (X (i+1)) (lag z) (N:=N) (i:=i+1) := by obtain ⟨a,b,c,d,e,f,h,i,j⟩:=he; exact ⟨a,b,c,d,e,f,h,i,j⟩
  obtain ⟨ht,ht',hT⟩ := J.tails a (lag z) rfl hl hf
  have he (X : (v:ℕ)→ ℕ → Support (C.side v p)) (T : Wire (C.labels.level d) (C.side i p)) (h : (address (X i) T).Format 0 C.params V) :
      (address (X i) T).Format 0 C.params (Pair.funds V r J.hr) := by
    refine ⟨fun l => ?_,h.origin,h.identity_null,h.projects,h.forcing,h.carried,h.invariant,h.supported,h.borel⟩
    obtain ⟨h,t,hv,hX,hY⟩ := h.smooth l
    exact ⟨h,t,hv,hX,hY⟩
  have hx : k= J.travel (lead z.1)+J.travel (lag z) := by unfold k; rw [← map_add,lead_lag]
  have hh : (address (X i) k).remBound 0 (Pair.funds V r J.hr) (money C.path.levels i) c := by
    rw [hx]; exact wired_add (he X _ hb) (he X _ ht) hB hT
  have hc : 0≤c := by obtain ⟨y,u,hy,hv,hc',-⟩ := hh; exact (add_nonneg hy hv).trans hc'
  let L := C.S.block i; let y := Bid.vowel (C.labels.level d) L z.1
  refine ⟨hh,hc,ha,J.diagonal,J.worth,le_trans ?_ ((add_le_add hb' ht').trans_eq (mul_add ..).symm),le_rfl⟩
  rw [hx]; let K := C.labels.level d
  change K.coeffSize ((J.travel (lead z.1)).1 + (J.travel (lag z)).1 - J.diagonal _) ≤ _
  rw [add_sub_right_comm]; unfold Frame.coeffSize; rw [←sum_add_distrib]; exact Finset.sum_le_sum (fun j _ => norm_add_le ..)
end Adjacent
end YM.AnalyticNext.GridStop.Coarrival
