import YM.Push.ABSOLUTE_SUMS.Copies
import YM.Push.ABSOLUTE_SUMS.Labels


/-!
#  absolute estimates in the merge after the log

Select missing clusters (original unforced-log addresses, retaining
order) and obligatory d's. The former cost their **absolute** hard-core
cluster majorants, and can occur repeatedly in the restoration
exponential. Keep the new words distinct up to the explicit multiplicity
factor! We keep even additional repeated d's and forget all old
exclusion and flag tests in this UPPER bound. Forces a positive mark to
survive wherever a d occurs.

This doesn't prove exclusion restoration algebra or specify how to
assemble and choose the labels (responsibility of the RG proof, can
consume these estimates once the physical vertex accounts are earned).
Assumes actual nonempty footprints, already including any enlargements
needed for the hit tests. Cluster conflict need only be contained in
tested overlaps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.OmitClusters
open Multiple Trees RG Lattice Finset Ursell
open scoped BigOperators Classical Topology
variable {ι κ : Type*} {n : Side} (R : ι → ι → Prop) (X : ι → Support n) (Y : κ → Support n)
    (u : ι → ℝ) (d : κ → ℝ) (M : ℕ)

abbrev Atoms (κ ι : Type*) := κ ⊕ Clusters ι

def grade : Atoms κ ι → ℝ := Sum.elim d (fun c => clusters R u c.2)

def test : Atoms κ ι → Support n := Sum.elim Y (fun c => unionOf X c.2)

def restores (s : Multiple.Reps (Atoms κ ι)) : Prop := ∃ i : κ, Sum.inl i ∈ s.1

private lemma neat (Z : ι → Support n) (M : ℕ) {b : ι → ℝ} {a γ δ : ℝ} (h : Ac.Hit Z M b a γ)
    (hd : 0 ≤ δ) : Ac.Hit Z M (fun i => δ*b i) a (δ*γ) := by
  intro x
  convert budget_scale hd (h x) using 1; ext i; split <;> ring

/-- t can be 2. A is the output support exponent; `B` in E is M.
`hfirst` prices UNFORCED ONCE. `hs` smallness includes exponential
recovery out of the seed/d costs *after* all other costs were put into
d and u. Gives weighted hit for every required copy-cut. -/
theorem restore {A γ δ q c t σ μ q' δ' η : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hd : ∀ i, 0 ≤ d i)
    (hX : ∀ i,(X i).Nonempty) (hY : ∀ i,(Y i).Nonempty)
    (ht : 1 ≤ t) (h0 : 0 ≤ σ) (hv : σ < 1) (hm : 0 ≤ μ)
    (hA : 0 ≤ A) (hδ : 0 < δ') (hr : Tests R X)
    (hfirst : Ready X M u (A+δ') γ δ q)
    (hD : Ac.Hit Y M d (A+δ') c)
    (hs : (t*Real.exp μ*(1-σ)⁻¹)*c + t*(1-σ)⁻¹*(γ*(1-q)⁻¹) ≤ η)
    (hN : 0 < η) (hP : η ≤ σ) (hg : degreePrice M η δ' ≤ q') (hq : q'<1)
    (x : Site n) (m : ℕ) :
    let T := test X Y
    SumBudget (fun r : Reps (Atoms κ ι) => if restores r ∧ m ≤ Multiple.card r then
      currency M A (r.1.biUnion T)*Multiple.connected T x (grade R u d) r else 0)
      (((t^m)⁻¹ * Real.exp (-μ))*(η*(1-q')⁻¹)) := by
  intro T; let w := grade R u d
  let e : Atoms κ ι → ℝ := Sum.elim (fun _ => μ) (fun _ => 0)
  have he i : 0 ≤ e i := by rcases i with i|i <;> first | exact hm | exact le_rfl
  have hw i : 0 ≤ w i := by
    rcases i with i|i
    · exact hd i
    · exact clusters_nonneg R hu _
  have hy i : (T i).Nonempty := by
    rcases i with i|z
    · exact hY i
    · obtain ⟨y,hy⟩ := hX (z.2 none)
      exact ⟨y,mem_biUnion.mpr ⟨none,mem_univ _,hy⟩⟩
  let b : Atoms κ ι → ℝ := fun i => (t*(w i*Real.exp (e i)))*(1-σ)⁻¹
  have ht' : 0 ≤ t := zero_le_one.trans ht
  have hσ : 0 < 1-σ := by linarith
  have hc : ∀ i, 0 ≤ b i := by intro i; unfold b; have h := hw i; positivity
  have h : Ready T M b A η δ' q' := by
    refine ⟨hN,hδ,hg,hq,hc,?_⟩
    let r : Clusters ι → Support n := fun c => unionOf X c.2
    let W : Clusters ι → ℝ := fun c => clusters R u c.2
    have hh : Ac.Hit r M W (A+δ') (γ*(1-q)⁻¹) := by
      intro x; simpa only [currency,Nat.zero_le,true_and,pow_zero,mul_one] using
        log_hit_tail R X M hr hfirst (by linarith) 0 x
    let C := t*Real.exp μ*(1-σ)⁻¹; let D := t*(1-σ)⁻¹
    have e1 := neat _ _ hD (show 0≤C by unfold C; positivity)
    have e2 := neat _ _ hh (show 0≤D by unfold D; positivity)
    have h := Labels.together _ _ _ e1 e2
    have he : b = Sum.elim (fun i=> C*d i) (fun i=> D*W i) := by
      funext i; rcases i with i|z <;>
        simp only [b,C,D,e,w,grade,W,Sum.elim_inl,Sum.elim_inr,Real.exp_zero] <;> ring
    rw [he]; intro x; exact budget_loosen (h x) hs
  refine estimates T M w e x hw hy hA ht h0 hv h hP restores ?_ m
  rintro ⟨r,p⟩ ⟨i,hi⟩
  let v : ↥r := ⟨_,hi⟩
  unfold tally; dsimp only
  apply le_trans _ (single_le_sum (f:=fun i:↥r => (p i+1:ℕ)*e i.val)
    (fun i (_:i∈univ) => mul_nonneg (by positivity) (he _)) (mem_univ v))
  change μ ≤ (p v+1:ℕ)*μ
  exact le_mul_of_one_le_left hm (by norm_cast; omega)
end YM.Push.AbsoluteSums.OmitClusters
