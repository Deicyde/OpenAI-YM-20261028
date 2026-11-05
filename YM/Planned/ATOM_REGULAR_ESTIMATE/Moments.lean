import YM.Next.EXTRACTION.Tails
import YM.Planned.ATOM_REGULAR_ESTIMATE.Grades
import YM.Planned.ATOM_REGULAR_ESTIMATE.Infinitesimal



/-! Cancel flat moments from the actual mask-agnostic, oriented
holonomy readout. This is an input jet theorem; no assumption about covariance
of performing a model block transformation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Flat
open Function Tensor Filter Lattice Wilson RG Source Labels Source.Drops Gauge Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {d k m : ℕ} {H : Hol G} {f : Config G n → ℂ}

section

set_option maxHeartbeats 600000 in
private lemma kill (o : Site n) (hf : ContDiffAt ℝ d (f ∘ increment 1) 0)
    (hh : H.PiVanish d o f) (hg : GaugeInvariant f) (p : Fin m → Perturb G d) (a : Fin m → ℕ)
    (ha : ∀ i, 0 < a i) (he : ∑ i, a i ≤ d) (hw : ∀ i, Phase (a i) (p i)) :
    iteratedFDeriv ℝ m ((f ∘ increment 1) ∘ surface H o) 0 p = 0 := by
  let F i := f (H.testLinks d o (expand d i) 1)
  let g := (f ∘ increment (1 : Config G n)) ∘ surface (d:=d) H o
  have hdim : m≤d := (arity a ha).trans he
  let L : Perturb G d →L[ℝ] Snap G d := ContinuousLinearMap.fst ℝ _ _
  have ht : g =ᶠ[𝓝 0] F ∘ L := by
    filter_upwards [truly H o (d:=d)] with v hv; change f ((increment 1 ∘ surface H o) v)=F (L v); rw [← hv]; exact hg ..
  have hS : ContDiffAt ℝ d F 0 := by
    let I : Snap G d →L[ℝ] Perturb G d := ContinuousLinearMap.inl ..
    have hz := surface_zero (d:=d) H o
    have hd : ContDiffAt ℝ d g 0 := (show ContDiffAt ℝ d (f ∘ increment 1) (surface H o (0:Perturb G d)) by rw [hz]; exact hf).comp (f:=surface H o) _ ((surface_diff H o).of_le le_top)
    have he : ContDiffAt ℝ d (F ∘ (⇑L)) (I 0) := by rw [map_zero]; exact hd.congr_of_eventuallyEq ht.symm
    exact he.comp (f:=I) 0 I.contDiff.contDiffAt
  have hp (v : Snap G d) (k : ℕ) (hk : k ≤ d) : iteratedDeriv k (F ∘ whorl v) 0 = 0 := by
    rw [show F ∘ whorl v = fun t => f (H.testLinks d o (expand d v) t) from funext fun t => by
      unfold Function.comp F
      nth_rw 2 [test_scaled]; rfl]
    exact (hh _).2 k hk
  change iteratedFDeriv ℝ m g 0 p = 0
  have ht' : iteratedFDeriv ℝ m g (0:Perturb G d)=iteratedFDeriv ℝ m (F ∘ (⇑L)) 0 := (ht.iteratedFDeriv (𝕜:=ℝ) m).eq_of_nhds
  have hu := snap_null hS hp (fun i => (p i).1) a he (fun i => (hw i).low)
  have hd : iteratedFDeriv ℝ m (F ∘ (⇑L)) 0 = _ := jets_linear L (k:=m) (hS.of_le (Nat.cast_le.mpr hdim))
  exact (congr_arg (fun T : Tensor.T (Perturb G d) ℂ m => T p) (ht'.trans hd)).trans hu

private lemma atomic {k : ℕ} (q : OrderedFinpartition k) (h : q.length=k) : q=OrderedFinpartition.atomic k := by
  rcases q with ⟨l,p,hp,e,hM,hP,hD,hC⟩
  change l=k at h; subst l
  have hs := OrderedFinpartition.sum_sigma_eq_sum ⟨k,p,hp,e,hM,hP,hD,hC⟩ (fun _ => (1:ℕ))
  change ∑ i : Fin k, (∑ _j : Fin (p i), (1:ℕ)) = _ at hs
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hs
  have hv : p = fun _ => 1 := by
    funext i
    by_contra hi
    have ht := Finset.sum_lt_sum (f:=fun _ => 1) (g:=p) (fun j _ => hp j)
      ⟨i,Finset.mem_univ _,lt_of_le_of_ne (hp i) (Ne.symm hi)⟩
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,hs,lt_self_iff_false] at ht
  subst p
  let t i := e i 0
  have hx : StrictMono t := hP
  let U : (Fin k) ≃o (Fin k) := StrictMono.orderIsoOfSurjective t hx (Finite.injective_iff_surjective.mp hx.injective)
  have ha : U=OrderIso.refl _ := Subsingleton.elim ..
  have he : e=fun i _ => i := funext fun i => funext fun j => by
    rw [Subsingleton.elim j 0]
    exact congr_arg (fun Z : Fin k ≃o Fin k => Z i) ha
  subst e; rfl

/-- Replacement inside an arbitrary polar jet: only the actual internal
edges matter, no periodic extension at hidden endpoints. -/
lemma replaces (X : Support n) (h : LocalOn X f) (hk : ContDiffAt ℝ k (f ∘ increment 1) 0)
    (v w : Fin k → Directions G n) (hv : ∀ i, Agrees X (v i) (w i)) :
    iteratedFDeriv ℝ k (f ∘ increment 1) 0 v = iteratedFDeriv ℝ k (f ∘ increment 1) 0 w := by
  let G' := f ∘ increment (1:Config G n)
  let L : Directions G n →L[ℝ] Directions G n := ContinuousLinearMap.pi fun e =>
    if e.1∈X ∧ e.1+step e.2∈X then ContinuousLinearMap.proj e else 0
  have hb e (u : Directions G n) (hx : e.1∈ X) (hy : e.1+step e.2∈X) : L u e = u e := by simp [L,hx,hy]
  have he : G' = G' ∘ L := by
    funext x; apply h; intro i hx hy; rw [increment,increment,hb i x hx hy]
  have hh (i) : L (v i) = L (w i) := by
    funext j
    by_cases hx : j.1∈X ∧ j.1+step j.2∈X
    · rw [hb _ _ hx.1 hx.2,hb _ _ hx.1 hx.2]; exact hv i j hx.1 hx.2
    simp [L,hx]
  change iteratedFDeriv ℝ k G' 0 v = iteratedFDeriv ℝ k G' 0 w
  rw [he, jets_linear L (f:=G') hk,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, funext hh]

/-- B70 PMOM for anchored input regular on actual trajectory geometry.
Includes order zero. -/
theorem moments (o : Site n) (X : Support n) (hp : Nonwrapping X o) (hn : 2 ≤ n.val)
    (hf : ContDiffAt ℝ d (f ∘ increment 1) 0) (hh : H.PiVanish d o f) (hg : GaugeInvariant f)
    (hl : LocalOn X f) (u : Fin k → Directions G n) (a : Fin k → ℕ) (h₁ : ∀ i, 0<a i)
    (h₂ : ∑ i, a i ≤ d) (hu : ∀ i, FitsGrade o X (a i - 1) (u i)) :
    iteratedFDeriv ℝ k (f ∘ increment 1) 0 u = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have he i : a i ≤ d := (Finset.single_le_sum (f:=a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h₂
    have hx i : (a i-1)<d := (Nat.sub_lt (h₁ i) one_pos).trans_le (he i)
    choose w hW e using fun i => interpolate H o X hp hn (u i) (hu i) (hx i)
    have hW' i : Phase (a i) (w i) := (Nat.sub_add_cancel (h₁ i)) ▸ hW i
    have hk := (arity a h₁).trans h₂
    let q := surface (d:=d) H o; let g := f ∘ increment (1 : Config G n)
    have h := kill o hf hh hg w a h₁ h₂ hW'
    have hd : ContDiffAt ℝ d q 0 := (surface_diff H o).of_le le_top
    have hv : q 0=0 := surface_zero ..
    change iteratedFDeriv ℝ k (g ∘ q) 0 w=0 at h
    rw [iteratedFDeriv_comp (show ContDiffAt ℝ d g (q 0) from hv.symm ▸ hf) hd (Nat.cast_le.mpr hk),
      FormalMultilinearSeries.taylorComp,hv,sum_apply,Finset.sum_eq_single (OrderedFinpartition.atomic k)] at h
    · change iteratedFDeriv ℝ k g 0 (fun i => iteratedFDeriv ℝ 1 q 0 (fun _ => w i))=0 at h
      simp_rw [iteratedFDeriv_one_apply] at h
      rw [replaces X hl (hf.of_le (Nat.cast_le.mpr hk)) u (fun i => tangent H o (w i)) e]; exact h
    · intro p _ hc
      have hw : p.length < k := lt_of_le_of_ne p.length_le (mt (atomic p) hc)
      let A (i : Fin p.length) := ∑ j, a (p.emb i j)
      refine ih _ hw (fun i => iteratedFDeriv ℝ (p.partSize i) q 0 (fun j => w (p.emb i j))) A (fun i => ?_) ?_ (fun i => ?_)
      · exact (p.partSize_pos i).trans_le (arity _ fun j => h₁ (p.emb i j))
      · unfold A; rw [p.sum_sigma_eq_sum]; exact h₂
      exact ((show FitsGrade o X ((∑ j,a (p.emb i j))-1) _ from degree_surface H o X hp hn (fun j => w (p.emb i j)) _ (fun j => h₁ (p.emb i j)) (fun j => hW' (p.emb i j))))
    simp
end
end YM.Planned.AtomRegular.Flat
