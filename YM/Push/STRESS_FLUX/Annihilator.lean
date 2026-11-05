import YM.Next.FOUNDATIONS.SU2
import YM.Push.STRESS_FLUX.Matching

/-! Propagate all the annular kernel comparisons without ever extracting new
hierarchies, even though matched labels can vary with mesh/period and node.
Finite-dimensionality only at the reference coordinates D. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Matching
open Function Set Filter MeasureTheory Extraction Lattice
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {L : Register G} {C : Family G} {S : Table C.book} {k D d h : ℕ} {f : Extraction.Order}
  {ι : Type*} [Fintype ι]

def pairRead (S : Table L) (v : L.Ref 4) (B : L.Ref d) (s : Audience L) (y : E4) := S.read (Points.cons y s.x) (Fin.cons ⟨4,v⟩ (Fin.cons ⟨d,B⟩ s.tags))

def Snip (S : Table L) (v : Axis → Axis → L.Ref 4) (B : L.Ref d) (D h : ℕ) :=
  ∀ j : ℕ, ∀ s : Fin j → Audience L, ∀ c : Fin j → ℂ, (∀ u, ∑ i, c i * S.injectFront (s i).tags (s i).x D u = 0) →
    ∃ e ε : ℕ → ℝ, (∀ k, 0<e k ∧ 0 ≤ ε k) ∧ Tendsto e atTop (𝓝 0) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, ∀ z : E4, 1/4 ≤ ‖z‖ → ‖z‖ ≤ 1 → (∀ i, Points.cons (e k • z) (s i).x ∈ generic _) → ∀ a b,
        ‖∑ i, c i * ((e k :ℂ)^h * pairRead S (v a b) B (s i) (e k • z))‖ ≤ ε k

lemma response (hp : f.PointLimits C S) (v : C.label 4) (B : C.label d) (s : ι → Audience C.book) (c : ι → ℂ)
    (hc : ∀ u, ∑ i, c i * S.injectFront (s i).tags (s i).x D u = 0) (r : ℝ) (y : E4) (hy : ∀ i, Points.cons y (s i).x ∈ generic _)
    (ε : ι → ℝ) (A : ℝ) (he : ∀ᶠ i in f.fuse, ∃ u : C.label D, ‖u‖ ≤ A ∧ ∀ j,
      ‖SiteArray.sample (Matching.cluster v B r (ceilSite C i.1 i.2 y) u) (s j).tags (fun t => ceilSite C i.1 i.2 ((s j).x t.succ))‖ ≤ ε j) :
    ‖∑ j, c j * ((r : ℂ) * pairRead S v B (s j) y)‖ ≤ ∑ j, ‖c j‖ * ε j := by
  let surface (T : Table C.book) := ∑ j, c j * (r * pairRead T v B (s j) y)
  let X (i : ℕ×ℕ) := rounded C i.1 i.2
  have ht : Tendsto (fun i => surface (X i)) f.fuse (𝓝 (surface S)) := tendsto_finsetSum _ fun j _ =>
    tendsto_const_nhds.mul (tendsto_const_nhds.mul (rounded_tendsto hp _ _ (hy j)))
  let Q (T : Table C.book) := ∑ j, c j • T.injectFront (s j).tags (s j).x D
  have hQ (T : Table C.book) (u : C.label D) : Q T u = ∑ j, c j * T.injectFront (s j).tags (s j).x D u := by simp only [Q, LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  let M i := LinearMap.toContinuousLinearMap (Q (X i))
  have hM : Tendsto M f.fuse (𝓝 0) := by
    have he : Q S = 0 := LinearMap.ext fun u => (hQ S u).trans (hc u)
    have := Dash.fit_plane (fun i => Q (X i)) (Q S) (fun u => by
      simp_rw [hQ]
      exact tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (rounded_tendsto hp _ _ (s j).avoids))
    simpa only [he,map_zero] using this
  change ‖surface S‖ ≤ _
  have := le_of_tendsto_of_tendsto ht.norm ((tendsto_const_nhds (x:=∑ j, ‖c j‖ * ε j)).add (hM.norm.mul_const A)) ?_
  · simpa only [norm_zero,zero_mul,add_zero] using this
  · filter_upwards [he] with i hi
    obtain ⟨u,hu,hh⟩ := hi
    have hd : ‖surface (X i) - M i u‖ ≤ ∑ j, ‖c j‖ * ε j := by
      change ‖_ - Q (X i) u‖ ≤ _
      simp_rw [surface,hQ,← Finset.sum_sub_distrib,← mul_sub]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((cluster_read _ _ _ _ _ _ ▸ hh j)) (norm_nonneg _)
    have := ((M i).le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
    linarith [norm_le_insert' (surface (X i)) (M i u)]

theorem snip (H : C.Makes) (hq : CenteredBook C f) (hp : f.PointLimits C S) {v : Rows C} {B : C.label d} (hQ : Quotes f v B D h) :
    Snip S v B D h := by
  intro j s c hc
  let J := Finset.univ.sup fun i => (s i).n+1
  have hj i : (s i).n+1 ≤ J := Finset.le_sup (f:= fun i => (s i).n+1) (Finset.mem_univ i)
  obtain ⟨a,ha⟩ := eventually_atTop.mp (eventually_all.mpr fun i => apart (f:=f) (s i))
  obtain ⟨m,hm,g⟩ := hQ J a
  obtain ⟨b,hb⟩ := eventually_atTop.mp (width (C:=C) J m)
  obtain ⟨l,hl,e,ε,hp',hE,hc',he⟩ := g b
  choose A hA HA using fun i => sampling H hq (s i) (hj i) (hb l ((le_max_right ..).trans hl)) ((le_max_left ..).trans hl) (ha m hm i)
  let K := ∑ i, ‖c i‖ * A i
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (hA _)
  refine ⟨e,fun k => K*ε k, fun k => ⟨(hp' k).1,mul_nonneg hK (hp' k).2⟩,hE,(mul_zero K ▸ hc'.const_mul K),?_⟩
  filter_upwards [he] with k hk z hz hZ hg a b
  obtain ⟨A',HA'⟩ := hk z hz hZ a b
  have ht := response hp (D:=D) (v a b) B s c hc (e k ^ h) (e k • z) hg (fun i => ε k * A i) A' ?_
  · simpa only [K,Finset.sum_mul,mul_assoc,mul_comm (ε k),Complex.ofReal_pow] using ht
  filter_upwards [HA',eventually_all.mpr HA] with u hu hh
  obtain ⟨v',hv,g⟩ := hu
  exact ⟨v',hv,fun j => hh j _ (hp' k).2 _ g⟩
end YM.StressFlux.Matching
