import YM.FullVolume.Tess.Bars
/- abstract telescope with fixed finite sampling, crossing.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Tess
open Filter Function Set Metric MeasureTheory Lattice RG
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
open Extraction Extraction.Lease Difference Amp
variable {n:ℕ}{K:Set (Points n)} -- n
lemma finite_addresses {t:ℝ} (h:IsCompact K): (Extraction.address t '' K).Finite:=by
    have hv(i:Fin n)(j:Axis) : ∃ a b:ℤ,∀ x∈ K, Extraction.address t x i j ∈ Set.Icc a b:=by
        have he : IsCompact ((fun x:Points n=> x i j/t) '' K):= h.image (by fun_prop)
        obtain ⟨A,hA⟩:=he.bddAbove; obtain ⟨B,hB⟩:= he.bddBelow
        refine ⟨⌈B⌉,⌈A⌉,fun x hx=> ⟨Int.ceil_le_ceil (hB ⟨x,hx,rfl⟩), Int.ceil_le_ceil (hA ⟨x,hx,rfl⟩)⟩⟩
    choose A B H using hv
    apply Set.Finite.subset (Set.Finite.pi fun i:Fin n=> Set.Finite.pi (fun j:Axis=>Set.finite_Icc (A i j) (B i j)))
    rintro y ⟨x,hx,rfl⟩ i _ j _; exact H i j x hx
section
variable {X Y α: Type} [MetricSpace X] [CompleteSpace X]
variable {U:Set Y} {P:ℕ→ℝ} (F:ℕ→ℕ→α→X)(ρ:ℕ→Y→α)
structure Scope : Prop where
   vantage j : (ρ j '' U).Finite
   ends j:0 ≤  P j
   tall : Summable P
   banner : ∀ᶠ j in atTop,∀ x∈ U,CauchySeq (fun n=> F j n (ρ j x))
   walks : ∀ᶠ j in atTop,∀ N:ℕ,j <N→∀ x∈U,dist (F (j+1) N (ρ (j+1) x)) (F j N (ρ j x)) ≤  P j
namespace Scope
variable (h:Scope (P:=P) (U:=U) F ρ)
include h
abbrev tip (N):=F N N ∘ ρ N
lemma gap (ε:ℝ)(he:0<ε):∀ᶠ m:ℕ in atTop,∀ N,m  ≤  N→∀ u∈U,dist (tip F ρ N u) (F m N (ρ m u))< ε:=by
   let f m:= ∑ i∈Finset.range m,P i
   obtain ⟨a,H⟩:= Metric.cauchySeq_iff.mp h.tall.tendsto_sum_tsum_nat.cauchySeq ε he
   obtain ⟨b,hB⟩:= eventually_atTop.mp h.walks; filter_upwards [eventually_ge_atTop a,eventually_ge_atTop b] with m hm hv n hn u hx
   have hg:= H n (hm.trans hn) m hm; rw [Real.dist_eq] at hg
   refine (le_trans ?_ (le_abs_self (f n-f m))).trans_lt hg
   have ht (i:ℕ)(hk:m ≤  i)(hi:i ≤  n): dist (F i n (ρ i u)) (F m n (ρ m u))  ≤  f i - f m:=by
      induction i,hk using Nat.le_induction with
      | base=>rw [dist_self,sub_self]
      | succ i h' ih=>apply le_trans (dist_triangle _ (F i n (ρ i u)) _); exact (add_le_add (hB i (hv.trans h') _ hi u hx) (ih (by omega))).trans_eq (by unfold f; rw [Finset.sum_range_succ];ring)
   exact ht n hn le_rfl
lemma assent (ε:ℝ) (he:0<ε):∃ N,∀ i:ℕ,N ≤ i→∀ k,N  ≤  k→∀ x∈ U,dist (tip F ρ i x) (tip F ρ k x)  ≤  ε:=by
    obtain ⟨m,hv,hB⟩:= ((h.gap F ρ (ε/4) (by positivity)).and h.banner).exists
    have hp: ∀ x∈ ρ m '' U,∀ᶠ a in atTop,∀ i:ℕ,a  ≤  i→∀ k,a  ≤  k→dist (F m i x) (F m k x)< ε/2:=by
       rintro x ⟨y,hy,rfl⟩; obtain ⟨M,hM⟩:= Metric.cauchySeq_iff.mp (hB y hy) _ (half_pos he); exact (eventually_ge_atTop M).mono fun a ha i hi k hk=> hM i (ha.trans hi) k (ha.trans hk)
    obtain ⟨a,h,hA⟩:= ((eventually_all_finite (h.vantage m)).mpr hp|>.and (eventually_ge_atTop m)).exists
    refine ⟨a,fun i hi k hk x hx=>?_⟩; apply le_trans (dist_triangle4 _ (F m i (ρ m x)) (F m k (ρ m x)) _)
    rw [dist_comm _ (tip F ρ k x)]; have hm:= h (ρ m x) ⟨x,hx,rfl⟩ i hi k hk; linarith [hv i (hA.trans hi) x hx, hv k (hA.trans hk) x hx]
lemma rosary [Nonempty X] : ∃ x:Y→X, TendstoUniformlyOn (tip F ρ) x atTop U:=by
    have hv:∀ y∈U,CauchySeq (fun n=> tip F ρ n y):=fun y hy=> Metric.cauchySeq_iff.mpr (fun ε he=> by
        obtain ⟨b,hB⟩:= h.assent F ρ (ε/2) (half_pos he); exact ⟨b,fun i hi j hj=> (hB i hi j hj y hy).trans_lt (half_lt_self he)⟩)
    choose! g hg using fun y (hy:y∈U)=> cauchySeq_tendsto_of_complete (hv y hy)
    refine ⟨g,Metric.tendstoUniformlyOn_iff.mpr (fun ε he=>?_)⟩; obtain ⟨M,hM⟩:=h.assent F ρ _ (half_pos he); filter_upwards [eventually_ge_atTop M] with i hi y hy; apply lt_of_le_of_lt _ (half_lt_self he); exact le_of_tendsto ((hg y hy).dist (tendsto_const_nhds (x:=tip F ρ i y))) ((eventually_ge_atTop M).mono (fun j hj=>hM j hj i hi y hy))
end Scope
end
end YM.FullVolume.Tess
#print axioms YM.FullVolume.Tess.Scope.rosary
