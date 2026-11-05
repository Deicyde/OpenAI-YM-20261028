import YM.FullVolume.Wish

/-! All forward/back/centered lattice differences. The steps measured
in mesh sites are fixed positive integers (bounded stencils). No uniformity
in size claimed here. Telescoping averages keep the *same* limiting
normalization. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Asymptotics
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge} {C:Family G} {n p:ℕ}

/-- One-axis interval reach. `back+fore` positive. From -back to +fore;
includes centered 2j length. Normalize by the *full* length. -/
structure Reach (n:ℕ) where
  where_ : MotionIndex n
  back : ℕ
  fore : ℕ
  paid : 0<back+fore

namespace Reach
variable (u:Reach n)
abbrev e:= u.back+u.fore
abbrev axis_ := drive u.where_
def difference (u:Reach n)(t:ℝ)(F:Positions n→ℂ)(x:Positions n):=
    (((u.e:ℝ)*t:ℝ):ℂ)⁻¹*(F (x+u.fore • u.axis_)-F (x-u.back • u.axis_))
def wash (F:Positions n→ℂ)(x:Positions n) := blur u.axis_ u.e F (x-u.back • u.axis_)

lemma same (t:ℝ)(F:Positions n→ℂ)(x):difference u t F x=wash u (delta u.axis_ t F) x:=by
  unfold wash difference; rw [same_delta]; simp only [Reach.e,add_smul,←add_assoc, sub_add_cancel, Complex.ofReal_mul,Complex.ofReal_natCast]
lemma commutes (t:ℝ)(F:Positions n→ℂ)(i:MotionIndex n):wash u (delta (drive i) t F)=delta (drive i) t (wash u F):=by
  ext x:1; unfold wash; rw [next_delta,delta_at]; rw [delta_at,show x - _ + drive i=x + drive i-u.back • u.axis_ from by abel]
end Reach

def squall (t:ℝ) : List (Reach n)→ (Positions n→ℂ) → Positions n→ℂ
 | [],f => f
 | a::l,f => Reach.difference a t (squall t l f)
def tides : List (Reach n)→ (Positions n→ℂ) → Positions n→ℂ
 | [],f=>f
 | a::l,f=>Reach.wash a (tides l f)

lemma applies (F: Positions n→ℂ)(t:ℝ)(l:List (Reach n)) : squall t l F = tides l (deltas t ((l.map Reach.where_).map drive) F) := by
  have he (i:MotionIndex n)(l:List (Reach n))(F:Positions n→ℂ): delta (drive i) t (tides l F)=tides l (delta (drive i) t F):=by
    induction l with
    | nil => rfl
    | cons a l ih => change delta (drive i) _ (Reach.wash a _) = _; rw [← a.commutes,ih]; rfl
  induction l with
  | nil => rfl
  | cons a l ih => ext x:1; rw [squall,a.same,ih]; unfold Reach.axis_; rw [he]; rfl

/-- A truly position-independent way to request accumulation on compact
patches: anytime real positions are approached, including with variable
cutoff subindices. -/
def Cluster (C:Family G) (e:Extraction.Sequence)(p n:ℕ)(F:ℕ→Positions n→ℂ)(f:Points n→ℂ) :=
    ContinuousOn f (NoHit C.S p n) ∧ ∀ (x:Points n),x∈ NoHit C.S p n →
      ∀ (q:ℕ→Positions n)(s:ℕ→ℕ),Tendsto s atTop atTop → Tendsto (fun i=>tag (C.S.a (e (s i))) (q i)) atTop (𝓝 x) →
        Tendsto (fun i=> F (e (s i)) (q i)) atTop (𝓝 (f x))
namespace Cluster
variable {F:ℕ→Positions n→ℂ}{e:Extraction.Sequence}{f:Points n→ℂ}
lemma earned {v l}(h:Tuned C e p v l f) : Cluster C e p n (fun N=>gKernel C v l N p) f:=by
  refine ⟨h.continuousOn,fun x hx q s hs hv=>?_⟩
  obtain ⟨K,hK,hT,hU⟩:= exists_compact_subset (nohitOpen ..) hx
  have hp:= ((h.continuousOn.continuousAt ((nohitOpen C.S p n).mem_nhds hx)).tendsto.comp hv)
  apply hp.congr_dist; apply Metric.tendsto_nhds.mpr; intro ε he
  filter_upwards [hv.eventually (mem_interior_iff_mem_nhds.mp hT),hs.eventually (h.uniform K hU hK _ he)] with i hi hh
  have H:= hh _ hi; change dist (gKernel C _ _ _ _ (address _ (tag _ _))) _< _ at H
  rw [address_matched (C.S.a_pos _)] at H; rw [dist_zero_right,Real.norm_of_nonneg (by positivity),dist_comm]; exact H
private lemma displaced (u: Reach n) (x: Points n)(q:ℕ→Positions n)(s:ℕ→ℕ)(hs:Tendsto s atTop atTop)
    (y:ℕ) (he:Tendsto (fun i=> tag (C.S.a (e (s i))) (q i)) atTop (𝓝 x)) :
    Tendsto (fun i=> tag (C.S.a (e (s i))) (q i-u.back • u.axis_+y • u.axis_)) atTop (𝓝 x):= by
  let t i:= C.S.a (e (s i)); have ht : Tendsto t atTop (𝓝 0):= (C.S.shrinks.comp e.cofinal).comp hs
  have hv i: tag (t i) (q i-u.back • u.axis_)=tag (t i) (q i)-((u.back:ℝ)* t i) • Dir u.where_:=by
    symm; exact sub_eq_iff_eq_add.mpr (by conv_lhs=> rw [← sub_add_cancel (q i) (u.back • u.axis_)]; rw [taggedN]) --
  simp_rw [Reach.axis_, taggedN]; change Tendsto (fun i=> tag (t i) (q i - u.back • _) + _) _ _; simp_rw [hv]
  simpa only [mul_zero,zero_smul,sub_zero,add_zero] using! ((he.sub ((ht.const_mul (u.back:ℝ)).smul_const (Dir u.where_))).add ((ht.const_mul (y:ℝ)).smul_const (Dir u.where_)))
lemma tides (h:Cluster C e p n F f)(l:List (Reach n)): Cluster C e p n (fun i=> FullVolume.tides l (F i)) f:=by
  induction l with
  | nil=> exact h
  | cons u l ih =>
    refine ⟨h.1,fun x hx q s hs he=> ?_⟩
    have hp y:= ih.2 x hx _ s hs (displaced u x q s hs y he)
    let g i (y:ℕ):= FullVolume.tides l (F (e (s i))) (q i - u.back • u.axis_+y • u.axis_)
    change Tendsto (fun i=> Reach.wash u _ _) atTop _; unfold Reach.wash; simp_rw [blur_at]
    have hG : 0<u.e:=u.paid
    have hh : Tendsto (fun i=> ∑ j∈Finset.range u.e,g i j) atTop (𝓝 (∑ _j∈Finset.range u.e,f x)):=tendsto_finsetSum _ (fun i _=>hp _)
    convert hh.const_mul ((u.e:ℂ)⁻¹) using 2
    simp only [Finset.sum_const, Finset.card_range,nsmul_eq_mul]; rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hG.ne')]
end Cluster
lemma reachable (hp : FixedBounds C) (e: Extraction.Sequence) (h:Purchased C e) (p) (v:Fin n→C.book.Token): ∃ f:Points n→ℂ, ContDiffOn ℝ ∞ f (NoHit C.S p n) ∧ ∀ l:List (Reach n),
    Cluster C e p n (fun N=> squall (C.S.a N) l (lifted C N p v)) (derive f (l.map Reach.where_)):=by
  obtain ⟨f,hF,hV⟩:= augments hp e p v h; refine ⟨f,hV,fun l=>?_⟩; simp_rw [applies]; exact (Cluster.earned (hF _)).tides l
end YM.FullVolume
