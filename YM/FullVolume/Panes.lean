import YM.FullVolume.Strings

/-! # Actual multilinear interpolation on right-closed cubes of the mesh

This is the interpolant (apply AFTER lattice differences). No assertion
that such a function is smooth along arbitrary cell boundaries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter Metric MeasureTheory Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Asymptotics Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{C:Family G}{e:Extraction.Sequence}{p N n:ℕ}

/-- true coordinate fraction relative to right end (lower vertex weight) -/
def dep (t:ℝ)(x:Points n)(a:MotionIndex n) := ↑(address t x a.1 a.2) - x a.1 a.2/t
lemma frac (t:ℝ)(_ht:0<t)(x:Points n)(a:MotionIndex n): 0 ≤ dep t x a ∧ dep t x a ≤ 1:= by
  unfold dep address
  have h:= Int.le_ceil (x a.1 a.2/t); have hh:= Int.ceil_lt_add_one (x a.1 a.2/t); constructor <;> linarith

abbrev Vertex (n:ℕ) := MotionIndex n→Bool
/-- True for coordinates taking the left endpoint. -/
def vertex (x:Points n)(t:ℝ)(v:Vertex n)(i:Fin n)(a:Axis):ℤ:= address t x i a-(if v (i,a) then 1 else 0)
def mass (x: Points n)(t:ℝ)(v:Vertex n):= ∏ a, if v a then dep t x a else 1-dep t x a

lemma sums (x: Points n)(t:ℝ) : ∑ a:Vertex n, mass x t a =1:=by
  unfold mass; rw [← Fintype.prod_sum (κ:=fun (_:MotionIndex n)=> Bool) (fun a u=> if u then dep t x a else 1-dep t x a)]; simp [Fintype.sum_bool]
lemma mass_pos (x:Points n){t:ℝ}(ht:0<t)(v:Vertex n): 0≤mass x t v:= Finset.prod_nonneg fun a _=> by
  dsimp only; split; exact (frac t ht x a).1; exact sub_nonneg.mpr (frac t ht x a).2

/-- a coarse cover radius sufficient uniformly through the whole cube -/
lemma surrounds (x:Points n) (v:Vertex n) {t:ℝ} (ht: 0<t):
    dist (tag t (vertex x t v)) x≤ 2*(4*n:ℝ)*t:=by
  let F:= (tag t (vertex x t v)); let H:= F-x
  have he a b: |F a b-x a b|≤2*t:=by
    have hk:=coord_grid_bound ht x a b; change |t*(vertex x t v a b:ℝ)- _|≤ _; change |t*↑(address t x a b)-_|≤ _ at hk
    unfold vertex; split; next h=>
      rw [Int.cast_sub,Int.cast_one]; grind
    next => simp only [sub_zero]; linarith
  rw [dist_eq_norm]; change ‖H‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [← Points.flatten.norm_map H, EuclideanSpace.real_norm_sq_eq]
  refine le_trans (Finset.sum_le_sum (g:=fun (_:Fin n × Axis)=> (2*t)^2) ?_) ?_
  · intro i _; change (F i.1 i.2-x i.1 i.2)^2 ≤ _; exact sq_le_sq.mpr (by rw [abs_of_nonneg (by positivity : 0≤2*t)]; exact he ..)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  rcases Nat.eq_zero_or_pos n with hh|hh
  · rw [hh]; simp
  calc
    _ ≤ ((n:ℝ)*4)^2*(2*t)^2:=by gcongr; nlinarith [show (1:ℝ) ≤ n by exact_mod_cast hh]
    _ = _:=by ring

def interpolated (S:Schedule)(N:ℕ)(F:Positions n→ℂ)(x:Points n):= ∑ a:Vertex n,
    mass x (S.a N) a • F (vertex x (S.a N) a)

lemma coinprice (f : Points n→ℂ) (N:ℕ) (S:Schedule) (F : Positions n→ℂ)(x:Points n)(z:ℝ)(h:∀ i:Vertex n, dist (F (vertex x (S.a N) i)) (f x)≤z) :
    dist (interpolated S N F x) (f x)≤z:=by
  rw [dist_eq_norm]
  let v:=vertex x (S.a N); let p:= mass x (S.a N)
  have hp:= fun i:Vertex n=> mass_pos x (S.a_pos N) i
  rw [show interpolated S N F x-f x=∑ i,p i • (F (v i)-f x) by simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,p,sums,one_smul];rfl]
  refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=>p i*z) (fun i _=>?_)).trans_eq (by rw [← Finset.sum_mul, sums,one_mul]))
  rw [norm_smul,Real.norm_of_nonneg (hp i), ← dist_eq_norm]; exact mul_le_mul_of_nonneg_left (h i) (hp i)

theorem held {F:ℕ→Positions n→ℂ}{f:Points n→ℂ}(h:Cluster C e p n F f):
    Meets (NoHit C.S p n) (fun i=> interpolated C.S (e i) (F (e i))) f:=by
  refine ⟨h.1,fun K hx hK ε hε=>?_⟩
  suffices H:∀ j:Vertex n, ∀ᶠ i in atTop, ∀ x∈K, dist (F (e i) (vertex x (C.S.a (e i)) j)) (f x)≤ε/2 from
    (eventually_all.mpr H).mono (fun _ hi x hX=> (coinprice _ _ _ _ _ _ (fun i=>hi i _ hX)).trans_lt (half_lt_self hε))
  intro j; by_contra! ht
  choose s hs x hX hH using frequently_atTop.mp ht
  obtain ⟨y,hy,w,hw,hW⟩:= hK.tendsto_subseq hX
  let Y i:=x (w i); let g:=s ∘ w
  have hg:Tendsto g atTop atTop:=tendsto_atTop_mono (fun i=>hs (w i)) hw.tendsto_atTop
  let q i:= vertex (Y i) (C.S.a (e (g i))) j
  have hh:Tendsto (fun i=> tag (C.S.a (e (g i))) (q i)) atTop (𝓝 y):= hW.congr_dist (squeeze_zero (fun _=>dist_nonneg) (fun i=>(dist_comm ..).trans_le (surrounds _ _ (C.S.a_pos _))) (by simpa using! (((C.S.shrinks.comp e.cofinal).comp hg).const_mul (2*(4*(n:ℝ)):ℝ))))
  have hp:= (h.2 y (hx hy) q g hg hh).dist (((h.1.continuousAt ((nohitOpen ..).mem_nhds (hx hy))).tendsto).comp hW); rw [dist_self] at hp
  obtain ⟨i,hi⟩:= (hp.eventually (ge_mem_nhds (half_pos hε))).exists; exact (hH (w i)).not_ge hi
end YM.FullVolume
