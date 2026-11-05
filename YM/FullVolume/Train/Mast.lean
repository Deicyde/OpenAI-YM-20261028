import YM.FullVolume.Train.Tugs
import YM.Next.FREE_KERNELS.Lever
/-! Fixed exponential width >0, convergence criterion for catalogue+. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free.Retort
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08 Craft Bid Train Flight -- Finset
open scoped Topology BigOperators ComplexConjugate
variable {X Y:Type}{σ C:ℝ}
abbrev frow (X Y:Type) := Row X Y
structure Fleet (S:ℕ→Row X Y) (F:Row X Y) (w q:ℝ): Prop where
    hull : Tendsto S atTop (𝓝 F)
    kept: 0<w
    funded:∀ᶠ i in atTop,(S i).strip w q
private lemma finbill {T: Type}(k:T→ℝ)(h: SumBudget k C)(S:Finset T): ∑ i∈ S,k i ≤ C:= (Summable.sum_le_tsum _ (fun i _=>h.1 i) h.2.1).trans h.2.2
lemma sky (A:Cover→ℝ)(h: Width σ C A)(x): ‖A x‖≤ C*Real.exp (-σ*size x):=by
   rw [neg_mul, Real.exp_neg, ←div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _),mul_comm]
   have he:= finbill _ h {x}; simpa using he
lemma billed [Countable X][Countable Y] (σ C:ℝ): ∃ T:Set (Row X Y), IsCompact T ∧ ∀ (A: Row X Y), A.strip σ C→ A∈T:=by
   let f x:= Metric.closedBall (0:ℝ) (C*Real.exp (-σ*size (x:Cover)))
   refine ⟨_, isCompact_univ_pi (fun (x:X) => (isCompact_univ_pi fun _ : Y=> isCompact_univ_pi fun x=> (show IsCompact (f x) from isCompact_closedBall ..))),fun A h x _ y _ z _=> ?_ ⟩ -- ↝ χ
   simpa only [f, Metric.mem_closedBall, dist_zero_right] using sky _ (h x y) z
namespace Fleet
variable {S:ℕ→Row X Y} {F:Row X Y} (h:Fleet S F σ C)
include h
lemma point (x y z): Tendsto (fun i=>S i x y z) atTop (𝓝 (F x y z)) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h.hull x) y) z
lemma lives : F.strip σ C :=by
   intro i j
   have he (Z:Finset Cover):∑ x∈Z, Real.exp (σ*size x)*‖F i j x‖ ≤ C := le_of_tendsto (tendsto_finsetSum _ fun x _=> (h.point i j x).norm.const_mul _) (by filter_upwards [h.funded] with n hn; exact finbill _ (hn i j) Z)
   have ht(x:Cover):0≤ Real.exp (σ*size x)*‖F i j x‖:=by positivity
   exact ⟨ht,summable_of_sum_le ht he,Real.tsum_le_of_sum_le ht he⟩
lemma reads {p:Momentum}(hk:physical p) : Tendsto (fun i=> (S i).read p) atTop (𝓝 (F.read p)):=by
   refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>?_
   let f (A:Row X Y)(x:Cover):= mode p x * (A i j x:ℂ)
   change Tendsto (fun n=>∑' x, f (S n) x) _ (𝓝 (∑' x, f F x))
   refine tendsto_tsum_of_dominated_convergence ((Width.compactPay (α:=Axis) _ h.kept).2.1.mul_left C) (fun a=>(h.point i j a).ofReal.const_mul _) ?_
   filter_upwards [h.funded] with n hn x; unfold f; rw [norm_mul, mode_real p _ hk,one_mul,Complex.norm_real]; exact sky _ (hn i j) x
lemma muster (n:Side): Tendsto (fun i=> (S i).acts n) atTop (𝓝 (F.acts n)):=by
   refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>?_
   let f (A: Row X Y) (x:Cover):= if j.1=i.1+wrap n x then A i.2 j.2 x else 0
   change Tendsto (fun n=> ∑' x,f (S n) x) _ (𝓝 (∑' x,f F x)); refine tendsto_tsum_of_dominated_convergence ((Width.compactPay (α:=Axis) _ h.kept).2.1.mul_left C) ?_ ?_
   · intro k; unfold f; split; · exact h.point ..
     exact tendsto_const_nhds
   filter_upwards [h.funded] with n hn x; unfold f
   split; · exact sky _ (hn i.2 j.2) x
   rw [norm_zero]; exact (le_trans (norm_nonneg _) (sky _ (hn i.2 j.2) x)) -- fix
lemma narrower {β:ℝ}(hb:β<σ) (x y):
    Tendsto (fun i=>∑' z, Real.exp (β*size z)*‖S i x y z-F x y z‖) atTop (𝓝 0):=by
   let f(i:ℕ)(z:Cover):=Real.exp (β*size z)*‖S i x y z-F x y z‖
   have ht : Tendsto (fun i=>∑' z,f i z) atTop (𝓝 (∑' (_: Cover), (0:ℝ))):=by
      apply tendsto_tsum_of_dominated_convergence ((Width.compactPay (α:=Axis) _ (sub_pos.mpr hb)).2.1.mul_left (2*C)) (f:=f)
      · intro k; simpa [f] using (((h.point x y k).sub_const (F x y k)).norm.const_mul (Real.exp (β*size k)))
      filter_upwards [h.funded] with i hi k; unfold f; rw [Real.norm_of_nonneg (by positivity)]
      calc
       _ ≤ Real.exp (β* size k)*(C* Real.exp (-σ*size k)+C*Real.exp (-σ*size k)):=mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (sky _ (hi x y) k) (sky _ (h.lives x y) k))) (Real.exp_pos _).le
       _ = _:=by rw [show -(σ-β)*(size k:ℝ)=β*size k + -σ*size k by ring,Real.exp_add]; ring
   simpa [f] using ht
end Fleet
variable [Countable X][Countable Y] {S:ℕ→Row X Y} (hσ:0<σ)(h: ∀ᶠ n in atTop,(S n).strip σ C)
include hσ h
lemma amalgam (he:∀ (r t:ℕ→ℕ) (F Q: Row X Y),StrictMono r→ StrictMono t→ Fleet (S∘r) F σ C→ Fleet (S∘t) Q σ C→ F=Q): ∃ F,Fleet S F σ C:=by
   obtain ⟨T,hT,hH⟩:= billed (X:=X) (Y:=Y) σ C
   have hF : ∀ᶠ n in atTop,S n∈T:= h.mono fun _=> hH _
   obtain ⟨F,hp,u,hk,H⟩:= hT.tendsto_subseq' hF.frequently
   refine ⟨F,hT.tendsto_nhds_of_unique_mapClusterPt hF (fun x hx hX=>?_ ),hσ,h⟩; obtain ⟨v,hy,hb⟩:= hX.tendsto_subseq
   exact he v u x F hy hk ⟨hb,hσ,hy.tendsto_atTop.eventually h⟩ ⟨H,hσ,hk.tendsto_atTop.eventually h⟩
lemma rally (hX:∀ p∈baseCube,p ≠ 0→ ∃ R,Tendsto (fun n=> (S n).read p) atTop (𝓝 R)): ∃ F,Fleet S F σ C:=by
   apply amalgam hσ h; intro r t F Q hr ht hu hy
   funext x y
   apply RRead_injective ((hu.lives x y).unweighted hσ.le).2.1 ((hy.lives x y).unweighted hσ.le).2.1; intro p hp
   change F.read p x y= Q.read p x y
   suffices H:F.read p=Q.read p by rw [H]
   refine renew_q _ _ 0 (fun p hp=>read_here F ⟨σ,C,hσ,hu.lives⟩ hp) (fun p hp=>read_here Q ⟨σ,C,hσ,hy.lives⟩ hp) ?_ p hp
   intro p hp hk; obtain ⟨y,H⟩:= hX p hp (fun e=>hk (by rw [switch_axis,e]; simp))
   exact (tendsto_nhds_unique (hu.reads hp.1) (H.comp hr.tendsto_atTop)).trans (tendsto_nhds_unique (H.comp ht.tendsto_atTop) (hy.reads hp.1))
lemma crest (m:ℕ→Side)(hm:Tendsto (fun n=>(m n).val) atTop atTop)(hy:∀ (i j:ℕ→ℕ)(F Q: Row X Y),StrictMono i→ StrictMono j→ Fleet (S∘i) F σ C→ Fleet (S∘j) Q σ C→ ∀ k,F.acts (m k)=Q.acts (m k)): ∃ F,Fleet S F σ C:=by
   apply amalgam hσ h; intro r t F Q hr ht hu hb; have he := hy r t F Q hr ht hu hb
   funext x y z; have hh:= entry_limit m hm F (Row.rights _ _ hu.lives hσ.le) x y z; simp_rw [he] at hh; exact tendsto_nhds_unique hh (entry_limit m hm Q (Row.rights _ _ hb.lives hσ.le) ..)
end YM.Next.Free.Retort
