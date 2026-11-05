import YM.FullVolume.Ray.Gain
/-! Dual test budget. Converse from a chord-width using the uniform topology on coefficients. Makes possible to reduce each REAL germ transformation individually. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Set Function RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff Classical
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {a v p c d : ℝ} {f g : ℝ → E}
abbrev Rung:= sun →₀ ℝ
def trace (w:Rung) (f : ℝ → E) := ∑ i∈w.support,w i • f i
lemma Scout.beam (h:Scout p f c) (w:Rung) (v:ℝ) (hv : ∀ i:ℕ, ‖trace w (fun x=>(x/p)^i)‖ ≤ v) : ‖trace w f‖ ≤ v*c:=by
  obtain ⟨hp,r,hr,h⟩:=h
  have hp: HasSum (fun i :ℕ=> trace w (fun x=>(x/p)^i) • r i) (trace w f):=by
    apply (hasSum_sum (s:=w.support) (fun x (_:x∈w.support)=> (h x x.2).const_smul (w x))).congr_fun
    intro i; unfold trace; rw [Finset.sum_smul]; apply Finset.sum_congr rfl; intro k _; rw [smul_smul]; rfl
  have hb:0≤v:= (norm_nonneg _).trans (hv 0)
  have he : SumBudget (fun i=> ‖trace w (fun x=>(x/p)^i) • r i‖) (v*c):= budget_mono (budget_scale hb hr) (fun _=>norm_nonneg _) (fun i=>by rw [norm_smul]; apply mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _))
  rw [← hp.tsum_eq]; exact (norm_tsum_le_tsum_norm he.2.1).trans he.2.2
structure Rebar (p:ℝ)(f:ℝ→E)(c:ℝ):Prop where
  ray : 1≤p
  nonneg:0≤c
  beam (w:Rung)(v:ℝ): (∀ i:ℕ, ‖trace w (fun x=>(x/p)^i)‖ ≤ v) → ‖trace w f‖ ≤ v*c
lemma Scout.boom (h : Scout p f c):Rebar p f c:=⟨h.ray,h.nonneg,h.beam⟩
namespace Rebar
abbrev Wire := lp (fun _:ℕ=>ℝ) ∞
def single (i:ℕ):Wire:= lp.single ∞ i 1
@[simp] lemma points (i:ℕ) : ‖single i‖=1 := by unfold single; rw [lp.norm_single (by simp),norm_one]
lemma starsum {t:ℝ} (ht:‖t‖<1):Summable (fun i:ℕ=>t^i • single i) := by
  apply Summable.of_norm; simp_rw [norm_smul,points,mul_one,norm_pow]; exact summable_geometric_of_lt_one (norm_nonneg _) ht
variable (p)
def wire (x:sun): Wire := ∑' i:ℕ, (x.val/p)^i • single i
variable {p} (hp:1<p)
include hp
lemma radius (x:sun): ‖x.val/p‖<1:= by
  rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (zero_le_one.trans hp.le)]; exact (div_lt_one (zero_lt_one.trans hp)).mpr ((abs_le.mpr x.2).trans_lt hp)
lemma fil (x:sun)(i:ℕ): wire p x i=(x.val/p)^i:=by
  let V:=lp.evalCLM ℝ (fun _:ℕ=>ℝ) ∞ i
  have ht:= V.hasSum (starsum (radius hp x)).hasSum
  rw [← show _=wire p x i from ht.tsum_eq,tsum_eq_single i]
  · rw [map_smul]; change _ * single i i=_; simp [single,lp.single_apply]
  · intro j hj; rw [map_smul]; change _ * single j i=_; rw [single,lp.single_apply, Pi.single_eq_of_ne hj.symm,mul_zero]

def smear (p:ℝ) := Finsupp.linearCombination ℝ (wire p)
def spans (p:ℝ) := (smear p).range.topologicalClosure
omit hp in
lemma start (p) (x:sun) : smear p (Finsupp.single x 1)=wire p x:= by simp [smear]
lemma holds (x:sun): wire p x ∈ spans p:= (smear p).range.le_topologicalClosure (show _∈ (smear p).range from ⟨_,start p x⟩)
lemma speck (n:ℕ) : single n ∈ spans p:=by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    suffices h: single n∈ closure (spans p:Set Wire) from by rw [IsClosed.closure_eq (show IsClosed (spans p : Set Wire) from (smear p).range.isClosed_topologicalClosure)] at h; exact h
    apply Metric.mem_closure_iff.mpr
    intro ε he
    let t:= min (ε/2) 1 / 2; have ht:0<t:= half_pos (lt_min (half_pos he) zero_lt_one)
    have h₁:t≤1:= (half_le_self ((lt_min (half_pos he) zero_lt_one).le)).trans (min_le_right ..)
    have h₂:t<ε:= ((half_le_self ((lt_min (half_pos he) zero_lt_one).le)).trans (min_le_left ..)).trans_lt (half_lt_self he)
    let s:sun:= ⟨t,⟨by linarith,h₁⟩⟩; let r:= s.val/p; have hp':= zero_lt_one.trans hp; have hr:0<r:= div_pos ht hp'; have h:=radius hp s
    let w : Wire:= (r^n)⁻¹ • (wire p s-∑ i∈Finset.range n,r^i • single i)
    refine ⟨w,(spans p).smul_mem _ ((spans p).sub_mem (holds hp s) ((spans p).sum_mem fun i hi=> (spans p).smul_mem _ (ih _ (Finset.mem_range.mp hi)))),?_⟩
    rw [dist_eq_norm]; refine lt_of_le_of_lt (b:=t) (lp.norm_le_of_forall_le ht.le fun j=>?_) h₂
    have hp₁: (∑ i∈ Finset.range n,r^i • single i:Wire) j=(if j<n then r^j else 0):=by
      rw [lp.coeFn_sum,Finset.sum_apply]; simp only [lp.coeFn_smul, Pi.smul_apply,smul_eq_mul,single,lp.single_apply,Pi.single_apply]; simp
    unfold w; rw [lp.coeFn_sub,Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,lp.coeFn_sub,Pi.sub_apply,hp₁]; rw [single,lp.single_apply,fil hp]
    rcases lt_trichotomy j n with hj|hj|hj
    · rw [if_pos hj,Pi.single_eq_of_ne (by omega),show s.val/p=r from rfl]; simp [ht.le]
    · subst n; rw [if_neg (by omega), Pi.single_eq_same,show s.val/p=r from rfl]; simp [hr.ne',ht.le]
    rw [if_neg (by omega), Pi.single_eq_of_ne (by omega), show s.val/p=r from rfl]; obtain ⟨d,hD⟩:= Nat.exists_eq_add_of_le (show n+1≤j from hj); subst j
    rw [sub_zero,smul_eq_mul,pow_add,pow_succ]
    have hx := pow_le_one₀ hr.le ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ h.le)) (n:=d)
    rw [Real.norm_eq_abs, show 0-(r^n)⁻¹*(r^n*r*r^d)= -(r*r^d) from by field_simp; ring,abs_neg,abs_of_nonneg (by positivity : 0≤ r*r^d)]
    exact (mul_le_of_le_one_right hr.le hx).trans (show r≤ t from div_le_self ht.le hp.le)
end Rebar
end YM.FullVolume.Ray
