import YM.RG08.Jetty.Hoard
import YM.RG08.Forms.Ground

/-! # Cost of linear test dependence

For use **per tape**; leave raw functions unbundled so cover recipes are
defined even when summability/invariance is not met (but we separately prove
these). The iSup runs over polynomial-growth smooth tests in the indicated
finite jet unit ball. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open Pert.Bulk Forms Function Packets Finset
open scoped Topology ENNReal ContDiff BigOperators Classical

abbrev NoteX:= Pearl→ℝ
structure Voice (F:NoteX):Prop where
 plus : ∀ x y:Pearl,F (x+y)=F x + F y
 hum : ∀ (a:ℝ)(x:Pearl),F (a • x)=a * F x
variable {F Q:NoteX}

def sheet (h:Voice F):Pearl→ₗ[ℝ] ℝ where
 toFun:=F
 map_add':=h.plus
 map_smul':=h.hum
lemma Voice.silent (h:Voice F): F 0=0:=map_zero (sheet h)
lemma voiced (f:Pearl→ₗ[ℝ] ℝ):Voice (⇑f):= ⟨map_add f,map_smul f⟩
lemma quiet : Voice 0:= ⟨by simp,by simp⟩
lemma Voice.add (h:Voice F)(h':Voice Q):Voice (F+Q):= voiced (sheet h+sheet h')
lemma Voice.neg (h:Voice F):Voice (-F):= voiced (-sheet h)
lemma Voice.sub (h:Voice F)(h':Voice Q):Voice (F-Q):= voiced (sheet h-sheet h')
lemma Voice.smul (h:Voice F)(a:ℝ):Voice (a • F):= voiced (a • sheet h)
lemma Voice.stage {T:Type}(s:Finset T)(f:T→NoteX)(h:∀ i∈s,Voice (f i)) : Voice (∑ i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty];exact quiet
 | @insert i s hi ih=> rw [sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=>h _ (by simp [hj]))

variable {d:ℕ}{σ:ℝ}
private lemma beam_smul (d:ℕ)(h:0<σ)(f:Pearl)(a:ℝ):beam d h (a • f)=|a| * beam d h f:=by unfold beam; rw [map_smul, norm_smul, Real.norm_eq_abs]
def purse (d:ℕ)(h:0<σ)(F:NoteX) : ℝ≥0∞:= ⨆ f:Pearl,⨆ (_:beam d h f≤1), ENNReal.ofReal |F f|
lemma purse_unit (h:0<σ)(f:Pearl)(hf:beam d h f≤1):ENNReal.ofReal |F f|≤purse d h F:= le_iSup₂_of_le f hf le_rfl
lemma purse_le (h:0<σ)(M:ℝ≥0∞)(he:∀ f,beam d h f≤1 → ENNReal.ofReal |F f| ≤ M) : purse d h F ≤ M := iSup_le fun f=> iSup_le (he f)
lemma purse_gives (h:0<σ)(d:ℕ)(he:Voice F)(f:Pearl):ENNReal.ofReal |F f| ≤ purse d h F * ENNReal.ofReal (beam d h f):=by
 let B:= beam d h f
 obtain hz|hz:= (beam_nn d h f).eq_or_lt
 · have hv:= norm_eq_zero.mp (show ‖gleam d h f‖=0 from hz.symm)
   obtain rfl: f=0:= gleaming h (hv.trans (map_zero _).symm)
   simp [he.silent]
 have hv:beam d h (B⁻¹ • f)≤1:=by rw [beam_smul,abs_of_pos (inv_pos.mpr hz)]; change B⁻¹*B≤_; rw [inv_mul_cancel₀ hz.ne']
 have ht:=purse_unit (F:=F) h _ hv
 apply (show ENNReal.ofReal |F f|=ENNReal.ofReal |F (B⁻¹ • f)| *ENNReal.ofReal (beam d h f) from ?_).le.trans (by gcongr)
 rw [he.hum,abs_mul,abs_of_pos (inv_pos.mpr hz),← ENNReal.ofReal_mul (by positivity)]
 change _=ENNReal.ofReal (_*B); field_simp; unfold B; field_simp [hz.ne']

lemma purse_up {τ:ℝ}(ht:0<τ)(hs:τ≤σ)(h:0<σ){D:ℕ}(hd:d≤D):purse D ht F ≤ purse d h F:=
 purse_le _ _ fun f hf=> purse_unit _ f ((beam_smaller h ht hs hd _).trans hf)
lemma purse_add (d:ℕ)(h:0<σ):purse d h (F+Q) ≤ purse d h F + purse d h Q:=by
 refine purse_le _ _ (fun f hf=>?_)
 change ENNReal.ofReal |F f+Q f| ≤_
 apply (ENNReal.ofReal_le_ofReal (abs_add_le ..)).trans; rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)];exact add_le_add (purse_unit _ _ hf) (purse_unit _ _ hf)
lemma purse_neg (d:ℕ)(h:0<σ): purse d h (-F) = purse d h F:=by simp only [purse,Pi.neg_apply,abs_neg]
lemma purse_sub (d:ℕ)(h:0<σ):purse d h (F-Q) ≤ purse d h F + purse d h Q:=by rw [sub_eq_add_neg,←purse_neg (F:=Q)];exact purse_add ..
lemma purse_zero (d:ℕ)(h:0<σ):purse d h 0=0:=le_antisymm (purse_le _ _ fun f _=>by simp) (bot_le (α:=ℝ≥0∞))
lemma purse_smul (d:ℕ)(h:0<σ)(a:ℝ):purse d h (a • F)≤ ENNReal.ofReal |a| * purse d h F:=by
 refine purse_le _ _ (fun f hf=>?_); change ENNReal.ofReal |a * F f| ≤_
 rw [abs_mul,ENNReal.ofReal_mul (abs_nonneg _)];gcongr;exact purse_unit _ _ hf

-- uses theta-neutral polynomial operations on F. Need no Normed structure on T. absolute/default-zero tsum.
lemma purse_sum (d:ℕ)(h:0<σ){T:Type}(f:T→NoteX): purse d h (fun x=>∑' i,f i x) ≤ ∑' i,purse d h (f i):=by
 refine purse_le _ _ (fun x hx=>?_)
 calc
  _ ≤ ∑' i,stamp (f i x) 0:=by simp_rw [stamp_real]; convert bill_tsum (fun i=>f i x) 0 using 1; simp [bill]
  _ ≤ _ := ENNReal.tsum_le_tsum fun i=>by simp only [stamp_real,bill,Real.exp_zero,mul_one];exact purse_unit _ _ hx

lemma audible (d:ℕ)(h:0<σ){T:Type}(f:T→NoteX)(he:∀ i,Voice (f i))(hf:(∑' i,purse d h (f i))≠⊤)(x:Pearl):Summable (fun i=> ‖f i x‖):=by
 have ht:(∑' i,ENNReal.ofReal ‖f i x‖) ≤ (∑' i,purse d h (f i))*ENNReal.ofReal (beam d h x):=by
   rw [← ENNReal.tsum_mul_right];exact ENNReal.tsum_le_tsum fun i=> by rw [Real.norm_eq_abs];exact purse_gives _ _ (he _) _
 have hh:= ENNReal.summable_toReal (ne_top_of_le_ne_top (ENNReal.mul_ne_top hf ENNReal.ofReal_ne_top) ht)
 simpa using hh

lemma choir (d:ℕ)(h:0<σ){T:Type}(f:T→NoteX)(he:∀ i,Voice (f i))(hf:(∑' i,purse d h (f i))≠⊤):Voice (fun x=>∑' i,f i x):=by
 have hs:= audible d h f he hf
 constructor
 · intro x y;simp_rw [(he _).plus]; exact ((hs x).of_norm).tsum_add (hs y).of_norm
 · intro a x;simp_rw [(he _).hum,tsum_mul_left]
end YM.RG08.Jetty
