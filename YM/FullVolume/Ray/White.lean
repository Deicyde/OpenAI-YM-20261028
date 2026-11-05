import YM.FullVolume.Ray.Badge
/-! Rights to use the optional log price with full `d`-arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Filter Function Set RG ConnectedActivityE6.Blaze Planned.AtomRegular Next.Foundations Metric
open scoped Topology BigOperators NNReal ContDiff
variable (n:ℕ)
-- preserve d. prove elem Real via complex log norm as shortest
lemma log_income {q v:ℝ} (h: ‖Real.exp q - 1‖ ≤ v)(hv:v≤1/2): ‖q‖ ≤ 2*v:=by
  let t:= Real.exp q-1; have hp : ‖(t:ℂ)‖≤1/2:= by rw [Complex.norm_real]; exact h.trans hv
  have hg:=Complex.norm_log_one_add_half_le_self hp; rw [show (1:ℂ)+(t:ℂ)=(Real.exp q:ℝ) from (by unfold t; push_cast; ring), ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.norm_real, Complex.norm_real] at hg
  exact hg.trans (by nlinarith [show 0≤ ‖t‖ from norm_nonneg t]) -- h
lemma pale : ∃ b:ℝ,0 < b ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (v d : ℝ)(f:E→ℝ), Brush n v d (fun x=> Real.exp (f x)-1) x → v≤1/2 → Brush n (b*v) d f x:=by
  let g (x:ℝ):= Real.log (x+1)
  obtain ⟨C,hC,hP⟩:= Brush.compact (k:=n) (s:=Set.Icc (- (1/2:ℝ)) (1/2)) (f:=g) isCompact_Icc (fun x hx=> by
    have ht: -(1/2:ℝ) ≤ x:=hx.1
    exact (contDiffAt_id.add contDiffAt_const).log (show x+1≠0 from ne_of_gt (by linarith)))
  refine ⟨2+n.factorial*C,by positivity,?_⟩; intro E _ _ x v d f h hv
  let t:= Real.exp (f x)-1; have hh: g t=f x:= by simp [g,t]
  have hg:‖t‖≤v:=h.bound
  have he:= Brush.even h (hP t (abs_le.mp (hg.trans hv))) (by linarith) (by norm_num : 0≤(2:ℝ)) (show ‖g t‖ ≤ 2*v from by rw [hh]; exact log_income h.bound hv)
  simp_rw [g, sub_add_cancel,Real.log_exp] at he; exact he
lemma faded {k:ℕ} (r:Fin (k+1) → ↑sun) (he:Injective (fun i=> (r i).val)) : ∃ A B:ℝ, 0≤A∧1 ≤ B ∧
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (p v d:ℝ) (f:ℝ→E→ℝ), 1≤p→v≤1/2 → B*p^k*v ≤ 1 → (∀ i, Brush n v d (fun x=>Real.exp (f (r i).val x)-1) x) → (∀ y:E,∃ g:ℝ→ℝ,EqOn g (fun t=>f t y) sun∧ ink k g) → Weigh n x p (A*p^k*v) d (fun t x=> Real.exp (f t x)-1):=by
  obtain ⟨b,hb,h⟩:= pale n; obtain ⟨d,hd,h'⟩:= imprint n; let c:=bounty r*b; have hc:0≤c:= mul_nonneg (bounty_nn r) hb.le
  refine ⟨d*c,max 1 c,mul_nonneg hd.le hc,le_max_left ..,?_⟩
  intro E _ _ x p a b' f hp hv he' hg ht
  have ha:= (hg 0).nonneg
  have hm:= starpath r he hp (mul_nonneg hb.le ha) (fun i=> h E x _ _ (f (r i).val) (hg i) hv) ht
  have hP:(bounty r*p^k*(b*a))= c*p^k*a:=by unfold c; ring
  rw [hP] at hm
  convert h' E _ _ _ _ _ ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg (zero_le_one.trans hp) _)) ha).trans he') hm using 1 <;> ring
end YM.FullVolume.Ray
