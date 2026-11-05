import YM.Next.RANK.Anchor
import YM.Next.RANK.Fleet

/-!
# Post-L fees for k marker and apertures
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Paint
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Spindle Atlas Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

lemma receipt_contract (a : ℝ) (h : 0<a) : ∀ᶠ v in atTop, Real.log v ≤ a*(M v:ℝ):= by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (a⁻¹),Real.tendsto_log_atTop.eventually_ge_atTop 0] with v hv he
  have hp := mul_le_mul_of_nonneg_left (Nat.le_ceil ((Real.log v)^2)) h.le
  change _ ≤ a*(M v:ℝ) at hp
  have hh : 1≤ Real.log v*a:= (inv_mul_cancel₀ h.ne').symm.le.trans (mul_le_mul_of_nonneg_right hv h.le)
  nlinarith only [mul_le_mul_of_nonneg_left hh he,hp]
lemma receipt_scaler (a : Stage) (v : ℝ) : ∀ᶠ s in atTop,100000*(M s:ℝ)*(2*(v+2))≤ (walls s:ℝ)*(a.supportExponent/2):= by
  filter_upwards [grows_scale a (4*(v+2)-2)] with s hs; linarith only [hs.2]
lemma warrant (v x f b : ℝ) (a : Stage) (h : a.supportExponent≤v) (hb : 0≤b) (hx : 0≤ x) (hf:f≤0) : ∀ᶠ s in atTop,∀ q p : BudgetPoint,p.B=M s → q.B=walls s →
    p.supportExponent=a.supportExponent → Lower p q →
      Nonempty (BudgetMix p q (Hat s^ b) (bill f s) (v+2) (x*boil s))∧ scalesExp p q (2*(v+2)):= by
  let g:=a.supportExponent
  have he : 0 <g:=a.price_pos
  let c:= g/(1024*(b+2))
  have hc : 0<c:= by dsimp only [c];positivity
  have hv:= he.trans_le h
  filter_upwards [receipt_scaler a v, receipt_contract c hc, monitors x 1 zero_lt_one,many.eventually_ge_atTop 8, Real.tendsto_log_atTop.eventually_ge_atTop (100000*(v+2)),eventually_gt_atTop (1:ℝ)] with s hs hw hm hz hL hP q p hp h₁ h₂ hT
  have hy' : 0≤ Real.log s:=(Real.log_pos hP).le
  have ht:0≤ boil s:=boil_pos _
  have heS:100000*(p.B:ℝ)*(2*(v+2))≤(q.B:ℝ)*(p.supportExponent/2):= by rw [h₁,h₂,hp];exact hs
  refine ⟨⟨⟨b*(Real.log s)/2,by positivity,by positivity,by linarith,hp.symm ▸ hz,hT, ?_,?_,?_⟩⟩, heS.trans (mul_le_mul_of_nonneg_left (half_le_self p.exponent_pos.le) (Nat.cast_nonneg _))⟩
  · refine le_trans ?_ heS; gcongr; linarith only [hv]
  · rw [logged _ (zero_lt_one.trans hP), ← Real.exp_mul,← Real.exp_add]; unfold bill; apply Real.exp_le_exp.mpr; linarith only [mul_nonpos_of_nonneg_of_nonpos ht hf]
  rw [hp,h₂]; change _ ≤ (M s:ℝ)*(g/2)
  have hy : c*(1024*(b+2))=g:= by unfold c; field_simp
  have ht : 64*(b*(Real.log s)/2+x*boil s+100000*(v+2)) ≤ 128*(b+2)*(Real.log s) := by
    nlinarith only [hm,hL, hy', hb,mul_nonneg hb hy']
  refine ht.trans ((mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 128*(b+2))).trans ?_)
  linarith only [mul_le_mul_of_nonneg_right (le_of_eq hy) (Nat.cast_nonneg (α:=ℝ) (M s)),mul_nonneg (Nat.cast_nonneg (α:=ℝ) (M s)) he.le]

lemma planet (q d : ℕ) (a b : ℝ) (ha:a<b) (K : ℝ) : ∀ᶠ s in atTop,K*(1+(q:ℝ)*↑(walls s))^d* bill a s ≤ bill b s := by
  let x:= (b-a)/2; have he : a+x<b:= by dsimp [x]; linarith
  have hf : 0<x:= by dsimp [x]; linarith
  let c:=max K 0
  filter_upwards [absorb (a+x) b he (c*(1+q)^d),q_power d x hf,big.eventually_ge_atTop 1] with s hs hh hk
  have hg : 1 ≤ (↑(walls s):ℝ):= by exact_mod_cast hk
  change c* (1+(q:ℝ))^d*bill (a+x) s ≤ bill b s at hs
  have hz : (1+(q:ℝ)*↑(walls s))^d ≤ (1+q)^d*bill x s := by
    have hy : 1+(q:ℝ)*↑(walls s) ≤ (1+(q:ℝ))*↑(walls s) := by linarith only [hg]
    refine (pow_le_pow_left₀ (by positivity) hy d).trans ?_; rw [mul_pow]; gcongr
  have hp:= Real.exp_pos (boil s*a)
  apply le_trans _ hs; rw [← overlap]; apply le_trans (b:= c*((1+(q:ℝ))^d*bill x s)*bill a s)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left ..) hz (by positivity) (le_max_right ..)) hp.le
  exact le_of_eq (by ring)
lemma tilt_pow (p : BudgetPoint) (X : Keepat n) (m : ℕ) (h : X.val = halo (m*p.B) {0}) (hz : 8 ≤ p.B) (e : ℝ) (he : 0 ≤ e) :
    debt p.B e X.val ≤ Real.exp (e*((2*m+1:ℕ):ℝ)^ (4:ℕ))∧ debt p.B e (halo 8 X.val) ≤ Real.exp (e*((2*m+3:ℕ):ℝ)^ (4:ℕ)):= by
  rw [h]; constructor
  · apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_left _ he; exact_mod_cast (show coverNumber p.B (halo (n:=n) (m*p.B) {0}) ≤ (2*m+1)^4 from (by simpa only [two_mul] using tile (0:Site n) m p.B p.B_pos))
  apply Real.exp_le_exp.mpr; apply mul_le_mul_of_nonneg_left _ he
  have hu : halo 8 (halo (n:=n) (m*p.B) {0})⊆ halo ((m+1)*p.B) {0}:= by
    intro i hi; obtain ⟨j,hj,hp⟩:=halo_spec.mp hi; obtain ⟨a,ha,hv⟩:=halo_spec.mp hj;rw [Finset.mem_singleton] at ha; subst a
    exact halo_spec.mpr ⟨0,by simp,(separation_triangle 0 j i).trans (by rw [Nat.add_mul,one_mul];omega)⟩
  have hx:= (cover_mono hu p.B).trans (tile _ _ _ p.B_pos); exact_mod_cast (show coverNumber _ _ ≤ (2*m+3)^4 from hx.trans_eq (congr_arg (fun x:ℕ=> x^4) (by omega)))

-- Actual cost service D positive.

def garn (d : ℕ) (s : ℝ) := (d+8:ℝ)*boil s

def Rocket (t v x δ : ℝ) (d Q d' : ℕ) (a s : ℝ) (f : Stage) :=
  let u:= shipAmount s
  let y:=u
  let E:=garn d s
  1 ≤ s ∧ ∀ p q : BudgetPoint,p.B=M s→q.B=walls s → p.threshold=regular s → p.supportExponent=f.supportExponent → Lower p q →
    Nonempty (BudgetMix p q (Hat s ^ a) (bill t s) (v+2) E) ∧ scalesExp p q (2*(v+2)) ∧ ∀ n : Side, ∀ X : Keepat n,X.val=halo (Q*q.B) {0} →
      bill (-(d':ℝ) - 8) s *debt q.B v X.val + drain (M s) p q y v E ≤ bill (-(d:ℝ)) s ∧
        (2* bill x s+strand X.val (M s) p q y v E) + mech (forcing s) q y v E + batch (trib δ s) (v+1) q.B ≤ bill (-1) s ∧
        (((q.B+q.B+1)^4 : ℕ):ℝ)*bill (-1) s ≤1∧ Real.exp (bill (-1) s)-1≤1
where shipAmount (s : ℝ):=bill (-8) s

lemma expired (θ m : ℝ) (hp : 0<θ) : Fades (fun s: ℝ=> Real.exp (100000*m)*Real.exp (-(θ*M s)/2)*bill (-8) s):= by
  have h : Fades fun s : ℝ => Real.exp (-(θ*M s)/2):= by
    intro x; filter_upwards [receipt_contract (θ/2) (half_pos hp),monitors (-x) 1 zero_lt_one] with s hf hx
    rw [abs_of_pos (Real.exp_pos _),bill]; apply Real.exp_le_exp.mpr; linarith only [hf,hx]
  apply fad_le (fad_pay (either h (Real.exp (100000*m))) (g:=bill (-8)) (a:= -8) (Eventually.of_forall (fun s=> (abs_of_pos (show 0<bill (-8) s from Real.exp_pos _)).le)))
  filter_upwards with s; rw [mul_comm]
lemma rockets (a : Stage) (m d d' : ℕ) (f v x δ b : ℝ) (hx' : x < -1) (hδ : 0<δ) (hv : a.supportExponent≤v) (hf : f ≤0) (hb : 0≤ b) (hd : d+4 ≤ d') : ∀ᶠ s in atTop,
    Rocket f v x δ d m d' b s a:= by
  let θ:=a.supportExponent
  let c:ℝ:=-(d:ℝ); let c':ℝ:= -(d':ℝ)
  let α:ℝ:=Real.exp (v*((2*m+1:ℕ):ℝ)^ (4:ℕ)); let β:= Real.exp ((v+2)*((2*m+3:ℕ):ℝ)^ (4:ℕ));let T:=Real.exp (100000*(v+2)); let J:=min (-3) c-4
  have hr:= a.price_pos.trans_le hv
  have he₁ : c'-8<c:= by
    have hh:(d:ℝ)+4 ≤ d':= by exact_mod_cast hd
    dsimp only [c,c']; linarith only [hh]
  have ht : J ≤ -7:=by dsimp only [J]; linarith only [min_le_left (-3:ℝ) c]
  have ht' : J < c:= by dsimp only [J]; linarith only [min_le_right (-3:ℝ) c]
  filter_upwards [warrant v ((d:ℝ)+8) f b a hv hb (by positivity) hf,
     expired a.supportExponent (v+2) a.price_pos J,
     -- Rship
     absorb (c'-8) c he₁ (3*α), absorb (c-8) c (by linarith) 3, absorb J c ht' 3,
     -- Boat
     wind_pay, absorb (-8+1) (-1) (by norm_num) (8*3*β), absorb (c-8+1) (-1) (by dsimp [c]; linarith) 16,
     absorb (J+1) (-1) (by linarith only [ht]) 8, absorb x (-1) hx' 16, absorb (-8+1) (-1) (by norm_num) (8*T),
     (era δ (v+1) hδ) (-2),fired v (-2), absorb (-2) (-1) (by norm_num) 16,
     (bill_hi (a:= -1) (by norm_num)).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/2)), planet 2 4 (-1) 0 (by norm_num) 1, eventually_ge_atTop (1:ℝ)]
    with s h hp hm hQ hK hV hW hL hk hy hD ht₀ ht₁ hS hx hρ hG
  let y:= bill (-8) s
  let u:= bill (-1) s
  have hf' (x):0≤bill x s:= (Real.exp_pos _).le
  have hu : Real.exp (-garn d s)=bill (c-8) s:= by unfold garn bill c; congr 1; ring
  refine ⟨hG,fun p q he₁ h₂ h₃ h₄ hB=>⟨(h _ _ he₁ h₂ h₄ hB).1,(h _ _ he₁ h₂ h₄ hB).2,fun n X hX=>?_⟩⟩
  let P:= drain (M s) p q y v (garn d s); have hp₁ := add_nonneg (Real.exp_pos (-garn d s)).le
      (show 0 ≤ Real.exp (100000*(v+2))*Real.exp (-(p.supportExponent*(M s))/2)*y from mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (hf' _)); change 0 ≤ P at hp₁
  have he:P≤ bill (c-8) s + bill J s := by unfold P drain; rw [hu,h₄]; exact add_le_add_right ((le_abs_self _).trans hp) _
  have hh:debt q.B v X.val ≤ α:= (tilt_pow q X m hX hB.size v hr.le).1
  have hβ:= (tilt_pow q X m hX hB.size _ (show 0≤v+2 by linarith only [hr])).2
  have hω : wilt q.B≤ bill 1 s:= h₂ ▸ (le_trans (le_abs_self _) hV)
  have hm': 0 ≤β:= (Real.exp_pos _).le
  have hζT := (le_trans (le_abs_self _) ht₁)
  have hζS:= (le_trans (le_abs_self _) ht₀)
  have htQ : strand X.val (M s) p q y v (garn d s) ≤ bill (-8+1) s*(3*β)+ bill (c-8+1) s+bill (J+1) s := by
    unfold strand debit; calc
      _ ≤ bill 1 s*(3*y*β)+bill 1 s*(bill (c-8) s+bill J s):= by
        have h : 0≤3*y := mul_nonneg (by norm_num) (hf' _)
        exact add_le_add (mul_le_mul hω (mul_le_mul_of_nonneg_left hβ h) (mul_nonneg h (Real.exp_pos _).le) (hf' _)) (mul_le_mul hω he hp₁ (hf' _))
      _ = _ := by unfold y; simp_rw [← overlap]; ring
  have hz : Real.sqrt (forcing s)≤1 := Real.sqrt_le_one.mpr (Real.exp_le_one_iff.mpr (by unfold bill; exact neg_nonpos.mpr (by positivity)))
  have hp' : mech (forcing s) q y v (garn d s) ≤ plane (forcing s) v + bill (-8+1) s*T+bill (c-8+1) s:= by
    apply add_le_add _ _
    · apply add_le_add_right
      refine le_trans ?_ (b:=bill 1 s*(T*y)) (le_of_eq ?_)
      · refine mul_le_mul hω (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) ?_ (hf' _)
        exact mul_le_of_le_one_right (hf' _) hz
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hf' _) (Real.sqrt_nonneg _))
      unfold y; rw [← overlap]; ring
    rw [show Real.exp (-garn d s)=_ from hu,mul_one, ← overlap]
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left hω (hf' _)
  refine ⟨?_,?_,?_,?_⟩
  · apply (add_le_add (mul_le_mul_of_nonneg_left hh (hf' _)) he).trans
    change bill (c'-8) s*α+ _≤_; linarith only [hm,hQ,hK]
  · change 2*bill x s+strand X.val (M s) p q y v (garn d s)+mech (forcing s) q y v (garn d s)+batch (trib δ s) (v+1) q.B ≤ _
    apply (add_le_add (add_le_add (add_le_add_right htQ _) hp') (h₂ ▸ hζS)).trans; linarith only [hW,hL,hk,hy,hD,hS,hζT, hf' (-1)]
  · rw [h₂]; push_cast; rw [show (walls s:ℝ)+walls s+1=1+2*(walls s:ℝ) by ring]; simpa [bill] using! hρ
  have ht : 0≤u:=hf' _; change _ ≤ (1:ℝ)/2 at hx
  change Real.exp u-1≤1; have he := Real.abs_exp_sub_one_le (x:=u) (by simpa only [abs_of_nonneg ht] using (le_trans hx (show (1:ℝ)/2 ≤ 1 by norm_num)))
  rw [abs_of_nonneg ht] at he; linarith only [hx,(abs_le.mp he).2]
end YM.Next.Rank.Paint
