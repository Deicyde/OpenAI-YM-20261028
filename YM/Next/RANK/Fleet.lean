import YM.Next.RANK.NoSpill
import YM.Next.RANK.Rifle
import YM.Next.RANK.Spirals


/-!
# Post-L costs at the k restart
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Paint
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

def delta (s : ℝ):= Hat s ^ ((11 : ℝ)/5)
def forcing (s : ℝ):= Real.exp (-(bill 1 s ^ (1/5 : ℝ)))

def invasion (a : Stage) (e θ s β : ℝ) : ℝ :=
    wilt (walls s) * (β*outTail a.width a.paths (walls s) +
      2*sourceCharge 2 (e+2) (2*bill 1 s^θ) (regular s) + β * (2*sourceCharge 3 (e+2) a.paths (regular s) +2*sourceCharge 4 (e+2) a.paths (regular s)) + Real.exp (100000*(e+2))*delta s)

lemma salary (a : Stage) {e θ s : ℝ} {p q : BudgetPoint} (h : q.B=walls s) (H : p.threshold=regular s) (b : ℝ) :
    vacancies e (2*bill 1 s^θ) a.width a.paths (delta s) b p q=invasion a e θ s b := by
  unfold vacancies breath invasion water; rw [H,h]; ring
lemma mon (a : Stage) {e θ s : ℝ} {p q : ℝ} (h : p ≤ q) (hp : 0<s) (hx : θ ≤ 1) : invasion a e θ s p ≤ invasion a e 1 s q:= by
  unfold invasion sourceCharge
  have ht:0≤ regular s:= by rw [regulog _ hp]; positivity
  have hr:0≤ a.paths := a.paths_pos.le
  have he : 0≤ outTail a.width a.paths (walls s) := by unfold outTail; positivity
  apply mul_le_mul_of_nonneg_left _ (wilty _); gcongr
  · exact Real.one_le_exp (mul_nonneg (boil_pos s) zero_le_one)

lemma fades_inv (a : Stage) (e : ℝ) : Fades (fun s : ℝ=> invasion a e 1 s (2*s)) := by
  unfold invasion; apply fad_pay _ wind_pay; refine fad_add (fad_add (fad_add ?_ ?_) ?_) (either (timeLoan (11/5) (by norm_num)) _)
  · have h := a.width_pos
    let X:ℝ:= Fintype.card PlaqAxes; let c : ℝ:= 4*X*a.paths^2
    have H:=either (tail_fades (a.width/4) (by positivity)) c
    refine fad_le H (Eventually.of_forall fun v=> (congr_arg (fun x:ℝ=>|x|) ?_).le)
    unfold outTail; simp only [neg_div]; unfold c X; ring
  · have h : Fades (fun s=> bill 1 s* regular s) := fad_pay tooCool (a:=1) (Eventually.of_forall fun v=> (abs_of_pos (show 0<bill 1 v from Real.exp_pos _)).le)
    let c:ℝ:=4*Real.exp (200000*(e+2)*(2+2))
    refine fad_le (either h c) ?_; filter_upwards [tooCool 0,eventually_gt_atTop (0:ℝ)] with v he hv
    have ht:= regular v; have hp' : 0≤ regular v := by rw [regulog _ hv]; positivity
    have h : |regular v| ≤ 1 := by simpa [bill] using he
    have hL : regular v^2 ≤ regular v:= (pow_succ (regular v) 1).trans_le (by rw [pow_one]; exact mul_le_of_le_one_right hp' (le_trans (le_abs_self _) h))
    have hc : 0<bill 1 v:= Real.exp_pos _
    dsimp only [c]; rw [abs_of_nonneg (by unfold sourceCharge; positivity),abs_of_nonneg (by positivity)]; unfold sourceCharge; rw [Real.rpow_one]; norm_cast
    push_cast; nlinarith only [mul_le_mul_of_nonneg_left hL (mul_nonneg (Real.exp_pos (200000*(e+2)*4)).le hc.le)]
  · let C:= a.paths
    let f (n : ℕ) : ℝ:= 4*a.paths*Real.exp (200000*(e+2)*(n+2))
    have ht:=fad_add (either (faded_three 3 (by norm_num)) (f 3)) (either (faded_three 4 (by norm_num)) (f 4))
    apply fad_le ht; filter_upwards with s; apply le_of_eq; congr 1; dsimp only [f]; unfold sourceCharge; ring

lemma fit_vac (a : Stage) (e u : ℝ) : ∀ᶠ s in atTop,∀ (p q : BudgetPoint),p.threshold=regular s→q.B=walls s → ∀ θ : ℝ, θ ≤ 1 → ∀ β : ℝ,β ≤ 2*s → vacancies e (2*bill 1 s^θ) a.width a.paths (delta s) β p q ≤ bill u s:= by
  filter_upwards [eventually_gt_atTop 0,fades_inv a e u] with s hp hv p q hg hq θ h β hx
  rw [salary a hq hg]; exact (mon a hx hp h).trans ((le_abs_self _).trans hv)

-- birth gain from hot, doesn't even require contour shape

def trib (a s : ℝ):= a*(hot s)^2
lemma torrid (a : ℝ) (ha : 0<a) : Fades (fun s=>Real.exp (-trib a s)):= by
  intro x; filter_upwards [Perch.force ha (max 0 (-x)) 0 (by norm_num) (le_max_left ..),eventually_gt_atTop 0] with s h hs
  have hx:= h s (Set.mem_Icc.mpr ⟨by linarith,le_rfl⟩); rw [abs_of_pos (Real.exp_pos _),bill]; apply Real.exp_le_exp.mpr; unfold trib; linarith only [hx,mul_le_mul_of_nonneg_right (le_max_right 0 (-x)) (boil_pos s)]
lemma era (a e : ℝ) (ha : 0<a) : Fades (fun s=>batch (trib a s) e (walls s)):= by
  let C:= Real.exp (e*(9^4:ℕ));let d:ℝ:=9^4*C
  have h:= fad_pay (torrid a ha) (a:=1) (g:=fun s : ℝ=> (↑(walls s):ℝ)^4) (by filter_upwards [q_power 4 1 zero_lt_one] with s hs; rwa [abs_of_nonneg (by positivity)])
  apply fad_le (either h d)
  filter_upwards [big.eventually_ge_atTop 1] with s hs
  have ha' : (1:ℝ)≤ (↑(walls s):ℝ):= by exact_mod_cast hs
  have hp : ((((4*walls s+4*walls s+1)^4:ℕ):ℝ))≤ (9*(walls s:ℝ))^4:= by push_cast; gcongr; linarith only [ha']
  dsimp only [batch,d,C]; rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) (Real.exp_pos _).le).trans_eq; ring
lemma fired (e : ℝ) : Fades (fun s=> plane (forcing s) e):= by
  have h : Fades forcing := by
    intro x
    filter_upwards [((isLittleO_pow_exp_pos_mul_atTop 1 (by norm_num : (0:ℝ)<1/5)).const_mul_left x|>.comp_tendsto boil_rate).def zero_lt_one] with s hs
    change ‖x * (boil s)^1‖ ≤ _ at hs
    change _ ≤ 1*‖Real.exp (1/5 * boil s)‖ at hs
    rw [one_mul,Real.norm_of_nonneg (Real.exp_pos _).le,pow_one] at hs
    unfold forcing; rw [abs_of_pos (Real.exp_pos _),bill, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have he : -(x*boil s) ≤ _:= neg_le_abs (x*boil s); rw [mul_one, mul_comm (boil s) (1/5)]; linarith only [he,show |x*boil s| ≤ _ from hs]
  have ht:= either (either h (Real.exp (100000*(e+1)))) 83521; exact ht

lemma grows_scale (A : Stage) (e : ℝ) : ∀ᶠ s in atTop,2000000*(e+2)≤ A.width* (walls s:ℝ) ∧ 100000*(M s:ℝ)*(e+2) ≤ (walls s:ℝ)* A.supportExponent:= by
  have hs:=A.width_pos; have ht:=A.price_pos
  have h : Tendsto (fun s=> (M s:ℝ)*A.supportExponent) atTop atTop:= (tendsto_natCast_atTop_atTop.comp many).atTop_mul_const ht
  have he:Tendsto (fun s=>A.width*(walls s:ℝ)) atTop atTop:=(tendsto_natCast_atTop_atTop.comp big).const_mul_atTop hs
  filter_upwards [he.eventually_ge_atTop _,h.eventually_ge_atTop (100000*(e+2))] with s hp h; refine ⟨hp,?_⟩; unfold walls; push_cast; linarith only [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (α:=ℝ) (M s))]

lemma alpha_phase (s : ℝ) (h : 0<s) : 0<phase s := by unfold phase; rw [logged s h]; exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
lemma phaseFit : ∀ᶠ s in atTop,2*phase s ≤ regular s := by
  filter_upwards [Spindle.hotter (1/2) (by norm_num), absorb (1/2) 1 (by norm_num) 2, eventually_gt_atTop 0] with s hp hz hs
  unfold phase regular; rw [mul_left_comm 2]; apply mul_le_mul_of_nonneg_left
  · exact (mul_le_mul_of_nonneg_left hp (by norm_num)).trans hz
  rw [logged _ hs]; positivity
lemma stimulated (S : Stage) : ∀ᶠ s in atTop, Turnon S.clip (phase s) (walls s):= by
  let c:= S.clip.relaxation; have hp : 0<c:= S.clip.radius_pos
  filter_upwards [dipping c⁻¹ (by positivity),surge.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2*Real.log 2)] with s hs hf hv hk
  have h : 1 ≤ hot s := hf
  unfold Turnon phase; rw [logged _ (zero_lt_one.trans hv)]
  apply le_trans _ (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (Real.exp_pos _).le h) (Real.exp_pos _).le)
  nth_rw 1 [← Real.exp_log (by norm_num : 0<(2:ℝ)),← Real.exp_add]; apply Real.exp_le_exp.mpr
  rw [← div_eq_inv_mul] at hs; exact (by unfold c at hs; linarith only [hs,hk])

lemma landing (a : Stage) (u : ℝ) (hu : u ≤ a.clip.linear/20) : ∀ᶠ s in atTop, ∀ β : ℝ,s/2 ≤ β →
    2 * trib u s ≤ β*a.clip.linear/5* phase s ^ 2 := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hp b hb
  have hx : s * Hat s ^ 2=1 := by unfold Hat; rw [inv_pow,Real.sq_sqrt hp.le,mul_inv_cancel₀ hp.ne']
  unfold trib phase
  have hh:s/2*a.clip.linear/5*(Hat s*hot s)^2=a.clip.linear/10*hot s^2 := by
    rw [show s/2*a.clip.linear/5*(Hat s*hot s)^2= s* (Hat s)^2*(a.clip.linear/10*hot s^2) by ring,hx,one_mul]
  apply le_trans (b:=s/2 *a.clip.linear/5*(Hat s*hot s)^2)
  · rw [hh]; linarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg (hot s))]
  gcongr; exact a.clip.tail_pos.le
-- all charges need k, even though initial κ comparison is allowed at ANY plate.

def Winter (a : Stage) (v u s x : ℝ) :=
    0<s ∧ RegularField s ∧ 2*phase s≤regular s ∧ M s≤walls s ∧ 8≤walls s ∧ Turnon a.clip (phase s) (walls s) ∧
    ∀ θ : ℝ, θ ≤ 1 → ∀ p : BudgetPoint,p.B=M s → p.threshold=regular s → p.supportExponent=a.supportExponent →
      ∀ q : BudgetPoint,q.threshold=phase s→q.B=walls s →Lower p q → q.supportExponent = p.supportExponent →
        ∀ (β : ℝ), s/2 ≤ β → β ≤ 2*s → ∀ (n : Side) (P : PathData G) (A : Activities G n),
          let C:=2*bill 1 s^θ; let u':= trib u s
          Drama P A a.clip β (delta s) v (forcing s) a.width a.paths C p q u' ∧
            vacancies v C a.width a.paths (delta s) β p q ≤ bill x s ∧ plane (forcing s) v ≤ bill x s ∧ batch u' (v+1) q.B ≤ bill x s
where
  RegularField (s : ℝ):= regular s≤1

-- room in hit
lemma stage_fires (S : Stage) (v u x : ℝ) (hv : S.supportExponent≤v) (h : 0<u) (hu : u≤ S.clip.linear/20) : ∀ᶠ s in atTop, Winter (G:=G) S v u s x:= by
  let z:= min x (-2); let J:= fun s=>batch (trib u s) (v+1) (walls s); let Y:= fun s=> plane (forcing s) v
  have hf:=fit_vac S v z; have H:=fired v z
  have h₀ : z<0:= lt_of_le_of_lt (min_le_right ..) (by norm_num)
  have hk := bill_hi h₀
  have heq:z+1<0:= lt_of_le_of_lt (add_le_add_left (min_le_right ..) _) (by norm_num)
  filter_upwards [hf,H,(era u (v+1) h) z,hk.eventually (ge_mem_nhds (by norm_num : (0:ℝ)< (1/16:ℝ))),
    (bill_hi heq).eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/324)), grows_scale S v, landing S u hu,
    q_power 4 (1:ℝ) (by norm_num),phaseFit,stimulated S, tooCool 0,big.eventually_ge_atTop 8,many.eventually_ge_atTop 1,eventually_gt_atTop 0] with s hf h1 h2 hp hp' Hx hy hs ht hT hr hb hM hV
  refine ⟨hV,?_,ht,(show M s≤M s^2 from by simpa only [pow_one] using pow_le_pow_right₀ hM (by norm_num : 1≤2)),hb,hT,?_⟩
  · dsimp only [Winter.RegularField]; apply le_trans (le_abs_self _); exact hr.trans (by rw [bill,mul_zero,Real.exp_zero])
  intro θ hQ p hx hy' hk q h3 h4 h5 ha b h6 h7 n P A C U
  let X:= bill z s
  have h₈ : vacancies v C S.width S.paths (delta s) b p q≤ X := hf p q hy' h4 θ hQ b h7
  have h₉ : plane (forcing s) v ≤ X:=le_trans (le_abs_self _) h1
  have h₁ : batch U (v+1) q.B ≤ X:= by rw [h4]; exact le_trans (le_abs_self _) h2
  have hX : X ≤ bill x s := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_left ..) (boil_pos _))
  refine ⟨⟨?_,ha ▸ hk ▸ hv,h₈.trans (hp.trans (by norm_num)), h3.symm ▸ hy _ h6,mul_nonneg h.le (by positivity),?_⟩,h₈.trans hX,h₉.trans hX,h₁.trans hX⟩
  · refine ⟨h5, ?_, h4.symm ▸ Hx.1,h3.symm ▸ h4.symm ▸ hT⟩
    unfold scalesExp; rw [hx,h4,hk]; exact Hx.2
  rintro a rfl
  have ht' : 2* vacancies v C S.width S.paths (delta s) b p q+plane (forcing s) v+batch U (v+1) q.B ≤4*X:= by linarith only [h₈,h₉,h₁]
  refine ⟨by linarith only [ht',show X≤1/16 from hp],?_⟩
  apply (mul_le_mul_of_nonneg_left ht' (by positivity)).trans
  have hy:1≤walls s:= Nat.le_trans (by decide) hb
  rw [h4]; push_cast
  have he:↑(walls s)+(walls s:ℝ)+1 ≤ 3*(walls s:ℝ) := by linarith only [show (1:ℝ) ≤ ↑(walls s) by exact_mod_cast hy]
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he 4) (show 0 ≤ 4*X from mul_nonneg (by norm_num) (Real.exp_pos _).le)).trans
  rw [mul_pow]
  have hb : X * (walls s:ℝ)^4 ≤ 1/324 := (mul_le_mul_of_nonneg_left hs (show 0 ≤ X from (Real.exp_pos _).le)).trans ((overlap ..).trans_le hp')
  linarith only [hb]
end YM.Next.Rank.Paint
