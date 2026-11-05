import YM.Next.RANK.Joule

/-! # Uniform post-L forecasts including Epoch powers and final stencil costs
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}
private lemma uplift (a : ℝ) (h : 0<a) : Volt a torque := by
  refine (show Volt a hot from ?_).scale 3
  exact ⟨1,zero_le_one,(hotter a h).mono fun s hx=>by rw [one_mul, abs_of_pos (show 0<hot s from Real.exp_pos _)]; exact hx⟩

private lemma insignia (d : ℕ) : Volt (1/2) (fun s=>Common.priced (torque s) d):= by
  apply (Volt.lift (M:=d) (uplift (1/(2*(d+1))) (by positivity))).high
  rw [← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).2; linarith

private lemma pay651 (P : Purse) : ∀ᶠ s in atTop,∀ u ∈ Set.Icc (s/2) s,
    let H:=P.era; let a:=H.coast; let l:=Paint.trib a.a u; let y:= Perch.bill (-1) s
    Real.exp l* (Perch.gas a u)^2+ 2*Perch.bill (-2) s*rentQ a.Q (load H+1) ≤ y ∧
      ↑(walls u+walls u+1 :ℕ)^ (4:ℕ) * y ≤ 1 ∧ Real.exp y-1 ≤ 1 := by
  let H:=P.era; let a:=H.coast;let g:=a.a
  have hg := a.posA; let e:=load P.era+1
  let c:= rentQ a.Q e; let f:=2*c+1
  have he (u) : Perch.gas a u= Real.exp (-trib g u):=by rw [gas,trib]; unfold g; simp
  have hx u: Real.exp (trib g u)*(gas a u)^2=gas a u:= by rw [he,pow_two,← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  filter_upwards [big.eventually_ge_atTop 1, half.eventually_ge_atTop 1,
    force hg 2 0 (by norm_num) (by norm_num), Paint.absorb (-2) (-1) (by norm_num) f,
    ((Real.continuous_exp.continuousAt.tendsto.comp (bill_hi (a:=-1) (by norm_num))).eventually (ge_mem_nhds (show Real.exp 0 <2 by rw [Real.exp_zero];norm_num))),
    q_power 4 (1/2) (by norm_num), (bill_hi (a:=1/2+ -1) (by norm_num)).eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/81))] with s hB hs hf hv hZ hp h u hu
  intro H' a' l y
  have ht : gas a u ≤ bill (-2) s := by rw [he]; unfold Perch.bill trib; apply Real.exp_le_exp.mpr; linarith only [hf u hu]
  refine ⟨?_, ?_ , ?_⟩
  · apply le_trans _ hv; rw [hx]
    change gas a u+ 2*bill (-2) s*c≤ _; unfold f; linarith only [ht]
  · have hV:= wall_mono (le_trans hs hu.1) (le_trans hs (hu.1.trans hu.2)) hu.2
    have hq:(1:ℝ) ≤ (walls s:ℝ):= by exact_mod_cast hB
    have hh : (((walls u+walls u+1:ℕ):ℝ)) ≤ 3*(walls s:ℝ) := by
      have ht' : (↑(walls u):ℝ)≤ walls s:= by exact_mod_cast hV
      push_cast; linarith only [ht',hq]
    apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hh 4) (Real.exp_pos _).le).trans
    rw [mul_pow,mul_assoc]; let b:= bill (1/2) s
    have hx := (mul_le_mul_of_nonneg_right hp (show 0≤y from (Real.exp_pos _).le)).trans ((overlap (1/2) (-1) s).trans_le h)
    exact le_trans (mul_le_mul_of_nonneg_left hx (by norm_num : 0 ≤ (3:ℝ)^4)) (by norm_num)
  change Real.exp y≤2 at hZ; linarith

lemma funding (P : Purse) (h : P.budget) : ∀ᶠ s in atTop,Faring P s:= by
  let m:=2*P.taylor
  have hx := (((uplift (1/2) (by norm_num)).plus ((Volt.scalar 1).high (show (0:ℝ) ≤ 1/2 by norm_num))).met (show (1/2:ℝ)<1 by norm_num))
  have he : Volt (0:ℝ) (fun s=> P.L+ P.sends s):= Volt.plus (Volt.scalar _) ((Volt.pulse _).high (neg_nonpos.mpr P.positive))
  filter_upwards [surge.eventually_ge_atTop 1,hx, he.met zero_lt_one, (insignia m).met (show (1/2:ℝ)<1 by norm_num), ((insignia 1).scale P.L).met (show (1/2:ℝ)<1 by norm_num),
    half.eventually_ge_atTop (Real.exp 1), Paint.absorb (-6) (-4) (by norm_num) (4*rentQ P.era.coast.Q (load P.era)), pay651 P,P.gifts h] with s hf hb hm hz hy hT hL hp hh
  refine ⟨show 1 ≤ (torque s) by unfold torque; linarith only [hf], le_sub_iff_add_le.mpr hb,hz,hy,hm,fun u hi=>?_,(mul_assoc ..).symm.trans_le hL,hh,hp⟩
  exact mul_le_mul_of_nonneg_left (hot_mono (le_trans hT hi.1) hi.2) (by norm_num : 0 ≤ (3:ℝ))

-- volatility shift from logspan: k before coeff test
private theorem epoch4 (P : Purse) : ∀ᶠ s in atTop,∀ u∈Set.Icc (s/2) s,
    let B:=P.era.coast.Q*walls u;6*G.colorScale*(4*(B:ℝ))^2*Paint.phase u*torque u ≤ P.sends s:= by
  let g:=G.colorScale; let Q := P.era.coast.Q; let f(u : ℝ):= walls u
  let Z(u:ℝ):= phase u * torque u
  let a:=P.foil; let F u:= 6*g*(4*((Q*f u:ℕ):ℝ))^2*Paint.phase u * torque u
  have he : Fades phase:= by
    rw [show phase=fun s=> hot s*Vac.Numbers.Hat s from funext fun i=> mul_comm ..]
    exact fad_pay Paint.cooling (a:=1) ((hotter 1 zero_lt_one).mono fun i hi=> (abs_of_pos (Real.exp_pos _)).trans_le hi)
  have ht : Fades F:= by
    have hh : Fades Z:= by
      have hx := fad_pay he (a:=1) (g:=torque) ?_
      · rw [show Z=(fun i=>torque i*Paint.phase i) by ext; unfold Z; ring]; exact hx
      filter_upwards [(uplift (1/2) (by norm_num)).met (b:=1) (by norm_num)] with s hs using (abs_of_pos (show 0<torque s from mul_pos (by norm_num) (Real.exp_pos _))).trans_le hs
    let v:= (6*g*(4*Q)^2)
    have hp:Fades (fun u=> v*((↑(walls u):ℝ)^2*Z u)):= either (fad_pay hh (a:=1) (g:=fun s=> (↑(walls s):ℝ)^2) (by filter_upwards [q_power 2 1 zero_lt_one] with s hs using (abs_of_nonneg (sq_nonneg _)).trans_le hs)) v
    convert hp using 1; ext; unfold F f v Z; push_cast; ring
  obtain ⟨u₀,hu₀⟩:= eventually_atTop.mp (ht (-4*a))
  filter_upwards [half.eventually_ge_atTop u₀,(y_rate.comp half).eventually_ge_atTop 1, logspan,y_rate.eventually_ge_atTop 1, half.eventually_gt_atTop 1] with s hh hx hs hz hE u hu
  intro B; let z:=y (s/2)
  have he:1≤z:=hx; have hv:1<s/2:=hE
  have hp : boil s≤4*boil u:= by
    have h : z≤y u:= Real.log_le_log (Real.log_pos hv) (Real.log_le_log (by linarith) hu.1)
    unfold boil; change y s ≤ z+1 at hs; nlinarith
  refine le_trans (le_trans (le_abs_self (F u)) (hu₀ u (le_trans hh hu.1))) (Real.exp_le_exp.mpr ?_); linarith only [mul_le_mul_of_nonneg_left hp P.positive]

lemma awakens (m : ℕ) (P : Purse) (h : P.budget) : ∀ᶠ s in atTop, Awakening (G:=G) P s m:= by
  let a:= Glimmer.fuel P.taylor m/4
  have hp : 0<a:= div_pos (Glimmer.fuel_real ..) (by norm_num)
  let Q:=P.era.coast.Q
  have he:Volt (a/4) (fun v => (walls v:ℝ)):= by
    refine ⟨1,zero_le_one,(q_power 1 (a/4) (by positivity)).mono ?_⟩; intro i h; rw [one_mul,abs_of_nonneg (show 0 ≤ (walls i:ℝ) by positivity)]; simpa using h
  have ht:Volt (a/2) (fun s=> (16*Q*(walls s:ℝ))*torque s):= by
    refine ((he.scale (16*Q)).times (uplift (a/4) (by positivity))).high ?_; linarith only
  filter_upwards [epoch4 P (G:=G),Perch.half.eventually_ge_atTop (Real.exp 1), ht.met (show a/2<a by linarith),P.deputed h] with s hQ hE hx hp
  refine ⟨fun u hu=> le_trans ?_ (hx.trans_eq (show bill a s=fraction m P.taylor s from rfl)), ?_,hQ,hp⟩
  · change _ ≤ 16*(Q:ℝ)*_ *_; have he':0 < torque u:= mul_pos (by positivity) (Real.exp_pos _); have hv:= hot_mono (le_trans hE hu.1) hu.2
    push_cast; change _ ≤ 16*Q*(walls s:ℝ)*_
    have hf:1 ≤ u:= le_trans (le_trans (Real.one_le_exp (by norm_num : 0 ≤ (1:ℝ))) hE) hu.1
    apply mul_le_mul _ (mul_le_mul_of_nonneg_left hv (by positivity : (0:ℝ) ≤ 3)) he'.le (by positivity)
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast wall_mono hf (hf.trans hu.2) hu.2) (by positivity)
  apply Glimmer.billed; unfold Glimmer.fuel; push_cast;apply (div_le_iff₀ (by norm_num : 0<(4:ℝ))).mpr;apply (div_le_iff₀ (by positivity)).mpr;nlinarith [Nat.cast_nonneg (α:=ℝ) P.taylor, Nat.cast_nonneg (α:=ℝ) m]
end YM.Next.Rank.Tapes
