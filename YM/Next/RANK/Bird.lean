import YM.Next.RANK.DockBudget
import YM.Next.RANK.Reign


/-!
# Explicit middle coupling requests

Regular tolerance originally on first-stage mask itself, not on a conditional
integral with that mask or on a continuum field. Change data only after proof
with these supports. Prove its purely numeric costs are possible *uniformly in
period and stand*. No such conclusion about any real W/correction/vac step gate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Perch
open Lattice Wilson RG Value Dock EntryWord Camp  Set Asymptotics Real Filter
open scoped Topology BigOperators Classical

-- b (station comparison) chosen separately. U,V may depend b,m, initial
-- calibration etc. Larger V requires larger single-cell error gain input.
structure Demand where
  Q : ℕ
  e : ℝ
  base : 0 ≤ e
  U : ℝ
  V : ℝ
  posU : 0 ≤ U
  posV : 0 ≤ V
  /-- rate fixed after L -/
  a : ℝ
  posA : 0 < a

-- width ends of receipt, use A actual couple at budget
variable (c : Demand)
def gas (u : ℝ) := Real.exp (-c.a * hot u ^ 2)

/-- Smallness conditions that can in fact be paid by scheduling AFTER all these
constants set. `u` current level hatBeta, not tied to the period in any tests. -/
structure Shelf (m : ℕ) (s u : ℝ) : Prop where
  span : 8 ≤ walls u
  space : walls u^2+2*(c.Q*walls u) ≤ M s^10
  local_pack : 64*((m:ℝ)*(c.U*boil s)+boil s) ≤ 1*(walls u:ℝ)
  force_pack : 64*((m:ℝ)*(c.U*boil s)+4*boil s * ((2^m:ℕ):ℝ)) ≤ 1*(walls u:ℝ)
  weather : ((2^m:ℕ):ℝ)*bill (-25/32) s+(Real.exp (-boil s)*1 + Real.exp (m*(c.V*boil s))*bill (-((m:ℝ)*c.V)-2) s) ≤ bill (-3/4) s
  cash : Real.exp ((m:ℝ)*(c.U*boil s)+ 4*boil s*((2^m:ℕ):ℝ)+2*join u)*gas c u+((2^m:ℕ):ℝ)*(bill 1 s*Real.exp (-(4*boil s))) ≤ bill (-1) s
  fits : ((walls u+walls u+1:ℕ):ℝ)^4*bill (-1) s ≤ 1
  wakes : Real.exp (c.e*((c.Q+c.Q+1:ℕ)^4:ℝ))*bill (1/8) s *bill (-31/32) s ≤ bill (-25/32) s
  tree : Real.exp ((c.e+1)*((c.Q+c.Q+1:ℕ)^4:ℝ))*bill (1/8) s*bill (1/4) s ≤ bill 1 s
  reserve : Real.exp (-(2*join u))*(Real.exp (bill (-1) s)-1) ≤ bill (-3/4) s*w u

-- four primitive feasibility calculations

private lemma beats {a b : ℝ} (h : a<b) (c : ℝ) : ∀ᶠ s : ℝ in atTop,c*bill a s ≤ bill b s := by
  have ht := (bill_hi (show a-b<0 by linarith)).const_mul c
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (ge_mem_nhds zero_lt_one)] with s hs
  change c*bill (a-b) s ≤ 1 at hs
  nth_rw 1 [show a=a-b+b by ring, ← overlap, ← mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (show 0 ≤ bill b s from (Real.exp_pos _).le)

private lemma together {a b d : ℝ} (h : a<b) (h' : d<b) (c f : ℝ) : ∀ᶠ s in atTop,c*bill a s + f*bill d s ≤ bill b s := by
  filter_upwards [beats h (2*c),beats h' (2*f)] with s hs hv
  linarith only [hs,hv]

-- pay stretch K v hurt against cold; $w$ ratio also any pair stretch

lemma force {a : ℝ} (ha : 0<a) (D E : ℝ) (he : 0≤E) (hd : 0≤D) : ∀ᶠ s in atTop,
    ∀ u ∈ Icc (s/2) s, D*boil s+E*join s ≤ a*hot u ^2 := by
  filter_upwards [rate_fire 1 zero_lt_one,fire_stretch,
    (surge.comp half).eventually_ge_atTop ((D+E)/a), half.eventually_ge_atTop (Real.exp 1)] with s hb hf ht hp u hu
  let v := s/2; have hx : Real.exp 1 ≤ v := hp
  have hu' : hot v ≤ hot u := hot_mono hx hu.1
  have hl := join_mono hx (hu.1.trans hu.2); rw [one_mul] at hb
  change (D+E)/a ≤ hot v at ht; have hy : 0 < hot u := Real.exp_pos _
  have h₁ := mul_le_mul_of_nonneg_left (hb.trans (hl.trans (hf.trans hu'))) hd
  have h₂ := mul_le_mul_of_nonneg_left (hf.trans hu') he
  have hg := (div_le_iff₀ ha).1 (ht.trans hu'); linarith only [mul_le_mul_of_nonneg_left hg hy.le,h₁,h₂]

private theorem reassemble (m : ℕ) : ∀ᶠ s in atTop,∀ u∈ Icc (s/2) s,
    Real.exp ((m:ℝ)*(c.U*boil s)+4*boil s*((2^m:ℕ):ℝ)+2*join u)*gas c u ≤ bill (-2) s := by
  let D := (m:ℝ)*c.U+4*((2^m:ℕ):ℝ)+2
  have hp := c.posU
  have he := force c.posA D 2 (by norm_num) (by dsimp only [D]; positivity)
  filter_upwards [he, half.eventually_ge_atTop (Real.exp 1)] with s hs hx u hu
  have hb := hs u hu
  have hV := join_mono ((show Real.exp 1 ≤ s/2 from hx).trans hu.1) hu.2
  unfold gas bill; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; dsimp only [D] at hb; linarith only [hb,hV]

private theorem holed : ∀ᶠ s in atTop, ∀ u∈ Icc (s/2) s,
    Real.exp (-(2*join u))*(Real.exp (bill (-1) s)-1) ≤ bill (-3/4) s*w u := by
  filter_upwards [rate_fire 1 (by norm_num),half.eventually_ge_atTop (Real.exp 1),(up.comp half).eventually_ge_atTop 10] with s hs hh ht u hu
  let p := bill (-1) s; have hp : p ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (boil_pos s) (by norm_num))
  have hv : Real.exp p-1 ≤ Real.exp 1 := le_trans (sub_le_self _ zero_le_one) (Real.exp_le_exp.mpr hp)
  apply (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans
  have hy := join_mono (show Real.exp 1 ≤ s/2 from hh) hu.1
  have he : 10 ≤ join u := le_trans ht hy
  rw [← Real.exp_add,w,bill,← Real.exp_add]; apply Real.exp_le_exp.mpr
  linarith only [hs,hy,he]

private theorem sunny (m : ℕ) : ∀ᶠ s in atTop,
    ((2^m:ℕ):ℝ)*bill (-25/32) s+(Real.exp (-boil s)*1+Real.exp (m*(c.V*boil s))*bill (-((m:ℝ)*c.V)-2) s) ≤ bill (-3/4) s := by
  have ht (s) : Real.exp (m*(c.V*boil s))*bill (-((m:ℝ)*c.V)-2) s=bill (-2) s := by unfold bill; rw [← Real.exp_add]; congr 1; ring
  simp_rw [ht,mul_one]
  filter_upwards [together (a:=-25/32) (b:=-3/4) (by norm_num) (d:=-1) (by norm_num) ((2^m:ℕ):ℝ) 2] with s hs
  have he : bill (-1) s = Real.exp (-boil s) := by simp [bill]
  have hh : bill (-2) s ≤ bill (-1) s := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by norm_num) (boil_pos s))
  rw [← he]; linarith only [hs,hh]

private lemma fits : ∀ᶠ s in atTop,∀ u∈Icc (s/2) s, ((walls u + walls u + 1 : ℕ):ℝ)^4 * bill (-1) s ≤ 1 := by
  filter_upwards [half.eventually_ge_atTop 1,big.eventually_ge_atTop 1,rate_wall (a:=1/2) (by norm_num) 4,
    boil_rate.eventually_ge_atTop (10*Real.log 3)] with s hs hv hl ht u hu
  have hh : walls u ≤ walls s := wall_mono (le_trans hs hu.1) ((le_trans hs (hu.1.trans hu.2))) hu.2
  let z := Real.log ((walls s):ℝ)
  have hp : 1 ≤ ((walls s):ℝ) := by exact_mod_cast hv
  have he : ((walls u + walls u + 1 : ℕ) : ℝ) ≤ 3*((walls s):ℝ) := by
    have hf : (↑(walls u):ℝ) ≤ walls s := Nat.cast_le.mpr hh; push_cast; linarith only [hf,hp]
  refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) he 4) (show 0 ≤ bill (-1) s from (Real.exp_pos _).le)).trans ?_
  have hw : 3*((walls s):ℝ)=Real.exp (Real.log 3+z) := by rw [Real.exp_add,Real.exp_log (by norm_num),show Real.exp z=((walls s):ℝ) from Real.exp_log (by positivity)]
  unfold bill; rw [hw, ← Real.exp_nat_mul,← Real.exp_add,Real.exp_le_one_iff]; push_cast; dsimp only [z]; linarith only [hl,ht,Real.log_pos (show 1<(3:ℝ) by norm_num)]

private lemma estate (Q : ℕ) : ∀ᶠ s in atTop,∀ u∈Icc (s/2) s,walls u^2+2*(Q*walls u) ≤ M s^10 := by
  filter_upwards [half.eventually_ge_atTop 1,many.eventually_ge_atTop (max 2 Q)] with s hs hm u hu
  have hV := wall_mono (le_trans hs hu.1) (le_trans hs (hu.1.trans hu.2)) hu.2
  let a := M s; change max 2 Q ≤ a at hm
  have ha : 2≤a := (le_max_left ..).trans hm
  have hq : Q≤a := (le_max_right ..).trans hm
  change walls u ≤ a^2 at hV
  have he : a^3 * 2 ≤ a^4 := by rw [pow_succ a 3]; gcongr
  have hh : 2 ≤ a^6 := ha.trans (by simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ a by omega) (by norm_num : 1 ≤ 6))
  calc
    _ ≤ (a^2)^2+2*(a*a^2) := by gcongr
    _ ≤ 2*a^4 := by linarith only [he]
    _ ≤ a^4*a^6 := by rw [mul_comm 2]; gcongr
    _ = _ := by dsimp [a]; ring

private lemma rebuild (P : ℝ) (hp : 0 ≤ P) : ∀ᶠ s in atTop,∀ u∈Icc (s/2) s, P * boil s ≤ (walls u:ℝ) := by
  filter_upwards [half.eventually_ge_atTop 1, rate_inverse (1/(P+1)) (by positivity)] with s hs hf u hu
  apply le_trans _ (Nat.cast_le.mpr (wall_mono (show 1 ≤ s/2 from hs) (le_trans hs hu.1) hu.1))
  rw [div_mul_eq_mul_div, one_mul,le_div_iff₀ (by linarith)] at hf; linarith only [hf,boil_pos s]

/-- constant equalities for W tests -/
private lemma awake (A : ℝ) : ∀ᶠ s in atTop,A*bill (1/8) s * bill (-31/32) s≤bill (-25/32) s := by simp_rw [mul_assoc,overlap]; exact beats (by norm_num) A
private lemma brisk (A : ℝ) : ∀ᶠ s in atTop,A*bill (1/8) s * bill (1/4) s≤bill 1 s := by simp_rw [mul_assoc,overlap]; exact beats (by norm_num) A

theorem mint (m : ℕ) : ∀ᶠ s in atTop,∀ u∈Icc (s/2) s, Shelf c m s u := by
  let A := (c.Q+c.Q+1:ℕ)
  let k : ℝ := (↑(2^m:ℕ):ℝ)
  have hc := c.posU
  filter_upwards [half.eventually_ge_atTop 1,(big.comp half).eventually_ge_atTop 8,estate c.Q, rebuild (64*((m:ℝ)*c.U+1)) (by positivity),
    rebuild (64*(m*c.U+4*k)) (by dsimp only [k]; positivity), sunny c m, reassemble c m, together (a:=-2) (b:=-1) (by norm_num) (d:=-3) (by norm_num) 1 k,
    fits, holed, awake (Real.exp (c.e*(A:ℝ)^4)),brisk (Real.exp ((c.e+1)*(A:ℝ)^4))] with s h1 h2 h3 h4 h5 h6 h7 h8 h9 ha hb hc u hu
  have h : walls (s/2) ≤ walls u := wall_mono h1 (le_trans h1 hu.1) hu.1
  refine ⟨le_trans h2 h,h3 _ hu,?_,?_,h6,?_,h9 _ hu,hb,hc,ha _ hu⟩
  · linarith only [h4 u hu]
  · change 64*(_ + _ * k) ≤ _; linarith only [h5 u hu]
  have hz := h7 u hu
  have he : bill 1 s * Real.exp (-(4*boil s))=bill (-3) s := by unfold bill; rw [← Real.exp_add]; congr 1; ring
  rw [he]; dsimp only [k] at h8; linarith only [hz,h8]
end YM.Next.Rank.Perch
