import YM.Next.FREE_KERNELS.Docked
import YM.Next.FREE_KERNELS.Wire

/-!
# Per-alias dual costs on the complex cube
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate
variable {ι : Type*} {j t : ℕ}
namespace Flight
variable (k : ℝ) (hk : 0<k) (hj : 4 ≤ j) (ht : 4 ≤ t)
    (F : ι → Flight j t) (l : ∀ i, Site (F i).L)

lemma latch_budget (r : ℕ) : Pay (fun _ : ι => 1) fun i p => latch (F i) p r := by
  have he := bills F (fun _ => 0); simp only [decay_zero] at he
  have hh := he.inv (bills_firm F) fun _ => one_pos
  have hx (a : Axis) : Moderate (fun _ : ι => 1) fun i p => (rail (F i).L ((F i).toe p a))⁻¹ := by
    have hu := rails F (fun _ => 0) fun _ => a
    simp_rw [alias_zero_eq] at hu
    have hp := hu.inv (rail_root _ _) (fun _ => one_pos)
    unfold toe; simpa only [alias_zero_eq,inv_one] using hp
  unfold latch; simpa only [one_pow,mul_one, inv_one, toe] using (Pay.expose_mask r hx).scale hh

include ht
lemma mouth_budget : Pay (fun _ : ι => 1) fun i p => mouth k (F i) p := by
  let v := fun i => (F i).land
  have hh (a : Axis) := Train.bulb_budget k ht v (fun _ => a)
  have hx := Pay.expose_mask 1 hh; simp only [one_pow] at hx; exact hx

include hj hk
lemma foot_budget : Moderate (fun _ : ι => 1) fun i p => footY k (F i) p := by
  have he := (bills F (fun _ => 0)).mul (back_bills F fun _ => 0)
  let v i := (F i).wing
  have hh := Train.bend_budget k hk ht (fun i => (F i).land)
  have hu := ((Train.bend_budget k hk hj v).inv (Train.bend_firm k hk hj v) fun _ => one_pos).on_alias _ (fun i => (F i).odd) (fun _ => 0)
  unfold footY; simpa only [v,yen,decay_zero,toe,inv_one,mul_one,div_eq_mul_inv] using (he.mul hh).mul hu
lemma brace_budget : Pay (fun _ : ι => 1) fun i p => brace k (F i) p := by
  let v i := (F i).land
  let G i p a := tailings k (F i) p a / ((v i).bulb k p a)
  have he (a : Axis) : Moderate (fun _ : ι => 1) fun i p => G i p a := by
    have hh := (Train.bulb_budget k ht v (fun _ => a)).inv (Train.bulb_firm _ hk v _) fun _ => one_pos
    unfold G; simpa only [div_eq_mul_inv,inv_one,mul_one] using (tail_budget k hj F a).mul hh
  have hh := (Pay.expose_mask 2 he).scale (divisor_control fun i => (F i).land.mass); simp only [one_pow,mul_one] at hh
  have hu : Pay (fun _ : ι => 1) fun i p => twice (G i p) := by
    apply Pay.diag; swap; exact fun _ => zero_le_one
    intro i; exact Moderate.sum _ _ (fun _ => zero_le_one) (fun a _ => he a)
  have hp := (heart_budget k hk hj fun i => (F i).wing).1.on_alias _ (fun i => (F i).odd) fun _ => 0
  unfold brace; simpa only [v,G,span,mul_one] using hp.times (hu.sub hh)
lemma copper_budget : Pay (fun _ : ι => 1) fun i p => copper k (F i) p := by
  have hd := flux_budget F 2 (fun _ => 0); simp only [decay_zero] at hd
  have he := hd.scale (foot_budget k hk hj ht F)
  have hs := (latch_budget F 2).times (out_budget (ι:=ι) 1)
  have hu := ((brace_budget k hk hj ht F).times hs).times (mouth_budget k ht F)
  have hz := Pay.expose_mask 1 (tail_budget k hj F)
  have hH := (heart_budget k hk hj fun i => (F i).wing).1.on_alias _ (fun i => (F i).odd) fun _ => 0
  have hy := (hH.times hs).times hz
  simp only [mul_one,one_pow] at he hu hy
  have ho := (hu.sub hy).times (out_budget (ι:=ι) 1).reverse.transpose; simp only [mul_one] at ho
  exact he.add ho

omit hj in
lemma notch_budget : Pay (fun _ : ι => 1) fun i p => notch k (F i) p := by
  have h := divisor_control fun i => (F i).land.mass
  have he := Pay.scale (Pay.const (α:=TypeFace 2) (β:=TypeFace 2) 1) (h.pow 2)
  have hq := out_budget (ι:=ι) 1
  have hp := (heart_budget k hk ht (fun i => (F i).land)).1
  have hm := (((hp.times hq).times (mouth_budget k ht F)).times hq.reverse.transpose).scale h
  simp only [mul_one,one_pow] at h hm he
  exact he.sub hm
lemma levy_budget (hi : ∀ i, l i≠0) : Moderate (fun _ : ι => 1) fun i p => levy k (F i) p (l i) := by
  have he := ((bills F l).mul (back_bills F l)).mul (Train.bend_budget _ hk ht fun i => (F i).land)
  have hb := he.mul (portR_budget k hk hj F l hi)
  have hu (i : ι) := grade_ge (l i)
  have hh := hb.raise_price (u:=fun _ => 1) (by
    intro i; dsimp only; rw [mul_one];
    have ht := decay_le_one (l i) j
    have he := decay_pos (l i) j
    refine (mul_le_of_le_one_right (mul_pos he he).le (inv_le_one_of_one_le₀ ?_)).trans ?_
    · exact one_le_pow₀ (one_le_pow₀ (hu i))
    exact (mul_le_of_le_one_right he.le ht).trans ht)
  simpa only [levy,yen,div_eq_mul_inv] using hh
lemma stake_budget (hi : ∀ i, l i≠0) : Pay (fun i => decay j (l i)) fun i p => stake k (F i) p (l i) := by
  have hv := (heart_budget k hk hj fun i => (F i).wing).1.on_alias _ (fun i => (F i).odd) l
  have hm := Pay.expose_mask 1 (fun a => portD_budget k hj F l hi (fun _ => a))
  have hd := sig_budget F l 1
  have hb := ((((hv.times hd).times hm).times (flux_budget F 1 l)).times (out_budget (ι:=ι) 1).reverse.transpose)
  have hy := ((flux_budget F 2 l).times (notch_budget k hk ht F)).scale (levy_budget k hk hj ht F l hi)
  simp only [mul_one,one_mul,pow_one] at hb hy
  unfold stake; refine Pay.add (hb.raise ?_) hy
  intro i
  apply mul_le_of_le_one_left (decay_pos ..).le
  have he := grade_ge (l i)
  rw [← div_eq_mul_inv,div_le_one (pow_pos (grade_pos (l i)) _)]; nlinarith
lemma wire_budget : Pay (fun i => decay j (l i)) fun i p => wire k (F i) p (l i) := by
  apply Pay.branches (fun i => l i=0) (fun i => (decay_pos ..).le)
  · have hh (i : {i // l i=0}) : l i.val=0 := i.property
    simp only [wire, hh, if_true,decay_zero]
    exact copper_budget k hk hj ht (fun i : {i // l i=0} => F i.val)
  have hh (i : {i // ¬ l i=0}) : ¬ l i.val=0 := i.property
  simp only [wire,hh,if_false]; exact stake_budget k hk hj ht (fun i : {i // ¬ l i=0} => F i.val) _ hh
end Flight
end YM.Next.Free
