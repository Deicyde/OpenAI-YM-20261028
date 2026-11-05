import YM.Next.RANK.Planck
import YM.Next.RANK.Rim
import YM.Next.RANK.Sky
import YM.Next.RANK.Tuning


/-!
# The vertex budget at the rounding scale

Origins use Street native number of axis steps. Show rates for spending tests
at radius ANY ζ>0 when using walls(k)^2 here as W_k maximal short stencil. It
is still small vs b fixed. This is a pre/post-L size to anticipate: E true
constants of leading kernels/Poly estimates must stay bought through these radii
(and not allowed after they are used).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Glimmer
open Lattice Wilson RG Supply Set Function Beamer Perch  CellsInt Maxwell Configuration Rise Normal Filter
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {n p d k v M : ℕ}

private lemma from_walk {w : ℕ} (f : Cover → ℝ) {c : ℝ} (h : 0 ≤ c)
    (hp : ∀ x, street x≤ w → ∀ i,‖stepValue f i x‖≤ c) (x : Cover) (hx : street x ≤ w) :
    ‖f x‖ ≤ ‖f 0‖+(w:ℝ)*c := by
  have hh (n : ℕ) (hn : n ≤ w) (i : Cover) (he : street i=n) : ‖f i‖ ≤ ‖f 0‖+n*c := by
    induction n generalizing i with
    | zero =>
      obtain h1|⟨s,h2,h3⟩ := strolling i
      · rw [h1]; simp
      omega
    | succ n H =>
      obtain h1|⟨s,h2,a,h3⟩ := strolling i
      · rw [h1]; apply le_add_of_nonneg_right; positivity
      have hs : street s=n := by omega
      have hz := H (by omega) _ hs
      have hv : ‖f i - f s‖≤ c := by
        rcases h3 with h|h
        · rw [h]; exact hp _ (by omega) a
        rw [norm_sub_rev,h]; exact hp i (he.trans_le hn) a
      apply le_trans (b:=‖f i-f s‖+‖f s‖) (by simpa only [sub_add_cancel] using norm_add_le (f i-f s) (f s)) ?_
      push_cast; linarith only [hv,hz]
  exact (hh _ hx x rfl).trans (add_le_add_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hx) h) _)

private lemma room (j : KeyIn G d) (a : PlaqAxes) (b : G.ColorIndex) :
    ∃ c : ℝ,0 ≤ c ∧ ∀ (M : ℕ) (z : Cover), street z ≤ M → ‖tester j.val (z,a,b)‖ ≤ c*(1+M:ℝ)^d := by
  let f (z : Cover) := tester j.val (z,a,b)
  let u := j.val.1
  have hh (i) (hp : i≤u+1) : ∀ p : Fin i → Axis,
      ∃ c : ℝ, 0≤c ∧ ∀ (v : ℕ) (x : Cover), street x≤v → ‖jumps i p f x‖ ≤ c*(1+v:ℝ)^(u+1-i) := by
    induction hp using Nat.decreasingInduction with
    | self =>
      intro p; refine ⟨0,le_rfl,fun v x _ => ?_⟩
      rw [zero_mul,show jumps _ p f x=0 from gesture_over (G:=G) ⟨a,b,x,u+1,p⟩ (Nat.lt_succ_self _) (Labels.axes G u j.val.2),norm_zero]
    | of_succ i hi IH =>
      intro p
      let g:= jumps i p f
      choose c hc h using fun i : Axis => IH (Fin.cons i p)
      let m:= u+1-(i+1)
      refine ⟨‖g 0‖+∑ i,c i, add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => hc i),?_⟩
      intro v x hv
      let z : ℝ := v
      have he (j) (hj : street j ≤ v) i' : ‖stepValue g i' j‖ ≤ (∑ i,c i)*(1+z)^m := by
        have hu : 1+z≥0 := by dsimp only [z]; positivity
        dsimp only [g]; rw [← hopped, ← steps]
        exact (h i' v j hj).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ _)) (pow_nonneg hu _))
      have hz : 0 ≤ z := Nat.cast_nonneg _
      have ht : 0 ≤ ∑ i,c i := Finset.sum_nonneg fun i _ => hc i
      apply (from_walk g (by exact mul_nonneg ht (pow_nonneg (by linarith) m)) he x hv).trans
      have hy : 1 ≤ (1+z)^(m+1) := one_le_pow₀ (by linarith)
      have h1 := mul_le_mul_of_nonneg_left hy (norm_nonneg (g 0))
      rw [pow_succ] at h1
      change ‖g 0‖+z*_≤ _*(1+z)^(u+1-i); rw [show u+1-i=m+1 by unfold m; omega,pow_succ]; nlinarith only [h1,mul_nonneg ht (show 0≤(1+z)^m by positivity)]
  obtain ⟨w,he,hc⟩ := hh 0 (Nat.zero_le _) Fin.elim0
  have ht : u+1-0≤d := by
    have hp : u+2≤d := j.property; omega
  exact ⟨w,he,fun M z hs => (hc M z hs).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show 1 ≤ (1+M:ℝ) by simp) ht) he)⟩

lemma display : ∃ c : ℝ,0≤c ∧ ∀ (T : ℕ) (x : Address G), street x.1≤T→ ∑ i : KeyIn G d, ‖tester i.val x‖ ≤ c*(1+T:ℝ)^d := by
  choose t ht hc using fun (i : KeyIn G d × PlaqAxes × G.ColorIndex) => room i.1 i.2.1 i.2.2
  let H := ∑ i,t i
  have hv : 0 ≤ H := Finset.sum_nonneg fun i _ => ht i
  refine ⟨(Fintype.card (KeyIn G d):ℝ)*H,mul_nonneg (by positivity) hv,?_⟩; rintro T ⟨z,a,b⟩ hp
  have h1 (i : KeyIn G d) : ‖tester i.val (z,a,b)‖ ≤ H * (1+T:ℝ)^d := (hc (i,a,b) T z hp).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => ht i) (Finset.mem_univ _)) (by positivity))
  refine le_trans (Finset.sum_le_sum fun j _ => h1 j) ?_; simp [← mul_assoc]

def lengthW (s : ℝ) := walls s ^2
lemma zone_power (i : ℕ) {a : ℝ} (ha : 0<a) : ∀ᶠ s in atTop, ((lengthW s):ℝ)^i ≤ bill a s := by
  filter_upwards [rate_wall ha (i*2),big.eventually_ge_atTop 1] with s hs hp
  have he : Real.exp (Real.log (walls s:ℝ))= (walls s:ℝ) := Real.exp_log (by exact_mod_cast hp)
  unfold lengthW; rw [Nat.cast_pow,← he, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; push_cast; linarith only [hs]
lemma roomier (i : ℕ) {a : ℝ} (ha : 0<a) (M : ℝ) : ∀ᶠ s in atTop,M*(1+lengthW s:ℝ)^i ≤ bill a s := by
  filter_upwards [zone_power i (a:=a/2) (by linarith),transports (a:=a/2) (b:=a) (by linarith) ((max 0 M)*2^i),big.eventually_ge_atTop 1] with s hs hf hu
  have hp : (1:ℝ) ≤ lengthW s := by unfold lengthW; exact_mod_cast one_le_pow₀ hu
  refine le_trans ?_ hf
  calc
    _ ≤ max 0 M*(2*↑(lengthW s))^i := mul_le_mul (le_max_right ..) (pow_le_pow_left₀ (by positivity) (by linarith only [hp]) _) (by positivity) (le_max_left ..)
    _ ≤ _ := by rw [mul_pow,← mul_assoc]; gcongr

variable {A : Type}
lemma radiant (k : ℕ) : ∀ᶠ s in atTop, ∀ (A : Type) (f : A → Address G) (v : ℝ) (_ : 1 ≤ v) (i : A), street (f i).1 ≤ lengthW s →
    cents (glyph (features d f v i)) Configuration.bear v ≤ bill (fuel k n) s := by
  obtain ⟨c,hc,h⟩ := display (d:=d) (G:=G)
  let a := fuel k n; have hp := fuel_real k n
  have hv : Tendsto (bill (a/2)) atTop atTop := bill_lo (by dsimp only [a]; linarith)
  filter_upwards [roomier d (a:=a/2) (by dsimp [a]; linarith) c,hv.eventually_ge_atTop 1,
    transports (show a/2<a by dsimp [a];linarith) 2] with s h1 h2 h3 A f v he i hz
  have hs (p : KeyIn G d) : cents (glyph (Finsupp.single (Sum.inl p : KeyIn G d ⊕ A) (fixedKey d f v i p))) Configuration.bear v ≤ ‖tester p.val (f i)‖ := by
    dsimp only [glyph]; rw [Finsupp.linearCombination_single,← MvPolynomial.C_mul']; apply (funds _ (zero_le_one.trans he) ..).trans
    rw [pay_C,pay_X,fixedKey,arbor, Pi.smul_apply, Complex.norm_real,norm_smul, norm_inv,Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans he) _)]
    change (v^_)⁻¹ * _ * v ^ Labels.generation p.val ≤ _; have hb := zero_lt_one.trans_le he; field_simp; exact le_rfl
  have hw : cents (glyph (Finsupp.single (Sum.inr i : KeyIn G d⊕A) (((v:ℂ)^(d+1))⁻¹))) Configuration.bear v ≤ 1 := by
    rw [glyph,Finsupp.linearCombination_single, ← MvPolynomial.C_mul']; apply (funds _ (zero_le_one.trans he) ..).trans
    rw [pay_C,pay_X,norm_inv,norm_pow, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans he)]
    change (v^_)⁻¹*v^(d+1)≤_; have H := zero_lt_one.trans_le he; field_simp; exact le_rfl
  unfold features; rw [map_add,map_sum]; apply (taller _ (zero_le_one.trans he) ..).trans
  apply (add_le_add ((Rise.collect _ (zero_le_one.trans he) ..).trans (le_trans (Finset.sum_le_sum fun j _ => hs j) (h _ _ hz))) hw).trans
  linarith only [h1,h2,h3]
end YM.Next.Rank.Glimmer
