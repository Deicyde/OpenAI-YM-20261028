import YM.RG08.Atrium.Stores
/-! # Inverse costs at stage W for each fixed e, diagonal pre & post.
 Use matrix product receipts on ANY corridor afterwards. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Atrium
open Function Finset Jetty Lattice Isles Forms Pert.Bulk Skiff Trickle
open Room Gallery Camera Glyph Quarry Weald Hatch Carrel Laurent Filter Stationary Spar Flint
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Lagoon Yurt Halo Trill
open RG Precision Next.Free
open scoped Classical ContDiff BigOperators Topology ENNReal ComplexConjugate Matrix.Norms.Frobenius PowerSeries Matrix
variable {I Y:Type}[Fintype I]{G:Gauge}{d n p l e D k:ℕ}
 set_option linter.unusedSectionVars false in
lemma post.sum {s:Finset Y}{P:Y→Hearth I}{u:Y→ℝ}(H:∀ i∈s,post (P i) (u i)):post (s.sum P) (s.sum u):=by intro i j; rw [Matrix.sum_apply]; exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun k hk=>H k hk i j))
-- prior power function for prices k all. *uniform prior*. Wage multiplication for all. -/
lemma deputy_budget (I:Type)[Fintype I](k:ℕ):∃ C:ℝ→ℝ,Wage C ∧ ∀ M:Sock I,∀ B:Hearth I,∀ P:ℝ,1≤P→post B P→(∀ i≤k,post (dusk i M) P)→ ∀ i≤k,post (dusk i (deputy M B)) (C P):=by
 induction k with
 | zero=>refine ⟨id,Wage.input,fun M B P h hc hD i hi=>?_⟩;rw [Nat.eq_zero_of_le_zero hi,deputy_home];exact hc
 | succ k ih=>
    obtain ⟨C,hC,H⟩:=ih
    let t:ℝ:=Fintype.card I;have ht:0 ≤ t:=Nat.cast_nonneg _
    let u:ℝ:=k+1; have hu:0 ≤ u:=by unfold u;positivity
    let F(W:ℝ):=t*(u*(t*C W*W))*W
    have hF:Wage F:= ((Wage.constant t ht).mul ((Wage.constant u hu).mul (((Wage.constant t ht).mul hC).mul Wage.input))).mul Wage.input
    refine ⟨fun W=>C W+F W,hC.add hF,fun M B W hW hB hD i hi j s=>?_⟩
    let N:=deputy M B;have hN:=H M B W hW hB (fun i hi=>hD _ (by omega))
    rcases eq_or_ne i (k+1) with rfl|hk
    · rw [emboss]
      have hg:post (tension M N k) (u*(t*C W*W)):=by
        have he:=post.sum (s:=range (k+1)) (fun i (hi:i∈range (k+1))=> post.mul (hN i (by simpa only [mem_range,Nat.lt_succ_iff] using hi)) (hD (k+1-i) (by omega)) (hC.nn hW))
        rw [sum_const,nsmul_eq_mul,card_range,Nat.cast_add,Nat.cast_one] at he;exact he
      exact (post.mul hg.diff hB (mul_nonneg hu (mul_nonneg (mul_nonneg ht (hC.nn hW)) (zero_le_one.trans hW))) j s).trans (le_add_of_nonneg_left (hC.nn hW))
    exact (hN i (by omega) j s).trans (le_add_of_nonneg_right (hF.nn hW))
lemma toe_post {P Q:ℝ}{M N:Sock I}(n:ℕ)(hp:0≤P)
 (h:∀ i≤n,post (dusk i M) P)(he:∀ i≤n,post (dusk i N) Q):∀ i≤n,post (dusk i (M*N)) (((n:ℝ)+1)*(Fintype.card I*P*Q)):=by
 intro i hi j k
 have hq:0≤Q:= (abs_nonneg _).trans (he 0 (by omega) j j)
 rw [dusk_mul];have hh:=post.sum (s:=range (i+1)) (fun a (ha:a∈range (i+1))=> post.mul (h a (by simp only [mem_range] at ha;omega)) (he (i-a) (by omega)) hp)
 rw [sum_const,nsmul_eq_mul,card_range,Nat.cast_add,Nat.cast_one] at hh;apply (hh j k).trans; gcongr
lemma inv_fallen (M N R S:Sock I)(hM: M*N=1)(hN:S*R=1): N-S=S*(R-M)*N:=by rw [mul_sub,sub_mul,hN,one_mul,mul_assoc,hM,mul_one] -- Matrix.mul_sub not necessary

lemma inkDelta {M N R S:Sock I}{W δ:ℝ}(hM:M*N=1)(hN:S*R=1)(hW:0≤W)(k:ℕ)(hv:∀ i≤k,post (dusk i N) W)(hr:∀ i≤k,post (dusk i S) W)
 (hs:∀ i≤k,post (dusk i (R-M)) (W*δ))(hσ:0≤δ):∀ i≤k,post (dusk i (N-S)) ((((k:ℝ)+1)*(Fintype.card I:ℝ))^2*W^3*δ):=by
 let a:ℝ:= (Fintype.card I:ℝ)
 rw [inv_fallen _ _ _ _ hM hN]
 have H:0≤a:=Nat.cast_nonneg _
 have hT:=toe_post k (show 0≤((k:ℝ)+1)*(a*W*(W*δ)) by positivity) (toe_post k hW hr hs) hv
 -- dangling D E W implicit blockers from unused
 convert hT using 3; unfold a; ring
variable {X:Labels.Frame G d}
-- uniform over post width W: T0 entries bound W, diagonal leading always ≥1, rest may cost W. Wx must include W tight for inverse diag. drop N.W-damped in product later.
lemma evacuate_price (X:Labels.Frame G d)(k:ℕ):∃ C:ℝ→ℝ,Wage C ∧ ∀ {M:Playbook X}{a:Accent X→ℝ},Arrow street a (ink M)→ (∀ i,1≤a i)→∀ W:ℝ,1≤W→(∀ i≤k,post (dusk i M) W)→
 ∀ i≤k,post (dusk i (evacuate M a)) (C W):=by
 let Z:=Accent X
 obtain ⟨C,hC,H⟩:=deputy_budget Z k
 obtain ⟨A,m,ha,h⟩:=hC
 let v(W:ℝ):=plum Z d W + W
 have ht:Wage v:= (plum_wage ..).add Wage.input
 have hz : Wage (fun W=> A*v W^m):=(Wage.constant _ ha).mul (by
    clear h; induction m with
    | zero=>simpa using Wage.constant 1 zero_le_one
    | succ m hm=> simp_rw [pow_succ]; exact hm.mul ht -- dependency? use independent.
    )
 refine ⟨_,hz,fun {M} {a} he hf W hW hP i hi s t=>?_⟩
 let B:=acrossF d a (ink M)
 have hB:=inv_board street hW he (hP 0 (by omega)) hf
 have h1:W≤v W:=le_add_of_nonneg_left (plum_nn (by linarith))
 have h2:plum Z d W≤v W:=le_add_of_nonneg_right (by linarith)
 exact (H M B (v W) (hW.trans h1) (fun j k=> (hB j k).trans h2) (fun i hi j k=>(hP i hi j k).trans h1) i hi s t).trans ((h (v W) (hW.trans h1)).2)
end YM.RG08.Atrium
