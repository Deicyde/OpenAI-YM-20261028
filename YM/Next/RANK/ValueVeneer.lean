import YM.Next.RANK.Peaks
import YM.Next.RANK.Peano
import YM.Next.RANK.Stories
import YM.Next.RANK.TrueWind


/-!
# Real calibrated curvature polynomials

Keep full old H for determination on rays; each entry (at even a mask boundary)
is continued along the ray only where large threshold flags are absent. Obtain
linearity and star from the whole polynomial rather than asserting historywise
reality for wrapping entries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Set Function Filter MeasureTheory MvPolynomial Lattice Wilson RG Source Labels Source.Drops Configuration
open Normal Rise Common Asymptotics
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {N p k d b i D : ℕ} {S : Rules G} {e : ℝ}

abbrev Up (C : Family G) (k p b : ℕ) := links G (0:Site (C.side k p)) b

def Summary {ι : Type*} {n : Side} (u : Rules G) (p : BudgetPoint) (b D : ℕ) (X : ι → Support n) (A : ι → Config G n→ℂ)
    (f : ι → ℂ) (T Q : ℝ) (L : poly (links G (0:Site n) b)) :=
    ∃ v, SumBudget (fun i=> ‖f i‖*v i) Q ∧ Teller u 0 b p D X A f v T L

structure WRead (S : Rules G) (k N p d b i D : ℕ) (c : ℝ) (v : C.label d) (F : poly (Up C k p b)) : Prop where
  plans : ∃ P Q, F=P+Q ∧
    Summary S (C.path.rep N p k).p b D (nearX C v i k N p) (nearA C v i k N p) (nearW C v i k N p) c (3*moneys C d k N p v) P ∧
    Summary S (C.path.rep N p k).p b D (wideX C v i k N p) (wideA C v i k N p) (wideW C v i k N p) c (expCut (C.path.rep N p k).p i *moneys C d k N p v) Q

lemma bind (S : Rules G) (D : ℕ) : ∃ c : ℝ,0 ≤ c ∧ ∀ (ι : Type) (n : Side) (p : BudgetPoint) (b : ℕ) (X : ι→Support n)
    (A : ι→ Config G n →ℂ) (f : ι→ℂ) (Q : ℝ), Wrapper p X A f Q → D+1≤p.order → ∃ L: poly (links G (0:Site n) b),
      Summary S p b D X A f (((Fintype.card (links G (0:Site n) b):ℝ)+1)^D*c) Q L := by
  obtain ⟨c,hc,H⟩:= till S D
  refine ⟨c,hc,fun ι n p b X A f Q h hp=>?_⟩
  obtain ⟨e,hE,Hc⟩:=h.pays; obtain ⟨L,hL⟩:= H ι n 0 b X A f p hp (fun i=>(hE i).1) _ (fun i=>(hE i).2) Hc.2.1
  exact ⟨L,e,Hc,hL⟩
private lemma prepared (S : Rules G) (D : ℕ) (h : C.Makes) (d : ℕ) : ∃ c : ℝ,0 ≤ c ∧ ∀ (k b p i N : ℕ), C.ref d≤k → k≤N →
    D+1 ≤(C.path.rep N p k).p.order → ∀ v : C.label d, ∃ F : poly (Up C k p b),WRead S k N p d b i D (((Fintype.card (Up C k p b):ℝ)+1)^D*c) v F := by
  obtain ⟨c,hc,Hc⟩:=bind S D
  refine ⟨c,hc,fun k b p i N hk hN hP v=>?_⟩
  obtain ⟨hx,hv⟩:=receipts C i h hk hN v p
  obtain ⟨L,hL⟩:= Hc _ _ _ b _ _ _ _ hx hP
  obtain ⟨Q,hQ⟩:= Hc _ _ _ b _ _ _ _ hv hP
  exact ⟨L+Q,⟨⟨L,Q,rfl,hL,hQ⟩⟩⟩

lemma exp_le (P : BudgetPoint) (m : ℕ) : expCut P m≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr P.exponent_pos.le) (Nat.cast_nonneg _))

variable {v : C.label d} {L : poly (Up C k p b)}
lemma tallied (h : WRead S k N p d b i D e v L) (he : 0≤ e) : totalDegree L ≤ D ∧ coin L≤ 4*moneys C d k N p v * e := by
  obtain ⟨P,Q,rfl,a,b⟩:=h.plans; obtain ⟨u,hU,H⟩:= a; obtain ⟨w,hw,W⟩:= b
  refine ⟨(totalDegree_add ..).trans (max_le H.produced.choose_spec.1.degree W.produced.choose_spec.1.degree), ?_⟩
  have hv := money_nn C d k N p v
  have ht:= H.charge.trans (mul_le_mul_of_nonneg_right hU.2.2 he)
  have hz:= W.charge.trans (mul_le_mul_of_nonneg_right (le_trans hw.2.2 (mul_le_of_le_one_left hv (exp_le ..))) he)
  refine (taller _ zero_le_one ..).trans ?_; change coin _+coin Q ≤ _; linarith only [ht,hz]

lemma beginnings (h : WRead S k N p d b i D e v L) (hp : C.Makes) (h₀ : C.ref d≤k) (h₁ : k≤N) (x : Space G (0:Site (C.side k p)) b) (hx : ‖x‖≤pane S) :
    ‖awakeFull C k N p v (net (C.path.rep N p k).p 0 b x)-text (scan x) L‖≤4*moneys C d k N p v * ‖x‖^(D+1) := by
  obtain ⟨F,P,rfl,α,hβ⟩:= h.plans
  let p':=(C.path.rep N p k).p; let M:=moneys C d k N p v
  obtain ⟨u,hu,hU⟩:=α; obtain ⟨s,hs,Hs⟩:=hβ
  rw [←sections_true hp h₀ h₁ p i v _ (voids (occupied p' x S hx) le_rfl),text,map_add,add_sub_add_comm]; apply (norm_add_le ..).trans
  apply (add_le_add ((hU.calls x hx).2 |>.trans (mul_le_mul_of_nonneg_right hu.2.2 (pow_nonneg (norm_nonneg _) _)))
    ((Hs.calls x hx).2 |>.trans (mul_le_mul_of_nonneg_right (le_trans hs.2.2 (mul_le_of_le_one_left (money_nn C ..) (exp_le ..))) (pow_nonneg (norm_nonneg _) _)))).trans_eq; ring

abbrev monitor (G : Gauge) {n : Side} (p : RG.BudgetPoint) {o : Site n} {b : ℕ} (x : Space G o b) (s:ℝ) := net p o b (s • x)
abbrev seen {G : Gauge} {n : Side} {o : Site n} {b : ℕ} (P : poly (links G o b)) (x : Space G o b) := fun s : ℝ=> text (scan (s • x)) P

def jetbill (C : Family G) (k N p b d) (v : C.label d) (s : Space G (0:Site (C.side k p)) b) (t : ℝ) := awakeFull C k N p v (monitor G (C.path.rep N p k).p s t)

variable {n : Side}
lemma rotates_in (S : Rules G) (p : RG.BudgetPoint) (s : Space G (0:Site n) b) : ∀ᶠ t : ℝ in 𝓝 0, flags p.threshold (monitor G p s t)=∅ := by
  have hp : Tendsto (fun t : ℝ => t • s) (𝓝 0) (𝓝 0) := by simpa using! (continuous_id.smul (continuous_const (y:=s))).tendsto (0:ℝ)
  filter_upwards [hp.eventually (Metric.ball_mem_nhds (0:Space G (0:Site n) b) (pane_pos S))] with i hi; rw [dist_zero_right] at hi
  exact voids (occupied p _ S hi.le) le_rfl
lemma watching (h : WRead S k N p d b i D e v L) (hp : C.Makes) (h₀ : C.ref d≤k) (h₁ : k≤N) (x : Space G (0:Site (C.side k p)) b) :
    asym D (jetbill C k N p b d v x-seen L x) := by
  have hX : Tendsto (fun t : ℝ=> t • x) (𝓝 0) (𝓝 0) := by simpa using! (continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)
  apply error_power (4*moneys C d k N p v* ‖x‖^(D+1)); filter_upwards [hX.eventually (Metric.ball_mem_nhds (0:Space G (0:Site (C.side k p)) b) (pane_pos S))] with t ht
  rw [dist_zero_right] at ht; refine (beginnings h hp h₀ h₁ (t • x) ht.le).trans_eq ?_; rw [norm_smul];ring

lemma examines {o : Site n} (P Q : poly (links G o b)) (hp : totalDegree P≤D) (hq : totalDegree Q≤D) (h : ∀ s, asym D (seen P s-seen Q s)) : P=Q := by
  apply listen _ _ 1 zero_lt_one; intro x hx
  obtain ⟨v,rfl,Hv⟩:= reads_back x 1 zero_le_one hx
  have he:= decipher D (seen P v) (seen Q v) (verse P _ D hp) (verse Q _ D hq) (h v); have hg:= congr_fun he 1; simpa only [seen,one_smul] using! hg

-- force reality at physical ray (not assuming real lower coordinates)
variable (h : C.Makes) (hX : C.ref d ≤ k) (hn : k ≤ N) {F : C.label d → poly (Up C k p b)} (hv : 0 ≤ e) (H : ∀ v,WRead S k N p d b i D e v (F v))
include h hX hn hv H

lemma reads_linear : IsLinearMap ℂ F := by
  have hp (x y : C.label d) (c : ℂ) : F (x+c•y)=F x+c• F y := by
    apply examines _ _ (tallied (H _) hv).1 ((totalDegree_add ..).trans (max_le (tallied (H x) hv).1 ((totalDegree_smul_le ..).trans (tallied (H _) hv).1)))
    intro s; let V:= H x; let Q v:=seen (F v) s; let A (v : C.label d):=jetbill C k N p b d v s
    have he := (((watching (H x) h hX hn s).add ((watching (H y) h hX hn s).const_mul_left c)).sub (watching (H (x+c•y)) h hX hn s))
    refine he.congr' ?_ EventuallyEq.rfl; filter_upwards [rotates_in S (C.path.rep N p k).p s] with t ht
    have ht : A (x+c • y) t=A x t+c*A y t := (on_branch h hX hn p _ ht x).2.2 y c
    change (A x t-Q x t + c * (A y t-Q y t))-(A (x+c•y) t-Q (x+c•y) t) = Q (x+c•y) t-seen _ s t
    rw [ht,show seen (F x+c • F y) s t=Q x t+c*Q y t by unfold Q seen text; rw [map_add,map_smul,smul_eq_mul]];ring
  have h₀ : F 0=0 := by have hh := hp 0 0 1; simp only [one_smul,add_zero,left_eq_add] at hh; exact hh
  exact ⟨fun x y=> by simpa only [one_smul] using! hp x y 1,fun c x=> by simpa [h₀] using hp 0 x c⟩

lemma rays_real (v : C.label d) (x : Space G (0:Site (C.side k p)) b) : text (scan x) (F (star v))=star (text (scan x) (F v)) := by
  let q:= seen (F v) x; let Q:=seen (F (star v)) x; let b' (v : C.label d):= jetbill C k N p b d v x
  have he : asym D (star (b' v-q)) := by
    rw [asym,isLittleO_iff]; intro c hc; filter_upwards [(watching (H v) h hX hn x).def hc] with s hs; rw [Pi.star_apply,norm_star]; exact hs
  have hh : star (b' v-q) =ᶠ[𝓝 0] b' (star v)-star q := by
    filter_upwards [rotates_in S (C.path.rep N p k).p x] with t ht
    change star (b' v t-q t)= b' (star v) t-star (q t); rw [star_sub]; exact congr_arg (· - _) (on_branch h hX hn p _ ht v).1.symm
  obtain ⟨f,hf⟩ : ∃ f,q=Dims D f := verse (F v) _ D (tallied (H _) hv).1
  have ha : star q=Dims D (fun i=> star (f i)) := by rw [hf];funext i;simp [Dims]
  have ht : asym D (Q-star q) := ((he.congr' hh EventuallyEq.rfl).sub (watching (H (star v)) h hX hn x)).congr_left (fun t=> by change b' (star v) t-star q t - (b' (star v) t-Q t)=Q t-star q t; ring)
  have hh:= congr_fun (decipher D Q (star q) (verse _ _ _ (tallied (H _) hv).1) ⟨_,ha⟩ ht) 1
  change text (scan ((1:ℝ) • x)) _ = star (text (scan ((1:ℝ) • x)) _) at hh; simpa only [one_smul] using hh
lemma sterling : F (C.refUnit d)=1 := by
  let v:= C.refUnit d; apply examines _ _ (tallied (H _) hv).1 (by rw [totalDegree_one]; exact Nat.zero_le _); intro s
  let P:= jetbill C k N p b d v s
  apply ((watching (H v) h hX hn s).neg_left).congr' _ EventuallyEq.rfl
  filter_upwards [rotates_in S (C.path.rep N p k).p s] with t ht; have hh : P t=1 := (on_branch h hX hn p _ ht v).2.1
  change -(P t-_)=(_ : ℂ)-seen 1 _ _
  simp only [hh,seen,text,map_one]; ring

omit h hX hn hv H in
lemma scan_sum (S : Space G (0:Site n) b) (j : links G (0:Site n) b) : |scan S j| ≤ ‖S‖ := by
  obtain ⟨L,hx,hv,ht⟩:= scanning G j.2
  change |S _ j.2| ≤ _; refine le_trans ?_ (le_trans (ht (S j.1)) (norm_le_pi_norm S j.1)); exact le_of_eq (by rw [hv,Complex.norm_real,Real.norm_eq_abs])

omit h hX hn hv H in
def coloring {G : Gauge} {ι : Type*} (u : G.El) (x : ι → G.Color) : ι → G.Color := fun i=>G.adjoint u (x i)

omit h hX hn hv H in
lemma land_smul (S : Space G (0:Site n) b) (u : G.El) (t : ℝ) : coloring u (t • S)=t • coloring u S := by ext1 i; exact map_smul (G.adjoint u) t _

omit h hX hn hv H in
lemma land_eq (S : Space G (0:Site n) b) (p : BudgetPoint) (u : G.El) : net p 0 b (coloring u S)=Lattice.gauge (fun _=>u) (net p 0 b S) := by
  ext1 i; unfold Lattice.gauge; dsimp only
  by_cases h : i∈Room (0:Site n) b
  · let a : Dim (0:Site n) b := ⟨i,h⟩
    rw [show net _ _ _ _ i= _ from net_in p (coloring u S) a, show net p 0 b S i= _ from net_in p S a]; unfold coloring; rw [← map_smul]
    apply G.mat_injective; rw [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; simp [Gauge.conjugate]
  rw [net_out p _ _ h,net_out p S i h]; group

lemma land (v : C.label d) (x : Space G (0:Site (C.side k p)) b) (f : G.El) : text (scan (coloring f x)) (F v) = text (scan x) (F v) := by
  let X:= coloring f x; let P:= (C.path.rep N p k).p
  let A:= jetbill C k N p b d
  have he : A v x =ᶠ[𝓝 0] A v X := by
    filter_upwards [rotates_in S P x] with t ht
    rw [show A v x t= _ from (sections_true h hX hn p i v _ ht).symm]
    have hs : monitor G P X t=Lattice.gauge (fun _=>f) (monitor G P x t) := by unfold monitor X; rw [← land_smul]; exact land_eq ..
    have hx : flags P.threshold (monitor G P X t)=∅ := by rw [hs,gauge_flags]; exact ht
    rw [show A v X t=_ from (sections_true h hX hn p i v _ hx).symm,hs]
    obtain ⟨L,Q,H',l,q⟩:= (H v).plans; rcases l with ⟨e,he,hT⟩; rcases q with ⟨z,hz,hv⟩
    congr 1
    · exact tsum_congr (fun i=>congr_arg (fun x : ℂ=> _ * x) ((hT.smooth i).symmetry (fun _=>f) (monitor G P x t)).symm)
    exact tsum_congr (fun i=>congr_arg (fun x : ℂ=> _ * x) ((hv.smooth i).symmetry (fun _=>f) (monitor G P x t)).symm)
  let P := seen (F v)
  have hx : asym D (P X-P x) := by
    apply ((watching (H v) h hX hn x).sub (watching (H v) h hX hn X)).congr' _ EventuallyEq.rfl; filter_upwards [he] with t ht
    change (A v x t-P x t)-(A v X t-P X t)=P X t-P x t; rw [ht]; ring
  have hp := congr_fun (decipher D (P X) _ (verse _ _ _ (tallied (H v) hv).1) (verse _ _ _ (tallied (H v) hv).1) hx) 1
  change seen _ X 1 = seen _ x 1 at hp; exact (by simpa only [seen,one_smul] using hp)

omit h hX hn hv H in
theorem machine (S : Rules G) (D : ℕ) (C : Family G) (h : C.Makes) (d : ℕ) : ∃ c : ℝ,0≤ c ∧ ∀ k b p i N : ℕ,C.ref d≤ k → k≤N → D+1 ≤(C.path.rep N p k).p.order →
    ∃ F : C.label d →ₗ[ℂ] poly (Up C k p b), ∀ v : C.label d, WRead S k N p d b i D (((Fintype.card (Up C k p b):ℝ)+1)^D*c) v (F v) := by
  obtain ⟨c,Hc,hE⟩:= prepared S D h d; refine ⟨c,Hc,fun k b p i N hk hN hP=> ?_⟩
  choose F hF using hE k b p i N hk hN hP
  exact ⟨IsLinearMap.mk' F (reads_linear h hk hN (by positivity) hF),hF⟩
end YM.Next.Rank.Spindle
