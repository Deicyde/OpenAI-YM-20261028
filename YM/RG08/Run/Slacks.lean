import YM.RG08.Run.Menu
/-!
# Truly same polynomial moments in and out. Low cancellations global, remainder billed termwise on near/far.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door
open scoped BigOperators Topology Real ContDiff Classical
variable {G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{L:Side}{R σ θ η w A B C:ℝ}
variable {b:Site L}{Q:Cross L (Loc G 1) (Loc G 1)}{V:EnvelopeU D R G r}
local notation "B₁" => Beads (Loc G 1) r
-- pre payable if low part anywhere or near terms
lemma trim_one (d k:ℕ)(z:Fin (d+1))(hs:1≤C) (G:Gauge) : ∃ D:ℝ,1≤D ∧ ∀ (L:Side)(b:Site L) (Q: Cross L (Loc G 1) (Loc G 1)), TakesP Q (rug k) (rug k) d C→∀ i:Cover×Loc G 1, (z.val<d ∨ size i.1<L.val) → Charge (rug k) (partsP d z b Q i) (D * Vale.height L (z.val+1)*dime (z.val+1) i.1) := by
  obtain ⟨D,hD,H⟩:= buds_bound (α:=Loc G 1) (β:=Loc G 1) (rug k) rug_one d z.val (Nat.le_of_lt_succ z.isLt)
  let A:=D*C; have ha:1≤A:= one_le_mul_of_one_le_of_one_le hD hs; have hA:C≤A:=le_mul_of_one_le_left (zero_le_one.trans hs) hD
  refine ⟨_,ha,fun L b Q h i hQ=>?_⟩
  unfold partsP; split
  next ht=>
    have hm:size i.1≤ L.val:= by omega
    let f:= fun y x=>node b Q (x,i.2) y; rw [ht]
    apply Ink.raise (surplus_paid (v:=rug k) (zero_le_one.trans rug_one) d L.val f (show 0≤C*Vale.height L (d+1) by positivity [height_p L (d+1)]) (fun l hl x hk=> by rw [← hl]; exact h.main_bound _ _ hl.le _ _ hk) i.1 hm)
    refine mul_le_mul (mul_le_mul_of_nonneg_right hA (height_p ..).le) ?_ (by positivity) (mul_nonneg (by positivity) (height_p ..).le)
    exact (pow_le_pow_left₀ (by positivity) (show (size i.1:ℝ)≤1+size i.1 from le_add_of_nonneg_left zero_le_one) d).trans (dime_more (Nat.le_succ d) _)
  apply Ink.raise (H L Q C _ h (zero_le_one.trans hs) b i); exact mul_le_mul_of_nonneg_left (dime_more (Nat.le_succ _) _) (mul_nonneg (by positivity) (height_p ..).le)
lemma trim_ear (x:Fin (d+1+1))(z:Fin r→Fin (d+1))(ht:1/2≤R)(hp:1≤ A)(hk:d+1≤ D)(m:ℕ): ∃ C:ℝ,1≤C ∧ ∀ (L:Side)(b:Site L)(Q:Cross L (Loc G 1) (Loc G 1))(he:Odd L.val), TakesP Q (rug m) (rug m) d A→∀ (V:EnvelopeU D R G r)(i:B₁), burden x z≤d ∨ girth i<L.val → cis m 1 (fun j=> Vale.whirl he ht hk b Q V x z (i,j)) (C*(Vale.height L (burden x z)*tailP (burden x z) 1 i)*‖V i‖) := by
  choose D hD H using fun i=> trim_one d m (z i) hp G
  obtain ⟨C,hC,HC⟩:= chest_income d (d+1) _ rfl hk R ht
  let D':=∏ i,D i; have hD':1≤ D':= one_le_prod (fun i _=> hD i); have hZ:1≤D'*C:=one_le_mul_of_one_le_of_one_le hD' hC
  refine ⟨_,hZ,fun L b Q he hQ V i ha=>?_⟩
  let f := 1+(girth i:ℝ); let g (j:Fin r):= (z j).val+1; have hf:1≤f:= by unfold f; simp
  have he' (j:Fin r) : Charge (rug m) (partsP d (z j) b Q (i j)) (D j * Vale.height L (g j) * f^(g j)) := by
    refine Ink.raise (H j _ b Q hQ _ ?_) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr (root_size i j)) 1) (g j)) (mul_nonneg (zero_le_one.trans (hD _)) (height_p ..).le)) -- add side switch
    cases ha
    · left; have hP: ∑ j,g j+(0:ℕ) ≤ d:= le_trans ?_ ‹burden x z≤ d› -- use
      have h := single_le_sum (fun i _=> Nat.zero_le (g i)) (mem_univ j); unfold g at *; simp only [add_zero] at hP; omega
      unfold burden g; simp
    · right; exact lt_of_le_of_lt (root_size i j) ‹girth i<L.val›
  let E j:= bulb (fun i=>partsP d (z i) b Q) (i,j); let W := ∑ j,g j
  have hl : Charge (tailP m 1) E (D' * Vale.height L W * f^W) := by
    have hz:= bulb_charge (fun i=> partsP d (z i) b Q) (fun _=> rug m) i _ he'
    apply Charge.mono hz (fun i=> (tailp zero_le_one i).trans' zero_le_one) (fun i=>?_)
    · unfold Vale.height D' W; simp only [prod_mul_distrib,prod_pow_eq_pow_sum,le_refl]
    change tailP m 1 i≤ mint m i; simpa only [tailP,one_mul] using lower_bill i m
  let P := (V i).comp (chest he ht hk b x)
  apply Ink.raise (rideP (tailP m 1) hl P)
  have hM : ‖P‖≤ C*Vale.height L x.val*‖V i‖:= (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul_of_nonneg_left (HC ..) (norm_nonneg _)).trans_eq (mul_comm ..))
  apply le_trans (mul_le_mul_of_nonneg_left hM hl.nonneg)
  simp only [tailP,one_mul]; change _≤D'*C*(Vale.height L (burden x z)*f^(burden x z))*‖V i‖
  have hz : f^W≤f^(burden x z):=pow_le_pow_right₀ hf (Nat.le_add_left ..)
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (mul_nonneg (by positivity) (height_p ..).le)) (by positivity [height_p L x.val])) (le_of_eq ?_)
  unfold Vale.height W burden g; ring
-- true term far. Replaced expression before summing.
lemma far_lug (d r k : ℕ)(he:d+1≤k)(h:1/2≤R)(hp:0<σ)(hq:0≤A) (D:ℕ) : ∃ C:ℝ, 0≤C ∧ ∀ (L:Side)(b: Site L)(Q:Cross L (Loc G 1) (Loc G 1)), PaysPath Q σ A d → ∀ (V:EnvelopeU D R G r)(i:Beads (Loc G 1) r), L.val≤girth i → cis k 1 (fun j:Beads (Loc G 1) r=> bulb (fun _:Fin r=>node b Q) (i,j) • readdress (V i) b) (C*(Vale.height L (d+1)*tailP k 1 i)*‖V i‖) := by
   let p:= (1+4*(r:ℝ))^k; let W:=(σ⁻¹^k*(k.factorial:ℝ)*Real.exp σ)*(Fintype.card (Loc G 1)*A); have hw:0≤W:= by unfold W; positivity
   have hP:0≤p:= by unfold p; positivity
   refine ⟨p*(2:ℝ)^k*W^r,by positivity,fun L b Q hQ V i hi=>?_⟩
   let t:ℝ:=1/L.val; have ht:0≤t:=by unfold t; positivity
   have hL: Q.strip σ A:= strip_mono (hQ.offsets [] (by simp)) le_rfl (mul_le_of_le_one_right hq (by simp [Vale.height]; exact Carrier.unitStep_le L))
   apply Ink.raise (rideP (tailP k 1) (waysP (σ:=t) hL hp i b (η:=1) zero_le_one (le_refl _) (le_refl _)) (readdress (V i) b)); apply mul_le_mul _ (read_scores hQ.odd h b _).1 (norm_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (height_p ..).le ((tailp zero_le_one i).trans' zero_le_one)))
   change p * tailP k t i * _ ≤ _
   have hi': 1≤ t*(girth i:ℝ):= by unfold t; rw [one_div,← div_eq_inv_mul]; apply (le_div_iff₀ (by positivity)).2; simpa only [one_mul] using (Nat.cast_le.mpr hi)
   have hy:tailP k t i ≤ (2:ℝ)^k*(Vale.height L (d+1)*tailP k 1 i):= by
     refine (pow_le_pow_left₀ (show 0≤1+t*girth i by positivity) (show 1+t*girth i≤ 2*(t*(1+1*girth i)) by nlinarith) k).trans ?_; unfold Vale.height tailP; rw [mul_pow,mul_pow]; unfold t;rw [one_div]; apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity); exact pow_le_pow_of_le_one (Carrier.unitStep_pos L).le (Carrier.unitStep_le L) he
   calc _ ≤ (p * ((2:ℝ)^k*(Vale.height L (d+1)*tailP k 1 i)))*(W^r) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy hP) (pow_nonneg hw _)
        _ = _ := by ring
end YM.RG08.Run
