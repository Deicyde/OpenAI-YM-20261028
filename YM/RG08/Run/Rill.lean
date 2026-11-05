import YM.RG08.Run.Yawl
/-!
# Supplies signed projection covariance and MarkCard
after real phases excluded. Any loaded stratum inputs; no ratio chosen by making reports converge.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J:Type}{u:I→Windows}{w:J→ ShoreP u} {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ A C:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
section book
variable {V B:I→ReadsU F D R}{U A:I→BoardU D R G}{S S':I→Native (Letter F)}{y p q ρ δ:I→ℝ}
lemma accounting (Φ:ReadsU F D R) (Z:Native (Letter F)): edgeBook Φ Z e r=∑ b,∑ j∈range (e+1), coeff j (Z b) • Φ b (e-j) r := by
   rw [edge_marks Φ Z e e le_rfl,Finset.sum_apply,Finset.sum_apply]; refine sum_congr rfl fun i _=>?_; unfold adapt; rw [Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j hj; simp only [Pi.smul_apply,footing (mem_range_succ_iff.mp hj)]
lemma elig (h:Audience y)(he:0≤ p) (hk : ∀ i≤ e,∀ b r, Card k y p (fun a=>V a b i r) 1)(hS : ∀ i,Boards (V i))(hm:∀ j v, j<e∨ j=e ∧ r ≤ slot v → Dig y δ (fun a=> coeff j (S a v))): Card k y (δ*p) (fun i=>edgeBook (V i) (S i) e r) 1 := by
    simp_rw [accounting]; refine Card.group _ h zero_le_one (F:=fun j i=>∑ a∈range (e+1),_) fun i _=> Card.group (range (e+1)) h zero_le_one (F:=fun j a=> coeff j (S a i) • V a i (e-j) r) (fun j hj=> ?_)
    by_cases hz:r ≤ slot i+(e-j); swap
    · simp_rw [show ∀ a: I,V a i (e-j) r=0 from fun a=>not_ne_iff.mp (mt (((hS a).rank i).cap _ _) hz),smul_zero]; exact Card.zero
    exact (hk _ (Nat.sub_le ..) _ _).awake he (hm _ _ (by have he:=mem_range_succ_iff.mp hj; omega))
lemma cardDig (H:Hol G)(b:Letter F){V:I→EnvelopeU D R G r}(hv : Card k y p V 1)(he:d*(slot b) * r≤ k) : Dig y p (fun i=> invest H (V i) b) := by
    obtain ⟨A,hA,HE⟩:=invest_price b R r D; obtain ⟨B,hB,H⟩:=hv.money; refine ⟨_,(Weighed.constant y hA).times hB,fun i=>?_⟩
    exact (HE (V i) _ ((H i).shrink (mint_pos _ _ _) (fun t=> le_trans (greater_bill t _) (by rw [Pi.one_apply, tailP,one_mul]; exact pow_le_pow_right₀ (by simp) he))) _).trans_eq (mul_assoc ..).symm
lemma variance_b {V U:ReadsU F D R}{A B:Native (Letter F)}: edgeBook V A-edgeBook U B=edgeBook (V-U) B+edgeBook V (A-B):= by
   ext1 i; ext1 j; rw [Pi.sub_apply,Pi.sub_apply,Pi.add_apply,Pi.add_apply]; simp_rw [accounting,← sum_sub_distrib,← sum_add_distrib]; refine sum_congr rfl fun p _=> sum_congr rfl fun n _=>?_ ; simp only [Pi.sub_apply,map_sub]; rw [_root_.sub_smul (coeff n (A p)) (coeff n (B p)) (V p (i-n) j),smul_sub]; abel
end book
section momentum
variable {L:Side}{σ B s':ℝ}
lemma belly_exp_l {E α β:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][Fintype β] (b:Site L){θ' v:ℝ} {V:Rooted E α r}{X:Cross L α β}(he:cis k v V A)(ht:X.strip σ B)(hv:0<σ)(hB:0≤B)(hk:0≤ θ')(hp:θ'≤1)(hm:θ'/L.val ≤ v):
    cis k θ' (belly b X V) (((1+4*(r:ℝ))^k*((utter k σ)*(Fintype.card β*B))^r)*A) := by
   apply budget_projection (g:=sires V (bulb (fun _=> node b X))) _ (fun i=>zero_lt_one.trans_le (tailp hk i)); apply Ink.sires_cost he _ _ (mul_nonneg (by positivity) (pow_nonneg (mul_nonneg (utter_pos hv) (by positivity)) _))
   intro i; exact Ink.raise (waysP ht hv i b hk hp hm) ((mul_right_comm ..).le)
lemma runeP {V:EnvelopeU D R G j} (b:Site L)(hr:1/2 ≤ R)(hL:Odd L.val) {θ' v:ℝ} {P: Cross L (Candles G) (Loc G 1)}(hk:cis k v V A)(hp:0≤θ')(he: θ'≤1)(hv:v ≤ 1)(ht:θ'/L.val ≤ v)(hz:P.strip σ B)(hs:0<σ)(hB:0 ≤ B):
    cis k θ' (rue b P V r) (((1+4*(r:ℝ))^k*(utter k σ*(Fintype.card (Loc G 1)*B))^r)*((((r+1:ℕ):ℝ)^k*silkSale G j r)*A)) := by
   have hu: 0≤v:= (div_nonneg hp (by positivity)).trans ht
   have hV: cis k v (fun i=>readdress (V i) b) A:= budget_mono hk (fun i=> mul_nonneg (zero_le_one.trans (tailp hu _)) (norm_nonneg _)) (fun i=>mul_le_mul_of_nonneg_left (read_scores hL hr b _).1 (zero_le_one.trans (tailp hu _)))
   exact belly_exp_l b (spun_p hV hu hv) hz hs hB hp he ht
end momentum
end YM.RG08.Run
