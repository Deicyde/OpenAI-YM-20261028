import YM.RG08.Creek.Pup
/-! # Every close step can carry the mixed coefficients at actual addresses.

Rough bound harmless on close span with *Age & operands* pol in z_m. Larger spans require either stable revisit or finer estimates; this statement for close only. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Wings High Pill Taste Run Matrix PowerSeries
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {X:Chain} {G:Gauge}{E e r d τ D j t f i k m n :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}
variable {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1 ≤ D}{T:Signals P Q E τ H Ω h hD}
variable {I J Y:Type} [Fintype I][DecidableEq I]{u:Y→Windows}{a b:I→ℕ}{Z:ℕ→ℝ}
section shipment
variable {p:J→ Dial u}{W:J→ℕ}{U:J→Layouts I G D R}{w:Aperture G P k E τ d D R}{ρ χ R':J→ℝ}
def priorZ (X:Chain)(j:Dial u)(l:ℕ):= X.S.scale j.K-X.S.scale l
structure Arrival (U: J→Layouts I G D R)(X:Chain)(b: J→ Dial u)(S:J→ℕ)(a:I→ℕ)(χ:J→ℝ):Prop where
    accept (i:J): (u (b i).a).start≤ S i
    sleep(i:J): S i≤(b i).K
    piece (i:J):Sense a (U i)
    -- χ budget age given poly-priced ahead. Need length-pol and width gates.
    onset : Audience χ
    height : Weighed χ (fun i=> Dial.fee X (b i))
    future : Weighed χ (fun i=> priorZ X (b i) (S i))
-- indices
structure SoftP (b:J→ Dial u)(S:J→ℕ)(n:ℕ) where
   i: J
   k:ℕ
   low : S i≤ k
   high : k+n ≤ (b i).K
variable (hA:Arrival U X p W a χ)
include hA
-- release from reporting cutoff to chosen stop. convenient budgeting *input priced post subpower exp*, same output.
private abbrev M {J Y:Type} {u:Y→Windows}{p:J→Dial u} {W:J→ℕ}:= SoftP p W n
private def shelfW (hA:Arrival U X p W a χ) (s:M (p:=p) (W:=W) (n:=n)) : Wings u n:=⟨⟨(p s.i).a,s.k,(hA.accept _).trans s.low⟩,(p s.i).N,(p s.i).M,s.high.trans (p s.i|>.main),p s.i|>.ripe⟩ -- include hA
private lemma mon_u : Weighed (fun i:M (p:=p) (W:=W) (n:=n)=> χ i.i) (menu X ∘ shelfW hA) := by
   apply ((hA.height.transfer SoftP.i).plus (hA.future.transfer SoftP.i) (fun i=>hA.onset _)).mono (fun i=>zero_le_one.trans (sh X _))
   intro v
   let k:= (p v.i).K; have hp:v.k≤k:= (Nat.le_add_right ..).trans v.high
   change 2+_+|X.S.scale v.k - X.S.scale k|≤ (2+_+|X.S.scale k-X.S.scale k|)+priorZ X (p v.i) (W v.i)
   unfold priorZ; rw [abs_of_nonpos (sub_nonpos.mpr (age_scale_mono X.S hp)),sub_self,abs_zero,add_zero]; have hh:= age_scale_mono X.S v.low; simp only [k, shelfW,Dial.W]; linarith
-- dominate a Weighed(soft) by Weighed(base) *uniform* on interval (not using pol surviving oversteps, pay step crude). Return necessarily genus $exp$.
private lemma envelope_r {C : M (p:=p) (W:=W) (n:=n)→ℝ}(hp: Weighed (fun i=> χ i.i) C): ∃ A:J→ℝ, Weighed χ A ∧ 0 ≤ A ∧ ∀ i,C i ≤ A i.i:= by
   obtain ⟨U,w,hu,H⟩:=hp; let K:= Weighed.times (Weighed.constant χ hu) (Weighed.power χ hA.onset w)
   exact ⟨_,K,K.positive,fun i=>by apply le_trans (H i).2 (le_of_eq ?_); simp⟩
private lemma step_span (j:J): Real.log 2 *((p j).K - W j :ℕ) ≤ priorZ X (p j) (W j):= by
   -- spacing
   let k:=(p j).K; have he: W j ≤ k:= hA.sleep j; change _ ≤ X.S.scale k-X.S.scale (W j)
   change Real.log 2 * ((k-W j:ℕ):ℝ)≤_
   clear_value k
   induction k,he using Nat.le_induction with
   | base=> simp
   | succ i hi ih=>
      have hp: Real.log 2 ≤ X.S.scale (i+1)- X.S.scale i:= by rw [X.S.scale_succ,add_sub_cancel_left]; exact Real.log_le_log (by norm_num) (by have ht:= X.S.block_large i; exact_mod_cast (show 2≤(X.S.block i).val by omega))
      rw [Nat.succ_sub hi,Nat.cast_succ,mul_add,mul_one]; linarith
private lemma span_cost : Weighed χ (fun i=> (((p i).K-W i:ℕ):ℝ)):= ((Weighed.constant _ (inv_nonneg.mpr (Real.log_nonneg (show 1≤ (2:ℝ) by norm_num)))).times hA.future).mono (fun i=>Nat.cast_nonneg _) (fun i=> (le_inv_mul_iff₀ (Real.log_pos (show 1<(2:ℝ) by norm_num))).2 (step_span hA i)) -- lemma name

abbrev vitalK (ν:G.ColorIndex)(D':ChartRatio G)(X:Chain)(p:J→Dial u)(U:J→ Layouts I G D R)(a b:I→ℕ)(j:J):= ledgerR (dance X ν D' (p j).N) (U j) a b (p j).K
variable (hp:Tights T S ν D' u) (hw: BrookW T u I Z)
include hp
lemma serves_v (i: SoftP p W 0): Sense a (vitalK ν D' X p U a b i.i i.k):=by
   obtain ⟨s,k,hl,hh⟩:=i; dsimp only
   rw [add_zero] at hh; induction hh using Nat.decreasingInduction with
   | self=> unfold vitalK; rw [ledgerR,if_neg (lt_irrefl _)]; exact hA.piece _
   | of_succ i he ih=> let l:SoftP p W 1:=⟨s,i,hl,he⟩; unfold vitalK; rw [ledgerR,if_pos he]; exact creekS_w _ (seasonal hp (shelfW hA l)) (ih (hl.trans (Nat.le_succ _))) h _
include hw
variable {B': J→ℝ} {A:I→ J→ℝ}
local notation "💼" => boon
lemma power_close (h:∀ i,vanes a i+E≤τ)(hB:∀ i,Fest (Z (X.J (p i|>.K))) E 1 (💼 (Real.exp (B' i)) (fun j=> A j i)) (U i))(hz: ∀ i,0≤ A i)(hY:Weighed χ B')(b:I→ℕ): ∃ H:J→ℝ, Weighed χ H ∧ ∀ v : SoftP p W 0,Fest (Z (X.J v.k)) E 1 (💼 (Real.exp (H v.i)) (fun j=> A j v.i)) (vitalK ν D' X p U a b v.i v.k) := by
   obtain ⟨B,hW,H⟩:= funds_rift hp hw b
   let k(s:J) (i:ℕ):= (p s).K-i; obtain ⟨C,hC,h0,H'⟩:= envelope_r hA ((mon_u (n:=1) hA).sway (fun i=>hA.onset _) (hW.transfer (shelfW hA)))
   let r(i:J)(m:ℕ):ℝ:= B' i + k i m*C i
   refine ⟨fun i=> r i (W i),hY.plus ((span_cost hA).times hC) hA.onset,fun v=>?_⟩
   suffices Fest (Z (X.J v.k)) E 1 (💼 (Real.exp (r v.i v.k)) (fun j=> A j v.i)) (vitalK ν D' X p U a b v.i v.k) from fun i hi j s=> owns_mono (this i hi j s) le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (Real.exp_monotone (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le_sub_left v.low _)) (h0 _)))) _) (prod_nonneg fun _ hi=>hz _ _)) zero_le_one)
   obtain ⟨j,n,hn,hh⟩:=v; dsimp only; rw [add_zero] at hh
   induction hh using Nat.decreasingInduction with
   | self=>
      unfold vitalK r k; rw [ledgerR, if_neg (lt_irrefl _),Nat.sub_self,Nat.cast_zero,zero_mul,add_zero]; exact hB _
   | of_succ i he ih=>
      let q:= p j ; let v:SoftP p W 1:=⟨j,i,hn,he⟩; let u:= shelfW hA v; let w:SoftP p W 0:=⟨j,i,hn,(Nat.le_succ i).trans he⟩; let d:= vitalK ν D' X p U a b j; change Fest _ _ _ _ (d i)
      have ht : d i=creekT (heights X ν D' u) a (vaneW X b i) (d (i+1)):= by unfold d vitalK; rw [ledgerR, if_pos he]; rfl
      have hk: Sense a (d i):= serves_v hA hp w
      have hl : W j ≤ i+1:= hn.trans (Nat.le_succ i)
      have hx: Sense a (d (i+1)):=serves_v hA hp (SoftP.mk j (i+1) hl he)
      let A'(i):= 💼 (Real.exp (r j i)) (fun s=> A s j); have hP(i): Crease (A' i):= boon_pos (fun i=> A i j) (fun i=>hz i j) _ (Real.exp_pos _|>.le)
      have hT : Fest (2*Z (X.J i)) E (B u) (A' (i+1)) (d i):= by rw [ht]; exact H u (d (i+1)) _ _ hx h (hP _) (ih hl)
      have hL : B u≤ Real.exp (C j):=(H' v).trans ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
      intro e hp r' t; by_cases h':t=∅
      · subst t; simp_rw [hk.void,one_mul]; exact owns_none _ _ (hP i|>.pos _) _ _ _
      apply owns_mono (hT e hp r' t) (le_mul_of_one_le_left (hw.irrigate _|>.le) (by norm_num)); rw [one_mul]; change _≤A' i _
      have hE:1 ≤ Real.exp (C j):= Real.one_le_exp (h0 _)
      calc _ ≤ Real.exp (C j)^t.card *A' (i+1) t := mul_le_mul_of_nonneg_right (hL.trans ((le_of_eq (pow_one _).symm).trans (pow_le_pow_right₀ hE (card_pos.mpr (nonempty_iff_ne_empty.mpr h'))))) (hP _|>.pos _)
           _ = _:= by unfold A' boon; rw [← mul_assoc,← mul_pow,← Real.exp_add]; have hx:k j i=k j (i+1)+1:= by unfold k; omega
                      rw [show (C j+r j (i+1))=r j i from (by unfold r; rw [hx]; push_cast; ring)]
end shipment
end YM.RG08.Creek
