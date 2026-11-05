import YM.RG08.Crossing.Coin
/-! # Uniform table of flat, post-block and growth costs for this action horizon

 Factor gains evaluated at the coarser vertex; a skipped step charged to the
 explicit length price. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary
open scoped BigOperators Topology Real Classical
variable {X : Chain} {G : Gauge} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} (S : Prism G X.kernel g P E) (ν : G.ColorIndex) (D : ChartRatio G)
variable {I : Type} (u : I→Windows)

structure Circuit : Prop where
  decks i : OnBoard S (u i).start
  M : NutWallet (fun i:Launch u=> X.patch i.i) ν D X.kernel E (Launch.farY X) (fun i=> ticketW P (X.J i.i))
  hessian : Weighed (Launch.farY (u:=u) X) (fun i=> K.bill (X.J i.i))
  chart : Weighed (Launch.farY (u:=u) X) (fun i=> P.bill (X.J i.i) (X.patch i.i))
  turn : Weighed (Launch.farY (u:=u) X) (fun i=> let j:= X.J i.i; Staffer.fundsTor G (K.b j) (K.bill j) _ X.kernel (X.trees i.i))
  cup : Weighed (Launch.farY (u:=u) X) (fun i=> Conductor.probeFee G (S.η (X.J i.i)))

abbrev Tier (S : Prism G X.kernel g P E) (i : ℕ) := S.η (X.J i)
variable {u ν D}
namespace Wings
variable {S : Prism G X.kernel g P E} {r : ℕ}

lemma q_whit {A : Wings u 0→ℕ} (h : Circuit S ν D u) :
    Voucher (menu X (u:=u)) 1 (fun i: Wings u 0=> Chain.column G X (A i) i.i) (fun i=> Tier S i.i) := by
  have ht:= h.hessian.transfer (toLaunch (u:=u) (k:=0))
  have he i : (qCap G (K.bill (X.J ((i:Wings u 0).i))))= (qCap G 1)*(K.bill (X.J i.i)) := by unfold qCap; ring
  refine ⟨_, (Weighed.constant (menu X) (qCap_pos G zero_le_one)).times ht, fun i=>?_⟩
  apply glow_less (Q_loans S (A i) i.i) le_rfl (le_of_eq ?_); rw [he i,Pi.mul_apply, Pi.one_apply,mul_one]
lemma mail (h : Circuit S ν D u) :
    SafeRow (menu X) (chop X (1/4)) ((fun i:Wings u 0=> X.K₀ i.N i.i)-(fun i:Wings u 0=>X.K₀ i.M i.i)) (fun i=> g.w (X.J i.i)) := by
  obtain ⟨A,p,hA,H⟩:=h.hessian; obtain ⟨C,hC,H'⟩:=k_cauchy A hA p
  refine ⟨_,(Weighed.constant (menu X) hC).times (Weighed.power (menu X) (sh X) p),fun i=>?_⟩
  simp only [Pi.sub_apply, Pi.pow_apply, Pi.mul_apply]; exact H' X K g (u i.b).Z (u i.b).pos (u i.b).start (u i.b).k (OnBoard.books S (h.decks i.b)) (fun k hk=> (H ⟨i.b,k,hk⟩).2) _ _ _ i.geC i.cut i.side
lemma q_right (h : Circuit S ν D u) :
    Both (menu X) (chop X (1/4)) (fun i : Wings u 0=> Chain.column G X i.N i.i) (fun i:Wings u 0=> Chain.column G X i.M i.i) (fun i=> Tier S i.i) := by
  refine ⟨q_whit h (A:=fun i=> i.N),q_whit h (A:=fun i=> i.M),?_⟩
  obtain ⟨V,hV,H⟩:=(mail h).soften (show (fun i=> Tier S i.i) ≤ _ from fun i=> S.sufficient _)
  refine ⟨_,(Weighed.constant (menu X) (qCap_pos G zero_le_one)).times hV,fun i=>?_⟩
  apply glow_less (Q_change (X:=X) (i:=i.i) (S.positive _) (hp:=show (X.K₀ i.N i.i-X.K₀ i.M i.i).strip (Tier S i.i) (V i*chop X (1/4) i) from H i)) le_rfl (le_of_eq ?_)
  rw [Pi.mul_apply]; unfold qCap; ring

lemma gear (h : Circuit S ν D u) (hv : X.Wake G) (A : Wings u 1→ℕ) :
    SafeRow (menu X) 1 (fun i=> Chain.curve G X (A i) i.i) (fun i=> P.w (X.J i.i)) ∧
      SafeRow (menu X) 1 (fun i=> Chain.predict G X (A i) i.i) (fun i=> P.w (X.J i.i)) := by
  have hp i := report_funding X hv P i.i (A i)
  have hh:= h.chart.transfer (toLaunch (u:=u) (k:=1))
  exact ⟨⟨_,hh,fun i=> by simpa only [Pi.one_apply,mul_one] using (hp i).1⟩,⟨_,hh,fun i=> by simpa only [Pi.one_apply,mul_one] using (hp i).2⟩⟩

private lemma mail_r (h : Circuit S ν D u) :
    SafeRow (menu X) (chop X (1/4)) ((fun i:Wings u 1=> X.K₀ i.N (i.i+1))-(fun i:Wings u 1=>X.K₀ i.M (i.i+1))) (fun i=> g.w (X.J (i.i+1))) := by
  obtain ⟨A,hA,H⟩:=mail h
  let L i:= ((X.S.block (i:Wings u 1).i).val:ℝ)
  have hp : Weighed (menu X) L := h.M.crop.transfer toLaunch
  have hs:= hA.transfer up
  refine ⟨_,((aged_up X h.M.crop).sway (sh X) hs).times hp,fun i=>?_⟩
  apply Work.F08.strip_mono (H i.up) le_rfl
  rw [Pi.mul_apply,mul_assoc]; apply mul_le_mul_of_nonneg_left ?_ (hA.positive _)
  exact continued' X _ (by norm_num) _ -- expose
lemma gear_both (h : Circuit S ν D u) (hv : X.Wake G) :
    RowBoth (menu X) (chop X (1/4)) (fun i: Wings u 1=> Chain.curve G X i.N i.i) (fun i: Wings u 1=> Chain.curve G X i.M i.i) (fun i=> ticketW P (X.J i.i)) ∧
    RowBoth (menu X) (chop X (1/4)) (fun i: Wings u 1=> Chain.predict G X i.N i.i) (fun i: Wings u 1=> Chain.predict G X i.M i.i) (fun i=>ticketW P (X.J i.i)) := by
  obtain ⟨C,hC,H⟩:=mail_r h
  let ψ i:= P.w (X.J (i:Wings u 1).i); let δ:=chop (u:=u) (r:=1) X (1/4)
  have hs : (fun i:Wings u 1=> ticketW P (X.J i.i)) ≤ ψ := fun i=> min_le_left ..
  obtain ⟨hx,hy⟩:=gear h hv N; obtain ⟨hs₁,hs₂⟩:= gear h hv M
  have hm (i:Wings u 1): X.J i.i=(X.patch i.i).J ∨ X.J i.i+1=(X.patch i.i).J := by
    change _=X.J (i.i+1) ∨ _=X.J (i.i+1); have hp:=X.mono i.i; have hz:= X.slow i.i; omega
  have he i:= (P.serves _ _ (hm i) (hv i.i) (X.history i.N (i.i+1)) (X.history i.M (i.i+1))).2.2 (g.w (X.J (i.i+1))) (C i*δ i) (mul_nonneg (hC.positive i) (gain_pos ..).le) (OnBoard.shift S (h.decks i.b) i.geC|>.1) (H i)
  have hw:= (h.chart.transfer (toLaunch (u:=u) (k:=1))).times hC
  exact ⟨⟨hx.soften hs,hs₁.soften hs,_,hw,fun i=> Work.F08.strip_mono ((he i).1) (hs i) (le_of_eq (mul_assoc ..).symm)⟩,⟨hy.soften hs,hs₂.soften hs,_,hw,fun i=> Work.F08.strip_mono ((he i).2) (hs i) (le_of_eq (mul_assoc ..).symm)⟩⟩
lemma tiers (S : Prism G X.kernel g P E) (i : ℕ) : Tier S i ≤ 1 :=
    ((le_trans (show Tier S i ≤ (E+3:ℕ) • Tier S i by simpa only [one_smul] using smul_le_smul_of_nonneg_right (show 1 ≤ E+3 by omega) (S.positive (X.J i)).le) (S.shade _))).trans (min_le_right ..)
lemma hire (h : Circuit S ν D u) (i : Wings u 1) : (E+3:ℕ) • ticketW P (X.J i.i) ≤ (X.S.block i.i).val * Tier S (i.i+1) :=
   (OnBoard.shift S (h.decks i.b) i.geC).2.1.trans (mul_le_mul_of_nonneg_left (div_le_self (S.positive (X.J (i.i+1))).le (by exact_mod_cast (show 1≤E+3 by omega))) (Nat.cast_nonneg _))
lemma ticketV (S : Prism G X.kernel g P E) (ht : r ≤ E+2) (i : ℕ) : (r+1:ℕ) • Tier S i ≤ ticketW P (X.J i) :=
   (smul_le_smul_of_nonneg_right (show r+1 ≤ E+3 by omega) (S.positive _).le).trans (S.shade _)

lemma launchCrop (S : Prism G X.kernel g P E) (ν : G.ColorIndex)(i r : ℕ)(k : ℕ) : Voucher (menu (u:=u) (r:=k) X) 1 (fun _=> wilsonTop ν i r) (fun j=> Tier S j.i) := by
  unfold wilsonTop; by_cases h : r=i+2 ∧ 0 < i
  swap
  · simp only [if_neg h]; exact Voucher.zero
  simp only [if_pos h]; obtain ⟨C,hC,H⟩:= sugar_paid (r:=r) ν zero_le_one
  exact ⟨_,Weighed.constant (menu X) hC,fun i=> glow_less H (tiers S _) (by simp only [Pi.one_apply, mul_one,le_refl])⟩
end Wings
end YM.RG08
