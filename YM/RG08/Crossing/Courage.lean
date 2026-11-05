import YM.RG08.Crossing.Cut
/-! # Tilt all carry rows, strict tickets; only need songs at compared lamps
- no comparison hypothesis on repeated *auxiliary* rays or paths.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Wings
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real Classical
variable {X : Chain} {G : Gauge} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} {S : Prism G X.kernel g P E} {ν : G.ColorIndex} {D : ChartRatio G}
variable {I : Type} {u : I→Windows} {r s : ℕ} {δ : Wings u 1→ℝ}

private def tote (t : Wings u 1) := K.b (X.J t.i) -- params from inference
private lemma waxFund (h : Circuit S ν D u) (ht : r ≤ E+2) {A : Wings u 1→Pot G s} {R : ∀ t:Wings u 1,Cross (X.S.block t.i) (Candles G) (Loc G 1)}(hp : SafeRow (menu X) 1 R (fun t=> tote (K:=K) t)) (hx : Voucher (menu X) δ A (fun t=> Tier S (t.i+1))) :
    Voucher (menu X) δ (fun t=> flow (cropWax (A t) r) (R t)) (fun t=>Tier S t.i) := by
  let Y : Wings u 1→ℝ := menu X; let v (t : Wings u 1) := Tier S (t.i+1)/((E+3:ℕ):ℝ)
  let w (t : Wings u 1) := Tier S t.i; have hv t : 0 ≤ v t := div_nonneg (S.positive _).le (by positivity)
  have he : 1 ≤ ((E+3:ℕ):ℝ):= by exact_mod_cast (show 1≤E+3 by omega)
  have hm t : (v t) ≤ 1:= (div_le_self (S.positive _).le he).trans (tiers S _)
  have hs : Weighed Y (fun t=> Real.exp (r*v t)) := (Weighed.constant Y (Real.exp_pos (r:ℝ)).le).mono (fun t=> (Real.exp_pos _).le) (fun t=> Real.exp_monotone (show _ ≤ (r:ℝ) from mul_le_of_le_one_right (by positivity) (hm t)))
  have hE : Voucher Y δ (fun t=> cropWax (A t) r) v := by
    obtain ⟨C,hC,H⟩:=hx; refine ⟨_,((hs.times (Weighed.constant _ (silkSale_pos G s r))).times hC),fun t=>?_⟩
    rw [Pi.mul_apply,mul_assoc]; refine silkFees (H t) (hv t) (le_trans ?_ (show ((E+3:ℕ):ℝ)*v t ≤ Tier S (t.i+1) from (mul_div_cancel₀ _ (zero_lt_one.trans_le he).ne').le))
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht.trans (Nat.le_succ _)) (hv t)
  obtain ⟨C,hC,H⟩:=hp; obtain ⟨B,hB,hV⟩:=hE
  have hy := h.M.crop.transfer (toLaunch (u:=u) (k:=1)); let k := Fintype.card (Loc G 1)
  let b t:= ((r+1:ℕ):ℝ)*w t
  have hh (t) : 0≤ w t:= (S.positive _).le
  have hY (t) : b t≤ticketW P (X.J t.i) := by simpa only [w,b,nsmul_eq_mul] using ticketV S ht t.i
  have hu : Weighed Y (fun t=> Real.exp (4*b t)) := (Weighed.constant _ (Real.exp_pos (4:ℝ)|>.le)).mono (fun _=> (Real.exp_pos _).le) (fun t=> Real.exp_monotone (mul_le_of_le_one_right (by norm_num: (0:ℝ)≤4) ((hY t).trans (min_le_right ..))))
  refine ⟨_,(((Weighed.constant Y (Nat.cast_nonneg k (α:=ℝ))).times hC).powers r).times ((hy.powers 4).times ((hu.powers r).times hB)),fun t=>?_⟩
  have hX : b t ≤ (X.S.block t.i).val*v t := (hY t).trans (le_trans (show ticketW _ _ ≤ (E+3:ℕ) • ticketW P (X.J t.i) by rw [nsmul_eq_mul]; exact le_mul_of_one_le_left (ticket_pos ..).le he) (OnBoard.shift S (h.decks t.b) t.geC).2.1)
  have hR : (R t).strip (b t) (C t) := by
    apply strip_mono (H t)
    · unfold b w tote; rw [← nsmul_eq_mul]; exact (smul_le_smul_of_nonneg_right (show r+1≤E+3 by omega) (S.positive _).le).trans (S.shine _)
    simp only [Pi.one_apply,mul_one,le_refl]
  simp only [Pi.mul_apply,mul_assoc]; exact (flow_basic (L:=X.S.block _) (hh t) (hv t) hX (hC.positive t) hR (hV t)).1

abbrev tilted (X : Chain) (t : Wings u 1) (ν : G.ColorIndex) (U : Pot G (r+2)) := penny ν (Chain.column G X t.N t.i) r (feather U (Chain.predict G X t.N t.i))

lemma jewel (L : Side){F : Pot G r}(h : Glows F) : Glows (gemL L F) := by
  obtain ⟨v,C,hv,H⟩:=h
  have he : 0<v/(r+1:ℕ):=div_pos hv (by positivity)
  refine ⟨_,_,he,gem_price _ H he.le ((le_of_eq (mul_div_cancel₀ v (by positivity))).trans (le_mul_of_one_le_left hv.le ?_))⟩
  exact_mod_cast L.property
lemma warmer {L : Side}{F : Pot G r}{R : Cross L (Loc G 1) (Loc G 1)}(h : Glows F)(hp : Whole R) : Glows (feather F R) := scroll_adm (jewel L h) (scan_whole hp)

lemma coasting (h : Circuit S ν D u) (hp : X.Wake G)(hs : G.Simple)(he : r ≤ E)
    (F : Wings u 1→Panel G) (hF : ∀ t,Songs G (F t))(hT : ∀ t, probeK ν (F t 2)=0)
    (hv : ∀ j < r+2,Voucher (menu X) δ (fun t=> F t j) (fun t=>Tier S (t.i+1))) :
    ∃ R : Wings u 1→ Pot G (r+2), Voucher (menu X) δ ((fun t=> tilted X t ν (F t (r+2))) - R) (fun t=>Tier S t.i) ∧
       ∀ t A, Glow (F t (r+2)) (Tier S (t.i+1)) A → Glow (R t) (Tier S t.i) (A*gain X.S (1/2) t.i (t.i+1)) := by
  let Q t:= Chain.column G X (t:Wings u 1).N t.i
  let W t:= painted G (X.A₀ t.N (t:Wings u 1).i)
  let V t:= Chain.predict G X (t:Wings u 1).N t.i
  choose L hL hS using fun t : Wings u 1=> earn G X t.N t.i hp t.cut K
  have hW (t) : Whole (W t) := ⟨_,_,K.positive _,paint_budget (az_strip X K (N t) _ [] (Nat.zero_le _))⟩
  have hl t: Whole (L t) := ⟨_,_,K.positive _,hL t⟩
  have hV t : Whole (V t):= (gear h hp N).2.status (fun _=> P.wpos _) t
  let T t:= feather (F t (r+2)) (W t); let A t:= feather (F t (r+2)) (V t); let B j t:= flow (cropWax (F t j) (r+2)) (L t); let C (t:Wings u 1):= ∑ j ∈ range (r+2), B j t
  have hL' : SafeRow (menu X) 1 L (fun i=> tote (K:=K) i) := ⟨_,h.turn.transfer toLaunch,fun t=> by simpa only [Pi.one_apply,mul_one,tote] using hL t⟩
  have hQ := (q_right h).fresh.mold low; have hw : Voucher (menu X) δ C (fun t=> Tier S t.i) := Voucher.list (range (r+2)) (sh X) (fun j hj=>waxFund h (by omega) hL' (hv j (mem_range.mp hj)))
  refine ⟨fun t=> penny ν (Q t) r (T t),?_,fun t _ ht=> penny_gain ν S (pre_gain S (h.decks t.b) t.geC he ht ((hF _).tunes _).2.1 ((hF _).sigh hs (hT _) r))⟩ -- `.ordered`
  let Z t:= penny ν (Q t) r (C t)
  have hZ : Voucher (menu X) δ Z (fun t=> Tier S t.i):= penny_paid ν (sh X) (fun _=>S.positive _) (h.cup.transfer toLaunch) hQ hw
  rw [show _-_ = -Z from funext fun i=> ?_]; · simpa only [neg_one_smul] using hZ.weight (-1)
  change penny ν (Q i) r (A i) - penny ν (Q i) r (T i) = - penny ν (Q i) r (C i)
  have hA : A i=T i-C i:= poetic G _ _ (fun m=>(hF i).words _ _) (fun j=> ((hF i).tunes j).1) (hW _) (hl _) (hV _) (hS _)
  have hc: Glows (C i):=⟨_,_,S.positive _,hw.choose_spec.2 i⟩
  have ht : Glows (T i) := warmer ((hF i).glows _) (hW _) -- names
  rw [hA,penny_sub _ _ _ ht hc]; abel
end YM.RG08.Wings
